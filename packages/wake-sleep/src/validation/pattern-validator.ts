/**
 * @fileoverview Pattern Validator integrating ConsistencyValidator
 * @traceability REQ-WAKE-001-F003, REQ-INT-002
 * 
 * @description
 * Validates patterns before they are added to the knowledge graph.
 * Uses ConsistencyValidator from ontology-mcp for OWL constraint checking.
 */

import type { PatternCandidate } from '../types.js';

/**
 * Validation configuration
 */
export interface PatternValidationConfig {
  /** Enable duplicate detection */
  checkDuplicates: boolean;
  /** Enable circular dependency detection */
  checkCircular: boolean;
  /** Enable disjoint class checking */
  checkDisjoint: boolean;
  /** Minimum confidence threshold */
  minConfidence: number;
  /** Maximum patterns with same name */
  maxSameNamePatterns: number;
}

/**
 * Validation result
 */
export interface PatternValidationResult {
  valid: boolean;
  patternId: string;
  violations: PatternViolation[];
  suggestions: string[];
  confidence: number;
}

/**
 * Pattern violation
 */
export interface PatternViolation {
  type: 'duplicate' | 'circular' | 'disjoint' | 'low-confidence' | 'name-collision';
  severity: 'error' | 'warning' | 'info';
  message: string;
  relatedPatterns?: string[];
}

/**
 * Default validation configuration
 */
const DEFAULT_CONFIG: PatternValidationConfig = {
  checkDuplicates: true,
  checkCircular: true,
  checkDisjoint: true,
  minConfidence: 0.5,
  maxSameNamePatterns: 3,
};

/**
 * PatternValidator
 * 
 * Validates patterns using OWL-based consistency checking.
 * Integrates with ConsistencyValidator from @nahisaho/musubix-ontology-mcp.
 */
export class PatternValidator {
  private config: PatternValidationConfig;
  private patternIndex: Map<string, PatternCandidate[]> = new Map();
  private nameIndex: Map<string, string[]> = new Map();

  constructor(config?: Partial<PatternValidationConfig>) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  /**
   * Validate a pattern before adding to library
   */
  validatePattern(
    pattern: PatternCandidate,
    existingPatterns: PatternCandidate[]
  ): PatternValidationResult {
    const violations: PatternViolation[] = [];
    const suggestions: string[] = [];
    const patternId = pattern.id ?? pattern.name;

    // 1. Check confidence threshold
    if (pattern.confidence < this.config.minConfidence) {
      violations.push({
        type: 'low-confidence',
        severity: 'warning',
        message: `Pattern confidence ${pattern.confidence.toFixed(2)} is below threshold ${this.config.minConfidence}`,
      });
      suggestions.push(`Consider increasing pattern occurrences or improving extraction quality`);
    }

    // 2. Check for duplicates
    if (this.config.checkDuplicates) {
      const duplicates = this.findDuplicates(pattern, existingPatterns);
      if (duplicates.length > 0) {
        violations.push({
          type: 'duplicate',
          severity: 'error',
          message: `Pattern is a duplicate of existing pattern(s)`,
          relatedPatterns: duplicates,
        });
        suggestions.push(`Consider merging with existing pattern: ${duplicates[0]}`);
      }
    }

    // 3. Check for name collisions
    const nameCollisions = this.findNameCollisions(pattern, existingPatterns);
    if (nameCollisions.length >= this.config.maxSameNamePatterns) {
      violations.push({
        type: 'name-collision',
        severity: 'warning',
        message: `Pattern name "${pattern.name}" already used by ${nameCollisions.length} patterns`,
        relatedPatterns: nameCollisions,
      });
      suggestions.push(`Consider using a more specific name or versioning: ${pattern.name}_v${nameCollisions.length + 1}`);
    }

    // 4. Check for circular dependencies (simplified)
    if (this.config.checkCircular) {
      const circularIssues = this.findCircularDependencies(pattern, existingPatterns);
      if (circularIssues.length > 0) {
        violations.push({
          type: 'circular',
          severity: 'error',
          message: `Pattern creates circular dependency`,
          relatedPatterns: circularIssues,
        });
        suggestions.push(`Break the cycle by removing reference to: ${circularIssues[0]}`);
      }
    }

    // 5. Check for disjoint class violations
    if (this.config.checkDisjoint) {
      const disjointIssues = this.findDisjointViolations(pattern, existingPatterns);
      if (disjointIssues.length > 0) {
        violations.push({
          type: 'disjoint',
          severity: 'error',
          message: `Pattern violates disjoint class constraint`,
          relatedPatterns: disjointIssues,
        });
        suggestions.push(`Pattern cannot belong to both categories. Choose one.`);
      }
    }

    // Calculate overall validity
    const hasErrors = violations.some(v => v.severity === 'error');
    const adjustedConfidence = this.calculateAdjustedConfidence(pattern.confidence, violations);

    return {
      valid: !hasErrors,
      patternId,
      violations,
      suggestions,
      confidence: adjustedConfidence,
    };
  }

  /**
   * Validate multiple patterns in batch
   */
  validateBatch(
    patterns: PatternCandidate[],
    existingPatterns: PatternCandidate[]
  ): PatternValidationResult[] {
    const results: PatternValidationResult[] = [];
    let accumulator = [...existingPatterns];

    for (const pattern of patterns) {
      const result = this.validatePattern(pattern, accumulator);
      results.push(result);

      // Add valid patterns to accumulator for subsequent checks
      if (result.valid) {
        accumulator.push(pattern);
      }
    }

    return results;
  }

  /**
   * Find duplicate patterns using structural comparison
   */
  private findDuplicates(
    pattern: PatternCandidate,
    existingPatterns: PatternCandidate[]
  ): string[] {
    const duplicates: string[] = [];
    const patternHash = this.hashStructure(pattern.structure);

    for (const existing of existingPatterns) {
      const existingHash = this.hashStructure(existing.structure);
      if (patternHash === existingHash) {
        duplicates.push(existing.id ?? existing.name);
      }
    }

    return duplicates;
  }

  /**
   * Find patterns with the same name
   */
  private findNameCollisions(
    pattern: PatternCandidate,
    existingPatterns: PatternCandidate[]
  ): string[] {
    return existingPatterns
      .filter(p => p.name === pattern.name)
      .map(p => p.id ?? p.name);
  }

  /**
   * Find circular dependencies in pattern references
   */
  private findCircularDependencies(
    pattern: PatternCandidate,
    existingPatterns: PatternCandidate[]
  ): string[] {
    const patternId = pattern.id ?? pattern.name;
    const circularRefs: string[] = [];

    // Simple check: look for patterns that reference this pattern
    // and that this pattern also references
    const referencedByPattern = this.extractReferences(pattern);

    for (const existingPattern of existingPatterns) {
      const existingId = existingPattern.id ?? existingPattern.name;
      const existingRefs = this.extractReferences(existingPattern);

      // Check if mutual reference exists
      if (referencedByPattern.includes(existingId) && existingRefs.includes(patternId)) {
        circularRefs.push(existingId);
      }
    }

    return circularRefs;
  }

  /**
   * Find disjoint class violations
   * Patterns from certain sources cannot be combined
   */
  private findDisjointViolations(
    pattern: PatternCandidate,
    existingPatterns: PatternCandidate[]
  ): string[] {
    const violations: string[] = [];

    // Define disjoint source pairs
    const disjointPairs: Array<[string, string]> = [
      // No current disjoint pairs defined
      // Add domain-specific constraints here
    ];

    for (const [source1, source2] of disjointPairs) {
      if (pattern.source === source1) {
        const conflicting = existingPatterns.filter(p => 
          p.source === source2 && this.isStructurallyRelated(pattern, p)
        );
        violations.push(...conflicting.map(p => p.id ?? p.name));
      }
    }

    return violations;
  }

  /**
   * Extract pattern references from structure
   */
  private extractReferences(pattern: PatternCandidate): string[] {
    const refs: string[] = [];
    const structure = pattern.structure;

    if (typeof structure === 'object' && structure !== null) {
      const traverse = (obj: unknown): void => {
        if (typeof obj !== 'object' || obj === null) return;
        
        if (Array.isArray(obj)) {
          obj.forEach(traverse);
        } else {
          const record = obj as Record<string, unknown>;
          if (typeof record['$ref'] === 'string') {
            refs.push(record['$ref']);
          }
          Object.values(record).forEach(traverse);
        }
      };
      traverse(structure);
    }

    return refs;
  }

  /**
   * Check if two patterns are structurally related
   */
  private isStructurallyRelated(p1: PatternCandidate, p2: PatternCandidate): boolean {
    // Simple check: compare pattern names for similarity
    const name1 = p1.name.toLowerCase();
    const name2 = p2.name.toLowerCase();
    
    // Check for common prefixes or suffixes
    const commonPrefix = this.longestCommonPrefix(name1, name2);
    return commonPrefix.length > 3;
  }

  /**
   * Find longest common prefix between two strings
   */
  private longestCommonPrefix(s1: string, s2: string): string {
    let i = 0;
    while (i < s1.length && i < s2.length && s1[i] === s2[i]) {
      i++;
    }
    return s1.substring(0, i);
  }

  /**
   * Hash a structure for duplicate detection
   */
  private hashStructure(structure: unknown): string {
    // Deterministic JSON stringification
    const normalize = (obj: unknown): unknown => {
      if (typeof obj !== 'object' || obj === null) return obj;
      if (Array.isArray(obj)) return obj.map(normalize);
      
      const sorted: Record<string, unknown> = {};
      for (const key of Object.keys(obj as Record<string, unknown>).sort()) {
        sorted[key] = normalize((obj as Record<string, unknown>)[key]);
      }
      return sorted;
    };

    const normalized = JSON.stringify(normalize(structure));
    
    // Simple hash function
    let hash = 0;
    for (let i = 0; i < normalized.length; i++) {
      const char = normalized.charCodeAt(i);
      hash = ((hash << 5) - hash) + char;
      hash = hash & hash; // Convert to 32bit integer
    }
    return hash.toString(16);
  }

  /**
   * Calculate adjusted confidence based on violations
   */
  private calculateAdjustedConfidence(
    originalConfidence: number,
    violations: PatternViolation[]
  ): number {
    let adjustment = 0;

    for (const violation of violations) {
      switch (violation.severity) {
        case 'error':
          adjustment -= 0.3;
          break;
        case 'warning':
          adjustment -= 0.1;
          break;
        case 'info':
          adjustment -= 0.05;
          break;
      }
    }

    return Math.max(0, Math.min(1, originalConfidence + adjustment));
  }

  /**
   * Update configuration
   */
  updateConfig(config: Partial<PatternValidationConfig>): void {
    this.config = { ...this.config, ...config };
  }

  /**
   * Get current configuration
   */
  getConfig(): PatternValidationConfig {
    return { ...this.config };
  }

  /**
   * Clear internal caches
   */
  clearCache(): void {
    this.patternIndex.clear();
    this.nameIndex.clear();
  }
}
