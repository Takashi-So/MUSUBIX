/**
 * YATA Local - Reasoning Engine
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/reasoning
 *
 * @see REQ-YL-REASON-001 ~ REQ-YL-REASON-004
 */

import type {
  RelationType,
  InferenceRule,
  Constraint,
  ValidationResult,
  ConstraintViolation,
} from './types.js';
import type { YataDatabase } from './database.js';
import type { QueryEngine } from './query-engine.js';

/**
 * Inference result from reasoning engine
 */
export interface InferenceResult {
  /** Inferred relationships */
  inferred: Array<{
    sourceId: string;
    targetId: string;
    type: RelationType;
    confidence: number;
    rule: string;
  }>;
  /** Applied rules */
  appliedRules: string[];
}

/**
 * Reasoning engine for inference and constraint validation
 */
export class ReasoningEngine {
  private rules: Map<string, InferenceRule> = new Map();
  private constraints: Map<string, Constraint> = new Map();

  constructor(
    private db: YataDatabase,
    private queryEngine: QueryEngine
  ) {
    this.initializeBuiltInRules();
    this.initializeBuiltInConstraints();
  }

  /**
   * Initialize built-in inference rules
   * @see REQ-YL-REASON-001
   */
  private initializeBuiltInRules(): void {
    // Type inheritance rule: if A extends B and B extends C, then A extends C
    this.rules.set('transitive-extends', {
      id: 'transitive-extends',
      name: 'Transitive Inheritance',
      description: 'If A extends B and B extends C, infer A extends C',
      pattern: {
        nodes: [
          { variable: 'a', type: 'class' },
          { variable: 'b', type: 'class' },
          { variable: 'c', type: 'class' },
        ],
        edges: [
          { sourceVar: 'a', targetVar: 'b', type: 'extends' },
          { sourceVar: 'b', targetVar: 'c', type: 'extends' },
        ],
      },
      inference: {
        sourceVar: 'a',
        targetVar: 'c',
        type: 'extends',
      },
      confidence: 1.0,
    });

    // Implementation implies type compatibility
    this.rules.set('implements-type', {
      id: 'implements-type',
      name: 'Interface Implementation',
      description: 'If class implements interface, class is type-compatible with interface',
      pattern: {
        nodes: [
          { variable: 'class', type: 'class' },
          { variable: 'interface', type: 'interface' },
        ],
        edges: [{ sourceVar: 'class', targetVar: 'interface', type: 'implements' }],
      },
      inference: {
        sourceVar: 'class',
        targetVar: 'interface',
        type: 'type-compatible',
      },
      confidence: 1.0,
    });

    // Dependency chain: if A depends on B and B depends on C, A transitively depends on C
    this.rules.set('transitive-dependency', {
      id: 'transitive-dependency',
      name: 'Transitive Dependency',
      description: 'If A depends on B and B depends on C, infer A transitively depends on C',
      pattern: {
        nodes: [
          { variable: 'a' },
          { variable: 'b' },
          { variable: 'c' },
        ],
        edges: [
          { sourceVar: 'a', targetVar: 'b', type: 'depends-on' },
          { sourceVar: 'b', targetVar: 'c', type: 'depends-on' },
        ],
      },
      inference: {
        sourceVar: 'a',
        targetVar: 'c',
        type: 'transitively-depends-on',
      },
      confidence: 0.9,
    });

    // Method override: if class extends base and has method with same name
    this.rules.set('method-override', {
      id: 'method-override',
      name: 'Method Override',
      description: 'If class extends base and both have same-named method, method overrides',
      pattern: {
        nodes: [
          { variable: 'child', type: 'class' },
          { variable: 'parent', type: 'class' },
          { variable: 'childMethod', type: 'method' },
          { variable: 'parentMethod', type: 'method' },
        ],
        edges: [
          { sourceVar: 'child', targetVar: 'parent', type: 'extends' },
          { sourceVar: 'child', targetVar: 'childMethod', type: 'has-method' },
          { sourceVar: 'parent', targetVar: 'parentMethod', type: 'has-method' },
        ],
      },
      inference: {
        sourceVar: 'childMethod',
        targetVar: 'parentMethod',
        type: 'overrides',
      },
      confidence: 0.8,
    });
  }

  /**
   * Initialize built-in constraints
   * @see REQ-YL-REASON-003
   */
  private initializeBuiltInConstraints(): void {
    // No circular inheritance
    this.constraints.set('no-circular-inheritance', {
      id: 'no-circular-inheritance',
      name: 'No Circular Inheritance',
      description: 'Classes must not have circular inheritance chains',
      type: 'graph',
      check: async (db: YataDatabase) => {
        const violations: ConstraintViolation[] = [];
        const { entities } = db.queryEntities({ type: 'class' }, 10000);

        for (const entity of entities) {
          const visited = new Set<string>();
          let current = entity.id;

          while (current) {
            if (visited.has(current)) {
              violations.push({
                entityId: entity.id,
                constraintId: 'no-circular-inheritance',
                message: `Circular inheritance detected: ${entity.name}`,
                severity: 'error',
              });
              break;
            }
            visited.add(current);

            const rels = db.getRelationships(current, 'out');
            const extendsRel = rels.find(r => r.type === 'extends');
            current = extendsRel?.targetId ?? '';
          }
        }

        return violations;
      },
    });

    // All imports must resolve
    this.constraints.set('imports-resolve', {
      id: 'imports-resolve',
      name: 'Imports Must Resolve',
      description: 'All import relationships must have valid targets',
      type: 'referential',
      check: async (db: YataDatabase) => {
        const violations: ConstraintViolation[] = [];
        const { entities } = db.queryEntities({}, 10000);

        for (const entity of entities) {
          const rels = db.getRelationships(entity.id, 'out');
          for (const rel of rels) {
            if (rel.type === 'imports') {
              const target = db.getEntity(rel.targetId);
              if (!target) {
                violations.push({
                  entityId: entity.id,
                  relationshipId: rel.id,
                  constraintId: 'imports-resolve',
                  message: `Unresolved import: ${rel.targetId}`,
                  severity: 'error',
                });
              }
            }
          }
        }

        return violations;
      },
    });

    // Entity must have name
    this.constraints.set('entity-has-name', {
      id: 'entity-has-name',
      name: 'Entity Must Have Name',
      description: 'All entities must have a non-empty name',
      type: 'cardinality',
      check: async (db: YataDatabase) => {
        const violations: ConstraintViolation[] = [];
        const { entities } = db.queryEntities({}, 10000);

        for (const entity of entities) {
          if (!entity.name || entity.name.trim() === '') {
            violations.push({
              entityId: entity.id,
              constraintId: 'entity-has-name',
              message: `Entity has no name: ${entity.id}`,
              severity: 'error',
            });
          }
        }

        return violations;
      },
    });

    // Function should have return type
    this.constraints.set('function-return-type', {
      id: 'function-return-type',
      name: 'Function Return Type',
      description: 'Functions should have a declared return type',
      type: 'property',
      check: async (db: YataDatabase) => {
        const violations: ConstraintViolation[] = [];
        const { entities } = db.queryEntities({ type: 'function' }, 10000);

        for (const entity of entities) {
          if (!entity.metadata.returnType) {
            violations.push({
              entityId: entity.id,
              constraintId: 'function-return-type',
              message: `Function ${entity.name} has no return type`,
              severity: 'warning',
            });
          }
        }

        return violations;
      },
    });
  }

  /**
   * Add custom inference rule
   */
  addRule(rule: InferenceRule): void {
    this.rules.set(rule.id, rule);
  }

  /**
   * Remove inference rule
   */
  removeRule(ruleId: string): boolean {
    return this.rules.delete(ruleId);
  }

  /**
   * Get all rules
   */
  getRules(): InferenceRule[] {
    return Array.from(this.rules.values());
  }

  /**
   * Add custom constraint
   */
  addConstraint(constraint: Constraint): void {
    this.constraints.set(constraint.id, constraint);
  }

  /**
   * Remove constraint
   */
  removeConstraint(constraintId: string): boolean {
    return this.constraints.delete(constraintId);
  }

  /**
   * Get all constraints
   */
  getConstraints(): Constraint[] {
    return Array.from(this.constraints.values());
  }

  /**
   * Run inference on the graph
   * @see REQ-YL-REASON-001
   */
  infer(options: { rules?: string[]; maxIterations?: number } = {}): InferenceResult {
    const maxIterations = options.maxIterations ?? 10;
    const rulesToApply = options.rules
      ? Array.from(this.rules.values()).filter(r => options.rules!.includes(r.id))
      : Array.from(this.rules.values());

    const result: InferenceResult = {
      inferred: [],
      appliedRules: [],
    };

    // Fixed-point iteration
    let changed = true;
    let iteration = 0;

    while (changed && iteration < maxIterations) {
      changed = false;
      iteration++;

      for (const rule of rulesToApply) {
        const matches = this.queryEngine.matchPattern(rule.pattern);

        for (const match of matches) {
          const sourceId = match.bindings[rule.inference.sourceVar];
          const targetId = match.bindings[rule.inference.targetVar];

          if (!sourceId || !targetId) continue;

          // Check if relationship already exists
          const existingRels = this.db.getRelationships(sourceId, 'out');
          const exists = existingRels.some(
            r => r.targetId === targetId && r.type === rule.inference.type
          );

          if (!exists) {
            result.inferred.push({
              sourceId,
              targetId,
              type: rule.inference.type,
              confidence: rule.confidence * match.confidence,
              rule: rule.id,
            });
            changed = true;

            if (!result.appliedRules.includes(rule.id)) {
              result.appliedRules.push(rule.id);
            }
          }
        }
      }
    }

    return result;
  }

  /**
   * Validate graph against constraints
   * @see REQ-YL-REASON-003
   */
  async validate(options: { constraints?: string[] } = {}): Promise<ValidationResult> {
    const constraintsToCheck = options.constraints
      ? Array.from(this.constraints.values()).filter(c => options.constraints!.includes(c.id))
      : Array.from(this.constraints.values());

    const allViolations: ValidationResult['violations'] = [];

    for (const constraint of constraintsToCheck) {
      const violations = await constraint.check(this.db);
      allViolations.push(...violations);
    }

    const errorCount = allViolations.filter(v => v.severity === 'error').length;
    const warningCount = allViolations.filter(v => v.severity === 'warning').length;

    return {
      valid: errorCount === 0,
      violations: allViolations,
      summary: {
        total: allViolations.length,
        errors: errorCount,
        warnings: warningCount,
        info: allViolations.filter(v => v.severity === 'info').length,
      },
    };
  }

  /**
   * Compute confidence score for entity relationship
   * @see REQ-YL-REASON-004
   */
  computeConfidence(sourceId: string, targetId: string, relType: RelationType): number {
    // Direct relationship
    const directRels = this.db.getRelationships(sourceId, 'out');
    const directRel = directRels.find(r => r.targetId === targetId && r.type === relType);
    if (directRel) return directRel.weight;

    // Inferred relationship
    const inferred = this.infer();
    const inferredRel = inferred.inferred.find(
      i => i.sourceId === sourceId && i.targetId === targetId && i.type === relType
    );
    if (inferredRel) return inferredRel.confidence;

    // Path-based confidence (decays with distance)
    const path = this.queryEngine.findPath(sourceId, targetId);
    if (path) {
      return Math.pow(0.9, path.length);
    }

    return 0;
  }

  /**
   * Find potential relationships based on structural similarity
   * @see REQ-YL-REASON-002
   */
  suggestRelationships(
    entityId: string,
    options: {
      maxSuggestions?: number;
      minConfidence?: number;
    } = {}
  ): Array<{ targetId: string; type: RelationType; confidence: number; reason: string }> {
    const maxSuggestions = options.maxSuggestions ?? 10;
    const minConfidence = options.minConfidence ?? 0.5;

    const suggestions: Array<{
      targetId: string;
      type: RelationType;
      confidence: number;
      reason: string;
    }> = [];

    const entity = this.db.getEntity(entityId);
    if (!entity) return suggestions;

    // Find similar entities by name pattern
    const nameParts = entity.name.split(/(?=[A-Z])|_|-/);
    for (const part of nameParts) {
      if (part.length < 3) continue;

      const similar = this.db.searchEntities(part, 20);
      for (const sim of similar) {
        if (sim.id === entityId) continue;

        // Check if relationship already exists
        const existingRels = this.db.getRelationships(entityId);
        const hasRelationship = existingRels.some(
          r => r.sourceId === sim.id || r.targetId === sim.id
        );

        if (!hasRelationship) {
          const confidence = this.computeNameSimilarity(entity.name, sim.name);
          if (confidence >= minConfidence) {
            suggestions.push({
              targetId: sim.id,
              type: 'related-to',
              confidence,
              reason: `Similar name pattern: "${part}"`,
            });
          }
        }
      }
    }

    // Find related by same file
    if (entity.filePath) {
      const { entities: sameFile } = this.db.queryEntities({}, 1000);
      for (const other of sameFile.filter(e => e.filePath === entity.filePath && e.id !== entityId)) {
        const existingRels = this.db.getRelationships(entityId);
        const hasRelationship = existingRels.some(
          r => r.sourceId === other.id || r.targetId === other.id
        );

        if (!hasRelationship) {
          suggestions.push({
            targetId: other.id,
            type: 'defined-in-same-file',
            confidence: 0.7,
            reason: 'Same source file',
          });
        }
      }
    }

    // Sort by confidence and limit
    return suggestions
      .sort((a, b) => b.confidence - a.confidence)
      .slice(0, maxSuggestions);
  }

  /**
   * Compute name similarity using Levenshtein distance
   */
  private computeNameSimilarity(name1: string, name2: string): number {
    const n1 = name1.toLowerCase();
    const n2 = name2.toLowerCase();

    const maxLen = Math.max(n1.length, n2.length);
    if (maxLen === 0) return 1;

    const distance = this.levenshteinDistance(n1, n2);
    return 1 - distance / maxLen;
  }

  /**
   * Levenshtein distance calculation
   */
  private levenshteinDistance(s1: string, s2: string): number {
    const m = s1.length;
    const n = s2.length;
    const dp: number[][] = Array(m + 1)
      .fill(null)
      .map(() => Array(n + 1).fill(0));

    for (let i = 0; i <= m; i++) dp[i][0] = i;
    for (let j = 0; j <= n; j++) dp[0][j] = j;

    for (let i = 1; i <= m; i++) {
      for (let j = 1; j <= n; j++) {
        if (s1[i - 1] === s2[j - 1]) {
          dp[i][j] = dp[i - 1][j - 1];
        } else {
          dp[i][j] = 1 + Math.min(dp[i - 1][j], dp[i][j - 1], dp[i - 1][j - 1]);
        }
      }
    }

    return dp[m][n];
  }
}
