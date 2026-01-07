/**
 * @fileoverview Result Aggregator - combines and deduplicates security findings
 * @module @nahisaho/musubix-security/core/result-aggregator
 * @trace DES-SEC2-ORCH-003, REQ-SEC2-REPORT-001
 */

import type {
  Vulnerability,
  Severity,
  SourceLocation,
} from '../types/vulnerability.js';
import type {
  DetectionSource,
  AggregatedVulnerability,
  AnalysisResult,
  AggregatedResult,
  DeduplicationRule,
  PrioritizationCriteria,
  IResultAggregator,
} from '../types/result.js';
import {
  DEFAULT_PRIORITIZATION,
  SEVERITY_SCORES,
} from '../types/result.js';

/**
 * Default deduplication rules
 */
const DEFAULT_DEDUP_RULES: DeduplicationRule[] = [
  {
    id: 'same-location-cwe',
    compareFields: ['location', 'cwes'],
    similarityThreshold: 0.9,
    mergeStrategy: 'keep-highest-confidence',
  },
  {
    id: 'same-rule-location',
    compareFields: ['ruleId', 'location'],
    similarityThreshold: 0.95,
    mergeStrategy: 'keep-first',
  },
];

/**
 * Result Aggregator implementation
 * @trace DES-SEC2-ORCH-003
 */
export class ResultAggregator implements IResultAggregator {
  private deduplicationRules: DeduplicationRule[];
  private prioritizationCriteria: PrioritizationCriteria;

  constructor(
    rules: DeduplicationRule[] = DEFAULT_DEDUP_RULES,
    criteria: PrioritizationCriteria = DEFAULT_PRIORITIZATION
  ) {
    this.deduplicationRules = rules;
    this.prioritizationCriteria = criteria;
  }

  /**
   * Aggregate results from multiple analyzers
   * @trace REQ-SEC2-REPORT-001
   */
  aggregate(results: AnalysisResult[]): AggregatedResult {
    const startTime = Date.now();
    
    // Collect all vulnerabilities with source tracking
    const allVulnerabilities: AggregatedVulnerability[] = [];
    const sources = new Set<DetectionSource>();
    
    for (const result of results) {
      sources.add(result.type);
      
      for (const vuln of result.vulnerabilities) {
        allVulnerabilities.push({
          ...vuln,
          sources: [result.type],
          originalIds: [vuln.id],
          isDuplicate: false,
          priorityScore: 0,
          riskScore: 0,
        });
      }
    }
    
    // Deduplicate
    const deduplicatedCount = allVulnerabilities.length;
    const deduplicated = this.deduplicateAggregated(allVulnerabilities);
    const duplicatesRemoved = deduplicatedCount - deduplicated.length;
    
    // Prioritize
    const prioritized = this.prioritizeAggregated(deduplicated);
    
    // Calculate summaries
    const bySeverity: Record<Severity, number> = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      info: 0,
    };
    
    const bySource: Record<DetectionSource, number> = {
      sast: 0,
      taint: 0,
      secret: 0,
      dependency: 0,
      container: 0,
      iac: 0,
      ai: 0,
      'neuro-symbolic': 0,
    };
    
    for (const vuln of prioritized) {
      bySeverity[vuln.severity]++;
      for (const source of vuln.sources) {
        bySource[source]++;
      }
    }
    
    // Calculate overall risk score
    const riskScore = this.calculateRiskScore(prioritized);
    
    return {
      vulnerabilities: prioritized,
      riskScore,
      bySeverity,
      bySource,
      duplicatesRemoved,
      sources: Array.from(sources),
      aggregatedAt: new Date(),
      aggregationDuration: Date.now() - startTime,
    };
  }

  /**
   * Deduplicate vulnerabilities
   */
  deduplicate(
    vulnerabilities: Vulnerability[],
    rules: DeduplicationRule[] = this.deduplicationRules
  ): Vulnerability[] {
    // Convert to aggregated format for processing
    const aggregated = vulnerabilities.map(v => ({
      ...v,
      sources: ['sast' as DetectionSource],
      originalIds: [v.id],
      isDuplicate: false,
      priorityScore: 0,
      riskScore: 0,
    }));
    
    const deduplicated = this.deduplicateAggregated(aggregated, rules);
    
    // Convert back to regular vulnerabilities
    return deduplicated.map(({ sources, originalIds, isDuplicate, priorityScore, riskScore, ...vuln }) => vuln);
  }

  /**
   * Deduplicate aggregated vulnerabilities
   */
  private deduplicateAggregated(
    vulnerabilities: AggregatedVulnerability[],
    rules: DeduplicationRule[] = this.deduplicationRules
  ): AggregatedVulnerability[] {
    if (vulnerabilities.length <= 1) return vulnerabilities;
    
    const result: AggregatedVulnerability[] = [];
    const merged = new Set<number>();
    
    for (let i = 0; i < vulnerabilities.length; i++) {
      if (merged.has(i)) continue;
      
      let current = vulnerabilities[i];
      
      for (let j = i + 1; j < vulnerabilities.length; j++) {
        if (merged.has(j)) continue;
        
        const other = vulnerabilities[j];
        
        for (const rule of rules) {
          const similarity = this.calculateSimilarity(current, other, rule.compareFields);
          
          if (similarity >= rule.similarityThreshold) {
            // Merge according to strategy
            current = this.mergeVulnerabilities(current, other, rule.mergeStrategy);
            merged.add(j);
            break;
          }
        }
      }
      
      result.push(current);
    }
    
    return result;
  }

  /**
   * Calculate similarity between two vulnerabilities
   */
  private calculateSimilarity(
    v1: Vulnerability,
    v2: Vulnerability,
    fields: (keyof Vulnerability)[]
  ): number {
    let matchingFields = 0;
    
    for (const field of fields) {
      if (this.fieldsMatch(v1[field], v2[field])) {
        matchingFields++;
      }
    }
    
    return matchingFields / fields.length;
  }

  /**
   * Check if two field values match
   */
  private fieldsMatch(v1: unknown, v2: unknown): boolean {
    if (v1 === v2) return true;
    
    // Handle arrays (like cwes)
    if (Array.isArray(v1) && Array.isArray(v2)) {
      return v1.length === v2.length && 
             v1.every((item, i) => item === v2[i]);
    }
    
    // Handle SourceLocation
    if (this.isSourceLocation(v1) && this.isSourceLocation(v2)) {
      return v1.file === v2.file &&
             v1.startLine === v2.startLine &&
             v1.endLine === v2.endLine;
    }
    
    return false;
  }

  /**
   * Type guard for SourceLocation
   */
  private isSourceLocation(v: unknown): v is SourceLocation {
    return typeof v === 'object' && v !== null &&
           'file' in v && 'startLine' in v && 'endLine' in v;
  }

  /**
   * Merge two vulnerabilities according to strategy
   */
  mergeVulnerabilities(
    v1: AggregatedVulnerability,
    v2: AggregatedVulnerability,
    strategy: 'keep-first' | 'keep-highest-confidence' | 'merge' = 'keep-highest-confidence'
  ): AggregatedVulnerability {
    // Always combine sources and original IDs
    const mergedSources = Array.from(new Set([...v1.sources, ...v2.sources]));
    const mergedIds = Array.from(new Set([...v1.originalIds, ...v2.originalIds]));
    
    switch (strategy) {
      case 'keep-first':
        return {
          ...v1,
          sources: mergedSources,
          originalIds: mergedIds,
          isDuplicate: true,
        };
        
      case 'keep-highest-confidence':
        const base = v1.confidence >= v2.confidence ? v1 : v2;
        return {
          ...base,
          sources: mergedSources,
          originalIds: mergedIds,
          isDuplicate: true,
        };
        
      case 'merge':
        // Merge additional info
        const mergedCwes = Array.from(new Set([...v1.cwes, ...v2.cwes]));
        return {
          ...v1,
          cwes: mergedCwes,
          confidence: Math.max(v1.confidence, v2.confidence),
          sources: mergedSources,
          originalIds: mergedIds,
          isDuplicate: true,
          // Combine recommendations if different
          recommendation: v1.recommendation === v2.recommendation
            ? v1.recommendation
            : `${v1.recommendation}\n\nAlternative: ${v2.recommendation}`,
        };
        
      default:
        return {
          ...v1,
          sources: mergedSources,
          originalIds: mergedIds,
          isDuplicate: true,
        };
    }
  }

  /**
   * Prioritize vulnerabilities
   */
  prioritize(
    vulnerabilities: Vulnerability[],
    criteria: PrioritizationCriteria = this.prioritizationCriteria
  ): Vulnerability[] {
    const withScores = vulnerabilities.map(v => ({
      vuln: v,
      score: this.calculatePriorityScore(v, criteria),
    }));
    
    withScores.sort((a, b) => b.score - a.score);
    
    return withScores.map(({ vuln }) => vuln);
  }

  /**
   * Prioritize aggregated vulnerabilities
   */
  private prioritizeAggregated(
    vulnerabilities: AggregatedVulnerability[],
    criteria: PrioritizationCriteria = this.prioritizationCriteria
  ): AggregatedVulnerability[] {
    for (const vuln of vulnerabilities) {
      vuln.priorityScore = this.calculatePriorityScore(vuln, criteria);
      vuln.riskScore = this.calculateIndividualRiskScore(vuln);
    }
    
    return vulnerabilities.sort((a, b) => b.priorityScore - a.priorityScore);
  }

  /**
   * Calculate priority score for a vulnerability
   */
  private calculatePriorityScore(
    vuln: Vulnerability,
    criteria: PrioritizationCriteria
  ): number {
    // Base score from severity
    const severityScore = SEVERITY_SCORES[vuln.severity];
    
    // Confidence factor
    const confidenceScore = vuln.confidence * 100;
    
    // Exploitability (estimate based on type)
    const exploitabilityScore = this.estimateExploitability(vuln);
    
    // Impact (estimate based on type and severity)
    const impactScore = this.estimateImpact(vuln);
    
    // Custom scorer if provided
    const customScore = criteria.customScorer?.(vuln) ?? 0;
    
    // Weighted sum
    const score = 
      severityScore * criteria.severityWeight +
      confidenceScore * criteria.confidenceWeight +
      exploitabilityScore * criteria.exploitabilityWeight +
      impactScore * criteria.impactWeight +
      customScore;
    
    return Math.round(score * 100) / 100;
  }

  /**
   * Estimate exploitability based on vulnerability type
   */
  private estimateExploitability(vuln: Vulnerability): number {
    // High exploitability types
    const highExploit = ['injection', 'xss', 'command-injection', 'path-traversal'];
    // Medium exploitability types
    const medExploit = ['broken-access', 'ssrf', 'open-redirect'];
    
    const vulnType = (vuln as unknown as { type?: string }).type;
    
    if (vulnType && highExploit.includes(vulnType)) return 90;
    if (vulnType && medExploit.includes(vulnType)) return 60;
    return 40;
  }

  /**
   * Estimate impact based on vulnerability characteristics
   */
  private estimateImpact(vuln: Vulnerability): number {
    // Critical and high severity have high impact
    if (vuln.severity === 'critical') return 100;
    if (vuln.severity === 'high') return 80;
    if (vuln.severity === 'medium') return 50;
    if (vuln.severity === 'low') return 20;
    return 10;
  }

  /**
   * Calculate individual risk score for a vulnerability
   */
  private calculateIndividualRiskScore(vuln: Vulnerability): number {
    const severityScore = SEVERITY_SCORES[vuln.severity];
    const confidenceFactor = vuln.confidence;
    
    // Base risk from severity and confidence
    const baseRisk = severityScore * confidenceFactor;
    
    // Adjust for multiple detection sources (indicates higher certainty)
    const sourceFactor = 'sources' in vuln 
      ? Math.min(1.2, 1 + ((vuln as AggregatedVulnerability).sources.length - 1) * 0.1)
      : 1;
    
    return Math.min(100, Math.round(baseRisk * sourceFactor));
  }

  /**
   * Calculate overall risk score for all vulnerabilities
   * @trace REQ-SEC2-REPORT-001
   */
  calculateRiskScore(vulnerabilities: Vulnerability[]): number {
    if (vulnerabilities.length === 0) return 0;
    
    // Weight critical/high vulnerabilities more heavily
    let totalRisk = 0;
    let weightSum = 0;
    
    for (const vuln of vulnerabilities) {
      const weight = SEVERITY_SCORES[vuln.severity] / 100;
      const risk = this.calculateIndividualRiskScore(vuln);
      
      totalRisk += risk * weight;
      weightSum += weight;
    }
    
    // Normalize to 0-100
    const avgWeightedRisk = weightSum > 0 ? totalRisk / weightSum : 0;
    
    // Factor in the number of vulnerabilities
    const countFactor = Math.min(1.5, 1 + vulnerabilities.length * 0.02);
    
    return Math.min(100, Math.round(avgWeightedRisk * countFactor));
  }

  /**
   * Configure deduplication rules
   */
  setDeduplicationRules(rules: DeduplicationRule[]): void {
    this.deduplicationRules = rules;
  }

  /**
   * Configure prioritization criteria
   */
  setPrioritizationCriteria(criteria: PrioritizationCriteria): void {
    this.prioritizationCriteria = criteria;
  }

  /**
   * Merge two similar vulnerabilities into one
   * @trace DES-SEC2-ORCH-003
   */
  mergeSimilar(vuln1: Vulnerability, vuln2: Vulnerability): Vulnerability {
    // Use the higher severity vulnerability as the base
    const base = SEVERITY_SCORES[vuln1.severity] >= SEVERITY_SCORES[vuln2.severity]
      ? vuln1
      : vuln2;
    const other = base === vuln1 ? vuln2 : vuln1;
    
    // Merge CWEs
    const mergedCwes = Array.from(new Set([...base.cwes, ...other.cwes]));
    
    // Use higher confidence
    const mergedConfidence = Math.max(base.confidence, other.confidence);
    
    // Expand location to cover both
    const mergedLocation: SourceLocation = {
      file: base.location.file,
      startLine: Math.min(base.location.startLine, other.location.startLine),
      endLine: Math.max(base.location.endLine, other.location.endLine),
      startColumn: Math.min(base.location.startColumn, other.location.startColumn),
      endColumn: Math.max(base.location.endColumn, other.location.endColumn),
    };
    
    // Combine descriptions
    const description = base.description === other.description
      ? base.description
      : `${base.description} (merged with related finding)`;
    
    return {
      ...base,
      cwes: mergedCwes,
      confidence: mergedConfidence,
      location: mergedLocation,
      description,
    };
  }
}

/**
 * Create a default result aggregator instance
 */
export function createResultAggregator(
  rules?: DeduplicationRule[],
  criteria?: PrioritizationCriteria
): ResultAggregator {
  return new ResultAggregator(rules, criteria);
}

/**
 * Merge similar vulnerabilities based on location overlap
 */
export function mergeSimilarByLocation(
  vulnerabilities: Vulnerability[],
  overlapThreshold: number = 0.5
): Vulnerability[] {
  // Sort by file and start line
  const sorted = [...vulnerabilities].sort((a, b) => {
    if (a.location.file !== b.location.file) {
      return a.location.file.localeCompare(b.location.file);
    }
    return a.location.startLine - b.location.startLine;
  });
  
  const result: Vulnerability[] = [];
  let i = 0;
  
  while (i < sorted.length) {
    const current = sorted[i];
    const overlapping: Vulnerability[] = [current];
    
    // Find all overlapping vulnerabilities
    for (let j = i + 1; j < sorted.length; j++) {
      const other = sorted[j];
      
      if (other.location.file !== current.location.file) break;
      
      const overlap = calculateLineOverlap(current.location, other.location);
      if (overlap >= overlapThreshold) {
        overlapping.push(other);
      } else {
        break;
      }
    }
    
    if (overlapping.length === 1) {
      result.push(current);
    } else {
      // Merge overlapping vulnerabilities
      const merged = mergeOverlapping(overlapping);
      result.push(merged);
    }
    
    i += overlapping.length;
  }
  
  return result;
}

/**
 * Calculate line overlap ratio between two locations
 */
function calculateLineOverlap(loc1: SourceLocation, loc2: SourceLocation): number {
  const start = Math.max(loc1.startLine, loc2.startLine);
  const end = Math.min(loc1.endLine, loc2.endLine);
  
  if (start > end) return 0;
  
  const overlapLines = end - start + 1;
  const totalLines = Math.max(loc1.endLine, loc2.endLine) - Math.min(loc1.startLine, loc2.startLine) + 1;
  
  return overlapLines / totalLines;
}

/**
 * Merge overlapping vulnerabilities
 */
function mergeOverlapping(vulnerabilities: Vulnerability[]): Vulnerability {
  // Use the highest severity one as base
  const sorted = vulnerabilities.sort((a, b) => 
    SEVERITY_SCORES[b.severity] - SEVERITY_SCORES[a.severity]
  );
  
  const base = sorted[0];
  const mergedCwes = Array.from(new Set(vulnerabilities.flatMap(v => v.cwes)));
  
  return {
    ...base,
    cwes: mergedCwes,
    confidence: Math.max(...vulnerabilities.map(v => v.confidence)),
    description: `${base.description} (${vulnerabilities.length} related findings merged)`,
  };
}
