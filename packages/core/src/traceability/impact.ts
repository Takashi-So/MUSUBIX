/**
 * Impact Analyzer
 * 
 * Analyzes the impact of changes across the traceability chain
 * 
 * @packageDocumentation
 * @module traceability/impact
 * 
 * @see REQ-TRA-002 - Impact Analysis
 * @see Article IV - Traceability Requirements
 */

import type {
  TraceabilityManager,
  TraceableArtifact,
  ArtifactType,
} from './manager.js';

/**
 * Change type
 */
export type ChangeType =
  | 'add'
  | 'modify'
  | 'delete'
  | 'deprecate';

/**
 * Change proposal
 */
export interface ChangeProposal {
  /** Artifact to change */
  artifactId: string;
  /** Type of change */
  changeType: ChangeType;
  /** Description of change */
  description: string;
  /** New values (for modify) */
  newValues?: Partial<TraceableArtifact>;
  /** Rationale */
  rationale?: string;
}

/**
 * Impact severity
 */
export type ImpactSeverity = 'critical' | 'high' | 'medium' | 'low';

/**
 * Impacted artifact
 */
export interface ImpactedArtifact {
  /** Artifact */
  artifact: TraceableArtifact;
  /** Impact severity */
  severity: ImpactSeverity;
  /** Distance from changed artifact */
  distance: number;
  /** Impact type */
  impactType: 'direct' | 'indirect' | 'ripple';
  /** Required actions */
  requiredActions: string[];
  /** Estimated effort (hours) */
  estimatedEffort: number;
}

/**
 * Impact analysis result
 */
export interface ImpactAnalysisResult {
  /** Original change proposal */
  proposal: ChangeProposal;
  /** Changed artifact */
  changedArtifact: TraceableArtifact;
  /** Directly impacted artifacts */
  directImpacts: ImpactedArtifact[];
  /** Indirectly impacted artifacts */
  indirectImpacts: ImpactedArtifact[];
  /** Total impact summary */
  summary: ImpactSummary;
  /** Risk assessment */
  risk: RiskAssessment;
  /** Recommendations */
  recommendations: string[];
}

/**
 * Impact summary
 */
export interface ImpactSummary {
  /** Total affected artifacts */
  totalAffected: number;
  /** By type */
  byType: Record<ArtifactType, number>;
  /** By severity */
  bySeverity: Record<ImpactSeverity, number>;
  /** Total estimated effort */
  totalEffort: number;
  /** Scope percentage (affected / total) */
  scopePercentage: number;
}

/**
 * Risk assessment
 */
export interface RiskAssessment {
  /** Overall risk level */
  level: 'critical' | 'high' | 'medium' | 'low';
  /** Risk score (0-100) */
  score: number;
  /** Risk factors */
  factors: RiskFactor[];
  /** Mitigation suggestions */
  mitigations: string[];
}

/**
 * Risk factor
 */
export interface RiskFactor {
  /** Factor name */
  name: string;
  /** Factor description */
  description: string;
  /** Weight (0-1) */
  weight: number;
  /** Score contribution */
  contribution: number;
}

/**
 * Impact analyzer configuration
 */
export interface ImpactAnalyzerConfig {
  /** Maximum depth for ripple effect analysis */
  maxDepth: number;
  /** Include deprecated artifacts */
  includeDeprecated: boolean;
  /** Effort estimation multipliers */
  effortMultipliers: Record<ArtifactType, number>;
  /** Severity weights for risk calculation */
  severityWeights: Record<ImpactSeverity, number>;
}

/**
 * Default configuration
 */
export const DEFAULT_IMPACT_CONFIG: ImpactAnalyzerConfig = {
  maxDepth: 5,
  includeDeprecated: false,
  effortMultipliers: {
    requirement: 2,
    design: 4,
    code: 8,
    test: 4,
    task: 1,
    documentation: 2,
  },
  severityWeights: {
    critical: 10,
    high: 5,
    medium: 2,
    low: 1,
  },
};

/**
 * Impact Analyzer
 * 
 * Analyzes change impacts across the traceability chain
 */
export class ImpactAnalyzer {
  private config: ImpactAnalyzerConfig;
  private traceability: TraceabilityManager;

  constructor(
    traceability: TraceabilityManager,
    config?: Partial<ImpactAnalyzerConfig>
  ) {
    this.traceability = traceability;
    this.config = { ...DEFAULT_IMPACT_CONFIG, ...config };
  }

  /**
   * Analyze impact of a proposed change
   */
  analyzeImpact(proposal: ChangeProposal): ImpactAnalysisResult {
    const artifact = this.traceability.getArtifact(proposal.artifactId);
    
    if (!artifact) {
      throw new Error(`Artifact not found: ${proposal.artifactId}`);
    }

    // Get direct impacts (immediate dependencies)
    const directImpacts = this.getDirectImpacts(artifact, proposal);
    
    // Get indirect impacts (ripple effects)
    const indirectImpacts = this.getIndirectImpacts(
      artifact,
      directImpacts,
      proposal
    );

    // Generate summary
    const allImpacts = [...directImpacts, ...indirectImpacts];
    const summary = this.generateSummary(allImpacts);

    // Assess risk
    const risk = this.assessRisk(proposal, allImpacts, summary);

    // Generate recommendations
    const recommendations = this.generateRecommendations(
      proposal,
      allImpacts,
      risk
    );

    return {
      proposal,
      changedArtifact: artifact,
      directImpacts,
      indirectImpacts,
      summary,
      risk,
      recommendations,
    };
  }

  /**
   * Analyze multiple changes together
   */
  analyzeBatchImpact(proposals: ChangeProposal[]): ImpactAnalysisResult[] {
    return proposals.map((p) => this.analyzeImpact(p));
  }

  /**
   * Get directly impacted artifacts
   */
  private getDirectImpacts(
    artifact: TraceableArtifact,
    proposal: ChangeProposal
  ): ImpactedArtifact[] {
    const impacts: ImpactedArtifact[] = [];

    // Get downstream artifacts (depend on this)
    const downstream = this.traceability.getDownstream(artifact.id);
    
    // Get upstream artifacts (this depends on)
    const upstream = this.traceability.getUpstream(artifact.id);

    // Process downstream
    for (const affected of downstream) {
      if (!this.config.includeDeprecated && affected.status === 'deprecated') {
        continue;
      }

      impacts.push({
        artifact: affected,
        severity: this.calculateSeverity(artifact, affected, proposal, 'direct'),
        distance: 1,
        impactType: 'direct',
        requiredActions: this.determineActions(affected, proposal),
        estimatedEffort: this.estimateEffort(affected, proposal),
      });
    }

    // For delete/modify, upstream may need updates too
    if (proposal.changeType === 'delete' || proposal.changeType === 'modify') {
      for (const affected of upstream) {
        if (!this.config.includeDeprecated && affected.status === 'deprecated') {
          continue;
        }

        impacts.push({
          artifact: affected,
          severity: this.calculateSeverity(artifact, affected, proposal, 'direct'),
          distance: 1,
          impactType: 'direct',
          requiredActions: ['Review dependency', 'Update references'],
          estimatedEffort: this.estimateEffort(affected, proposal) * 0.5,
        });
      }
    }

    return impacts;
  }

  /**
   * Get indirectly impacted artifacts (ripple effects)
   */
  private getIndirectImpacts(
    _source: TraceableArtifact,
    directImpacts: ImpactedArtifact[],
    proposal: ChangeProposal
  ): ImpactedArtifact[] {
    const impacts: ImpactedArtifact[] = [];
    const visited = new Set<string>();
    
    // Mark source and direct impacts as visited
    visited.add(proposal.artifactId);
    for (const impact of directImpacts) {
      visited.add(impact.artifact.id);
    }

    // BFS for ripple effects
    const queue: Array<{ artifact: TraceableArtifact; distance: number }> = [];
    
    for (const impact of directImpacts) {
      const downstream = this.traceability.getDownstream(impact.artifact.id);
      for (const d of downstream) {
        if (!visited.has(d.id)) {
          queue.push({ artifact: d, distance: 2 });
        }
      }
    }

    while (queue.length > 0) {
      const { artifact, distance } = queue.shift()!;
      
      if (visited.has(artifact.id) || distance > this.config.maxDepth) {
        continue;
      }

      if (!this.config.includeDeprecated && artifact.status === 'deprecated') {
        continue;
      }

      visited.add(artifact.id);

      impacts.push({
        artifact,
        severity: this.calculateIndirectSeverity(distance),
        distance,
        impactType: distance === 2 ? 'indirect' : 'ripple',
        requiredActions: ['Review for consistency', 'Update if affected'],
        estimatedEffort: this.estimateEffort(artifact, proposal) * Math.pow(0.5, distance - 1),
      });

      // Continue BFS
      const downstream = this.traceability.getDownstream(artifact.id);
      for (const d of downstream) {
        if (!visited.has(d.id)) {
          queue.push({ artifact: d, distance: distance + 1 });
        }
      }
    }

    return impacts;
  }

  /**
   * Calculate impact severity
   */
  private calculateSeverity(
    source: TraceableArtifact,
    target: TraceableArtifact,
    proposal: ChangeProposal,
    _impactType: 'direct' | 'indirect'
  ): ImpactSeverity {
    // Delete always has high impact on direct dependencies
    if (proposal.changeType === 'delete') {
      return 'critical';
    }

    // Requirements changes are high impact
    if (source.type === 'requirement') {
      if (target.type === 'code' || target.type === 'test') {
        return 'high';
      }
      return 'medium';
    }

    // Design changes impact code
    if (source.type === 'design' && target.type === 'code') {
      return 'high';
    }

    // Deprecation is medium impact
    if (proposal.changeType === 'deprecate') {
      return 'medium';
    }

    return 'low';
  }

  /**
   * Calculate indirect severity based on distance
   */
  private calculateIndirectSeverity(distance: number): ImpactSeverity {
    if (distance <= 2) return 'medium';
    if (distance <= 3) return 'low';
    return 'low';
  }

  /**
   * Determine required actions
   */
  private determineActions(
    artifact: TraceableArtifact,
    proposal: ChangeProposal
  ): string[] {
    const actions: string[] = [];

    switch (proposal.changeType) {
      case 'delete':
        actions.push(`Remove dependency on ${proposal.artifactId}`);
        actions.push('Find alternative implementation');
        break;

      case 'modify':
        if (artifact.type === 'code') {
          actions.push('Update implementation');
          actions.push('Run tests');
        } else if (artifact.type === 'test') {
          actions.push('Update test cases');
          actions.push('Verify test coverage');
        } else if (artifact.type === 'design') {
          actions.push('Review design consistency');
        }
        break;

      case 'deprecate':
        actions.push('Plan migration');
        actions.push('Update to new version');
        break;

      case 'add':
        actions.push('Review compatibility');
        break;
    }

    return actions;
  }

  /**
   * Estimate effort for impacted artifact
   */
  private estimateEffort(
    artifact: TraceableArtifact,
    proposal: ChangeProposal
  ): number {
    const baseEffort = this.config.effortMultipliers[artifact.type] ?? 1;
    
    let multiplier = 1;
    switch (proposal.changeType) {
      case 'delete':
        multiplier = 2;
        break;
      case 'modify':
        multiplier = 1;
        break;
      case 'deprecate':
        multiplier = 0.5;
        break;
      case 'add':
        multiplier = 0.25;
        break;
    }

    return baseEffort * multiplier;
  }

  /**
   * Generate impact summary
   */
  private generateSummary(impacts: ImpactedArtifact[]): ImpactSummary {
    const byType: Record<ArtifactType, number> = {
      requirement: 0,
      design: 0,
      code: 0,
      test: 0,
      task: 0,
      documentation: 0,
    };

    const bySeverity: Record<ImpactSeverity, number> = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
    };

    let totalEffort = 0;

    for (const impact of impacts) {
      byType[impact.artifact.type]++;
      bySeverity[impact.severity]++;
      totalEffort += impact.estimatedEffort;
    }

    // Get total artifacts from traceability (estimate)
    const totalArtifacts = this.estimateTotalArtifacts();

    return {
      totalAffected: impacts.length,
      byType,
      bySeverity,
      totalEffort: Math.round(totalEffort * 10) / 10,
      scopePercentage: totalArtifacts > 0
        ? Math.round((impacts.length / totalArtifacts) * 100 * 10) / 10
        : 0,
    };
  }

  /**
   * Estimate total artifacts
   */
  private estimateTotalArtifacts(): number {
    // This would need access to all artifacts
    // For now, estimate from the traceability manager
    let count = 0;
    const types: ArtifactType[] = ['requirement', 'design', 'code', 'test', 'task', 'documentation'];
    for (const type of types) {
      count += this.traceability.getArtifactsByType(type).length;
    }
    return count;
  }

  /**
   * Assess overall risk
   */
  private assessRisk(
    proposal: ChangeProposal,
    impacts: ImpactedArtifact[],
    summary: ImpactSummary
  ): RiskAssessment {
    const factors: RiskFactor[] = [];
    let totalScore = 0;

    // Factor 1: Change type
    const changeTypeScores: Record<ChangeType, number> = {
      delete: 30,
      modify: 15,
      deprecate: 10,
      add: 5,
    };
    const changeScore = changeTypeScores[proposal.changeType];
    factors.push({
      name: 'Change Type',
      description: `${proposal.changeType} operation`,
      weight: 0.3,
      contribution: changeScore,
    });
    totalScore += changeScore;

    // Factor 2: Scope
    const scopeScore = Math.min(summary.scopePercentage, 30);
    factors.push({
      name: 'Scope',
      description: `${summary.scopePercentage}% of artifacts affected`,
      weight: 0.3,
      contribution: scopeScore,
    });
    totalScore += scopeScore;

    // Factor 3: Severity distribution
    const severityScore = 
      summary.bySeverity.critical * 10 +
      summary.bySeverity.high * 5 +
      summary.bySeverity.medium * 2 +
      summary.bySeverity.low * 0.5;
    const normalizedSeverity = Math.min(severityScore, 30);
    factors.push({
      name: 'Severity Distribution',
      description: `${summary.bySeverity.critical} critical, ${summary.bySeverity.high} high impacts`,
      weight: 0.4,
      contribution: normalizedSeverity,
    });
    totalScore += normalizedSeverity;

    // Determine level
    let level: RiskAssessment['level'];
    if (totalScore >= 60) level = 'critical';
    else if (totalScore >= 40) level = 'high';
    else if (totalScore >= 20) level = 'medium';
    else level = 'low';

    // Generate mitigations
    const mitigations = this.generateMitigations(level, impacts, summary);

    return {
      level,
      score: Math.round(totalScore),
      factors,
      mitigations,
    };
  }

  /**
   * Generate risk mitigations
   */
  private generateMitigations(
    level: RiskAssessment['level'],
    impacts: ImpactedArtifact[],
    summary: ImpactSummary
  ): string[] {
    const mitigations: string[] = [];

    if (level === 'critical' || level === 'high') {
      mitigations.push('Consider phased rollout');
      mitigations.push('Create comprehensive test plan');
      mitigations.push('Schedule stakeholder review');
    }

    if (summary.bySeverity.critical > 0) {
      mitigations.push('Address critical impacts first');
      mitigations.push('Create rollback plan');
    }

    if (summary.byType.test > 0) {
      mitigations.push('Update and run affected tests');
    }

    if (summary.byType.code > 3) {
      mitigations.push('Consider code review for all changes');
    }

    if (impacts.some((i) => i.distance > 3)) {
      mitigations.push('Verify ripple effects manually');
    }

    if (mitigations.length === 0) {
      mitigations.push('Standard review process sufficient');
    }

    return mitigations;
  }

  /**
   * Generate recommendations
   */
  private generateRecommendations(
    proposal: ChangeProposal,
    impacts: ImpactedArtifact[],
    risk: RiskAssessment
  ): string[] {
    const recommendations: string[] = [];

    // Based on risk level
    if (risk.level === 'critical') {
      recommendations.push('🚨 High-risk change - require approval from tech lead');
      recommendations.push('Create detailed change plan before proceeding');
    } else if (risk.level === 'high') {
      recommendations.push('⚠️ Significant change - schedule dedicated time for updates');
    }

    // Based on change type
    if (proposal.changeType === 'delete') {
      recommendations.push('Verify no runtime dependencies before deletion');
      recommendations.push('Consider deprecation before hard delete');
    }

    // Based on impacts
    const codeImpacts = impacts.filter((i) => i.artifact.type === 'code');
    if (codeImpacts.length > 0) {
      recommendations.push(`Update ${codeImpacts.length} code file(s)`);
    }

    const testImpacts = impacts.filter((i) => i.artifact.type === 'test');
    if (testImpacts.length > 0) {
      recommendations.push(`Update ${testImpacts.length} test(s) for verification`);
    }

    // Effort-based
    if (risk.score > 40) {
      recommendations.push(
        `Estimated effort: ~${Math.round(impacts.reduce((sum, i) => sum + i.estimatedEffort, 0))} hours`
      );
    }

    return recommendations;
  }
}

/**
 * Create impact analyzer instance
 */
export function createImpactAnalyzer(
  traceability: TraceabilityManager,
  config?: Partial<ImpactAnalyzerConfig>
): ImpactAnalyzer {
  return new ImpactAnalyzer(traceability, config);
}
