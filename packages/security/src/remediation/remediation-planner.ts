/**
 * @fileoverview Remediation Planner for Security Vulnerabilities
 * @module @nahisaho/musubix-security/remediation/remediation-planner
 * 
 * Plans and prioritizes remediation of security vulnerabilities
 * considering dependencies, risk, and effort.
 */

import type { Vulnerability, Fix, ScanResult } from '../types/index.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Remediation plan
 */
export interface RemediationPlan {
  /** Plan ID */
  id: string;
  /** Plan name */
  name: string;
  /** Created timestamp */
  createdAt: Date;
  /** Plan status */
  status: PlanStatus;
  /** Total vulnerabilities */
  totalVulnerabilities: number;
  /** Planned phases */
  phases: RemediationPhase[];
  /** Estimated effort */
  estimatedEffort: EffortEstimate;
  /** Risk reduction */
  riskReduction: RiskReduction;
  /** Dependencies between fixes */
  dependencies: FixDependency[];
  /** Metadata */
  metadata: PlanMetadata;
}

/**
 * Plan status
 */
export type PlanStatus = 'draft' | 'approved' | 'in-progress' | 'completed' | 'cancelled';

/**
 * Remediation phase
 */
export interface RemediationPhase {
  /** Phase number */
  phase: number;
  /** Phase name */
  name: string;
  /** Description */
  description: string;
  /** Fixes in this phase */
  fixes: PlannedFix[];
  /** Estimated duration */
  estimatedDuration: Duration;
  /** Prerequisites */
  prerequisites: string[];
  /** Risk level after phase */
  residualRisk: RiskLevel;
}

/**
 * Planned fix
 */
export interface PlannedFix {
  /** Fix reference */
  fix: Fix;
  /** Vulnerability reference */
  vulnerability: Vulnerability;
  /** Priority score */
  priorityScore: number;
  /** Effort estimate */
  effort: EffortEstimate;
  /** Blocked by (fix IDs) */
  blockedBy: string[];
  /** Blocks (fix IDs) */
  blocks: string[];
  /** Status */
  status: FixStatus;
  /** Assigned to */
  assignedTo?: string;
  /** Due date */
  dueDate?: Date;
}

/**
 * Fix status
 */
export type FixStatus = 'pending' | 'in-progress' | 'testing' | 'completed' | 'blocked' | 'skipped';

/**
 * Fix dependency
 */
export interface FixDependency {
  /** Source fix ID */
  fixId: string;
  /** Depends on fix ID */
  dependsOn: string;
  /** Dependency type */
  type: DependencyType;
  /** Reason */
  reason: string;
}

/**
 * Dependency type
 */
export type DependencyType = 'requires' | 'conflicts' | 'enhances' | 'supersedes';

/**
 * Effort estimate
 */
export interface EffortEstimate {
  /** Estimated hours */
  hours: number;
  /** Confidence (0-1) */
  confidence: number;
  /** Complexity */
  complexity: 'low' | 'medium' | 'high' | 'very-high';
  /** Testing hours */
  testingHours: number;
  /** Review hours */
  reviewHours: number;
}

/**
 * Duration
 */
export interface Duration {
  /** Value */
  value: number;
  /** Unit */
  unit: 'hours' | 'days' | 'weeks';
}

/**
 * Risk reduction
 */
export interface RiskReduction {
  /** Initial risk score */
  initialRisk: number;
  /** Final risk score */
  finalRisk: number;
  /** Reduction percentage */
  reductionPercent: number;
  /** Critical vulnerabilities fixed */
  criticalFixed: number;
  /** High vulnerabilities fixed */
  highFixed: number;
  /** Medium vulnerabilities fixed */
  mediumFixed: number;
  /** Low vulnerabilities fixed */
  lowFixed: number;
}

/**
 * Risk level
 */
export type RiskLevel = 'critical' | 'high' | 'medium' | 'low' | 'minimal';

/**
 * Plan metadata
 */
export interface PlanMetadata {
  /** Author */
  author?: string;
  /** Approved by */
  approvedBy?: string;
  /** Approval date */
  approvalDate?: Date;
  /** Target completion */
  targetCompletion?: Date;
  /** Notes */
  notes?: string[];
  /** Tags */
  tags?: string[];
}

/**
 * Prioritization strategy
 */
export type PrioritizationStrategy = 
  | 'severity-first'
  | 'effort-first'
  | 'risk-based'
  | 'dependency-aware'
  | 'balanced';

/**
 * Planner options
 */
export interface RemediationPlannerOptions {
  /** Default prioritization strategy */
  defaultStrategy?: PrioritizationStrategy;
  /** Max fixes per phase */
  maxFixesPerPhase?: number;
  /** Include effort estimates */
  includeEffortEstimates?: boolean;
  /** Team size for effort calculation */
  teamSize?: number;
}

/**
 * Planning options
 */
export interface PlanningOptions {
  /** Prioritization strategy */
  strategy?: PrioritizationStrategy;
  /** Max phases */
  maxPhases?: number;
  /** Group by file */
  groupByFile?: boolean;
  /** Exclude severities */
  excludeSeverities?: string[];
  /** Target completion date */
  targetDate?: Date;
}

// ============================================================================
// RemediationPlanner Class
// ============================================================================

/**
 * Planner for vulnerability remediation
 * 
 * @example
 * ```typescript
 * const planner = createRemediationPlanner();
 * const plan = planner.createPlan(scanResult, fixes, { strategy: 'risk-based' });
 * console.log(plan.phases.length); // Number of remediation phases
 * ```
 */
export class RemediationPlanner {
  private options: Required<RemediationPlannerOptions>;

  constructor(options: RemediationPlannerOptions = {}) {
    this.options = {
      defaultStrategy: options.defaultStrategy ?? 'risk-based',
      maxFixesPerPhase: options.maxFixesPerPhase ?? 10,
      includeEffortEstimates: options.includeEffortEstimates ?? true,
      teamSize: options.teamSize ?? 2,
    };
  }

  /**
   * Create a remediation plan
   */
  createPlan(
    scanResult: ScanResult,
    fixes: Fix[],
    options: PlanningOptions = {}
  ): RemediationPlan {
    const strategy = options.strategy ?? this.options.defaultStrategy;
    
    // Match vulnerabilities to fixes
    const plannedFixes = this.createPlannedFixes(scanResult.vulnerabilities, fixes);
    
    // Detect dependencies
    const dependencies = this.detectDependencies(plannedFixes);
    
    // Apply prioritization
    const prioritized = this.prioritize(plannedFixes, strategy, dependencies);
    
    // Create phases
    const phases = this.createPhases(prioritized, dependencies, options);
    
    // Calculate metrics
    const estimatedEffort = this.calculateTotalEffort(plannedFixes);
    const riskReduction = this.calculateRiskReduction(scanResult.vulnerabilities);

    return {
      id: `PLAN-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
      name: `Security Remediation Plan`,
      createdAt: new Date(),
      status: 'draft',
      totalVulnerabilities: scanResult.vulnerabilities.length,
      phases,
      estimatedEffort,
      riskReduction,
      dependencies,
      metadata: {
        notes: [],
        tags: ['security', 'remediation'],
      },
    };
  }

  /**
   * Update plan status
   */
  updatePlanStatus(plan: RemediationPlan, status: PlanStatus): RemediationPlan {
    return {
      ...plan,
      status,
      metadata: {
        ...plan.metadata,
        approvalDate: status === 'approved' ? new Date() : plan.metadata.approvalDate,
      },
    };
  }

  /**
   * Mark a fix as completed
   */
  markFixCompleted(plan: RemediationPlan, fixId: string): RemediationPlan {
    const updatedPhases = plan.phases.map(phase => ({
      ...phase,
      fixes: phase.fixes.map(pf => 
        pf.fix.id === fixId ? { ...pf, status: 'completed' as FixStatus } : pf
      ),
    }));

    // Check if phase is complete
    for (const phase of updatedPhases) {
      const allComplete = phase.fixes.every(f => f.status === 'completed' || f.status === 'skipped');
      if (allComplete) {
        // Could trigger next phase
      }
    }

    return {
      ...plan,
      phases: updatedPhases,
    };
  }

  /**
   * Get next fixes to work on
   */
  getNextFixes(plan: RemediationPlan, count: number = 5): PlannedFix[] {
    const available: PlannedFix[] = [];

    for (const phase of plan.phases) {
      for (const fix of phase.fixes) {
        if (fix.status === 'pending' && fix.blockedBy.length === 0) {
          available.push(fix);
          if (available.length >= count) break;
        }
      }
      if (available.length >= count) break;
    }

    return available;
  }

  /**
   * Calculate plan progress
   */
  calculateProgress(plan: RemediationPlan): {
    totalFixes: number;
    completedFixes: number;
    percentComplete: number;
    currentPhase: number;
  } {
    let totalFixes = 0;
    let completedFixes = 0;
    let currentPhase = 0;

    for (const phase of plan.phases) {
      for (const fix of phase.fixes) {
        totalFixes++;
        if (fix.status === 'completed') {
          completedFixes++;
        }
      }

      const phaseComplete = phase.fixes.every(
        f => f.status === 'completed' || f.status === 'skipped'
      );
      if (!phaseComplete && currentPhase === 0) {
        currentPhase = phase.phase;
      }
    }

    return {
      totalFixes,
      completedFixes,
      percentComplete: totalFixes > 0 ? (completedFixes / totalFixes) * 100 : 0,
      currentPhase: currentPhase || plan.phases.length,
    };
  }

  /**
   * Generate remediation report
   */
  generateReport(plan: RemediationPlan): string {
    const progress = this.calculateProgress(plan);
    const lines: string[] = [];

    lines.push('# Security Remediation Plan Report');
    lines.push('');
    lines.push(`**Plan ID:** ${plan.id}`);
    lines.push(`**Status:** ${plan.status}`);
    lines.push(`**Created:** ${plan.createdAt.toISOString()}`);
    lines.push('');

    lines.push('## Summary');
    lines.push('');
    lines.push(`- Total Vulnerabilities: ${plan.totalVulnerabilities}`);
    lines.push(`- Total Fixes: ${progress.totalFixes}`);
    lines.push(`- Completed: ${progress.completedFixes} (${progress.percentComplete.toFixed(1)}%)`);
    lines.push(`- Current Phase: ${progress.currentPhase} of ${plan.phases.length}`);
    lines.push('');

    lines.push('## Risk Reduction');
    lines.push('');
    lines.push(`- Initial Risk Score: ${plan.riskReduction.initialRisk}`);
    lines.push(`- Target Risk Score: ${plan.riskReduction.finalRisk}`);
    lines.push(`- Reduction: ${plan.riskReduction.reductionPercent.toFixed(1)}%`);
    lines.push(`- Critical Fixed: ${plan.riskReduction.criticalFixed}`);
    lines.push(`- High Fixed: ${plan.riskReduction.highFixed}`);
    lines.push('');

    lines.push('## Effort Estimate');
    lines.push('');
    lines.push(`- Development: ${plan.estimatedEffort.hours} hours`);
    lines.push(`- Testing: ${plan.estimatedEffort.testingHours} hours`);
    lines.push(`- Review: ${plan.estimatedEffort.reviewHours} hours`);
    lines.push(`- Complexity: ${plan.estimatedEffort.complexity}`);
    lines.push('');

    lines.push('## Phases');
    lines.push('');

    for (const phase of plan.phases) {
      const phaseComplete = phase.fixes.filter(f => f.status === 'completed').length;
      lines.push(`### Phase ${phase.phase}: ${phase.name}`);
      lines.push('');
      lines.push(`${phase.description}`);
      lines.push('');
      lines.push(`Progress: ${phaseComplete}/${phase.fixes.length} fixes complete`);
      lines.push('');
      lines.push('| Fix | Vulnerability | Severity | Status | Effort |');
      lines.push('|-----|---------------|----------|--------|--------|');

      for (const fix of phase.fixes) {
        lines.push(
          `| ${fix.fix.title.substring(0, 30)} | ${fix.vulnerability.id} | ` +
          `${fix.vulnerability.severity} | ${fix.status} | ${fix.effort.hours}h |`
        );
      }
      lines.push('');
    }

    return lines.join('\n');
  }

  // ============================================================================
  // Private Methods
  // ============================================================================

  private createPlannedFixes(
    vulnerabilities: Vulnerability[],
    fixes: Fix[]
  ): PlannedFix[] {
    const plannedFixes: PlannedFix[] = [];
    const fixMap = new Map(fixes.map(f => [f.vulnerabilityId, f]));

    for (const vuln of vulnerabilities) {
      const fix = fixMap.get(vuln.id);
      if (fix) {
        plannedFixes.push({
          fix,
          vulnerability: vuln,
          priorityScore: this.calculatePriorityScore(vuln, fix),
          effort: this.estimateEffort(vuln, fix),
          blockedBy: [],
          blocks: [],
          status: 'pending',
        });
      }
    }

    return plannedFixes;
  }

  private detectDependencies(plannedFixes: PlannedFix[]): FixDependency[] {
    const dependencies: FixDependency[] = [];

    // Group fixes by file
    const byFile = new Map<string, PlannedFix[]>();
    for (const pf of plannedFixes) {
      const file = pf.vulnerability.location.file;
      const fileFixes = byFile.get(file) || [];
      fileFixes.push(pf);
      byFile.set(file, fileFixes);
    }

    // Detect conflicts within same file
    for (const [file, fileFixes] of byFile) {
      for (let i = 0; i < fileFixes.length; i++) {
        for (let j = i + 1; j < fileFixes.length; j++) {
          const fix1 = fileFixes[i];
          const fix2 = fileFixes[j];

          // Check for overlapping line ranges
          const loc1 = fix1.vulnerability.location;
          const loc2 = fix2.vulnerability.location;

          if (this.rangesOverlap(
            loc1.startLine, loc1.endLine ?? loc1.startLine,
            loc2.startLine, loc2.endLine ?? loc2.startLine
          )) {
            dependencies.push({
              fixId: fix1.fix.id,
              dependsOn: fix2.fix.id,
              type: 'conflicts',
              reason: `Overlapping code regions in ${file}`,
            });
          }
        }
      }
    }

    // Check for type dependencies (e.g., fix secrets before fixing crypto)
    const typeOrder: Record<string, number> = {
      'hardcoded-secret': 1,
      'weak-crypto': 2,
      'sql-injection': 3,
      'xss': 3,
      'path-traversal': 3,
    };

    for (const fix1 of plannedFixes) {
      for (const fix2 of plannedFixes) {
        if (fix1.fix.id === fix2.fix.id) continue;

        const order1 = typeOrder[fix1.vulnerability.type] || 10;
        const order2 = typeOrder[fix2.vulnerability.type] || 10;

        if (order1 < order2 && fix1.vulnerability.location.file === fix2.vulnerability.location.file) {
          dependencies.push({
            fixId: fix2.fix.id,
            dependsOn: fix1.fix.id,
            type: 'requires',
            reason: `${fix1.vulnerability.type} should be fixed before ${fix2.vulnerability.type}`,
          });
        }
      }
    }

    return dependencies;
  }

  private rangesOverlap(
    start1: number, end1: number,
    start2: number, end2: number
  ): boolean {
    return !(end1 < start2 || end2 < start1);
  }

  private prioritize(
    plannedFixes: PlannedFix[],
    strategy: PrioritizationStrategy,
    dependencies: FixDependency[]
  ): PlannedFix[] {
    // Apply blocked relationships
    const depMap = new Map<string, string[]>();
    for (const dep of dependencies) {
      if (dep.type === 'requires') {
        const blockedBy = depMap.get(dep.fixId) || [];
        blockedBy.push(dep.dependsOn);
        depMap.set(dep.fixId, blockedBy);
      }
    }

    for (const pf of plannedFixes) {
      pf.blockedBy = depMap.get(pf.fix.id) || [];
    }

    // Sort by strategy
    const sorted = [...plannedFixes];

    switch (strategy) {
      case 'severity-first':
        sorted.sort((a, b) => {
          const sevOrder = { critical: 0, high: 1, medium: 2, low: 3, info: 4 };
          const aSev = sevOrder[a.vulnerability.severity as keyof typeof sevOrder] ?? 5;
          const bSev = sevOrder[b.vulnerability.severity as keyof typeof sevOrder] ?? 5;
          return aSev - bSev;
        });
        break;

      case 'effort-first':
        sorted.sort((a, b) => a.effort.hours - b.effort.hours);
        break;

      case 'risk-based':
        sorted.sort((a, b) => b.priorityScore - a.priorityScore);
        break;

      case 'dependency-aware':
        // Topological sort considering dependencies
        sorted.sort((a, b) => {
          if (a.blockedBy.includes(b.fix.id)) return 1;
          if (b.blockedBy.includes(a.fix.id)) return -1;
          return b.priorityScore - a.priorityScore;
        });
        break;

      case 'balanced':
      default:
        sorted.sort((a, b) => {
          // Combine severity and effort
          const aScore = a.priorityScore / (a.effort.hours || 1);
          const bScore = b.priorityScore / (b.effort.hours || 1);
          return bScore - aScore;
        });
    }

    return sorted;
  }

  private createPhases(
    prioritizedFixes: PlannedFix[],
    _dependencies: FixDependency[],
    options: PlanningOptions
  ): RemediationPhase[] {
    const phases: RemediationPhase[] = [];
    const remaining = [...prioritizedFixes];
    const completed = new Set<string>();
    let phaseNum = 1;

    while (remaining.length > 0 && phaseNum <= (options.maxPhases || 10)) {
      const phaseFixes: PlannedFix[] = [];
      const toRemove: number[] = [];

      for (let i = 0; i < remaining.length && phaseFixes.length < this.options.maxFixesPerPhase; i++) {
        const fix = remaining[i];
        
        // Check if all dependencies are met
        const blocked = fix.blockedBy.some(id => !completed.has(id));
        if (!blocked) {
          phaseFixes.push(fix);
          toRemove.push(i);
        }
      }

      // If no fixes can be added (circular dependency), force add
      if (phaseFixes.length === 0 && remaining.length > 0) {
        phaseFixes.push(remaining[0]);
        toRemove.push(0);
      }

      // Mark as completed
      for (const fix of phaseFixes) {
        completed.add(fix.fix.id);
      }

      // Remove from remaining (in reverse order to preserve indices)
      for (let i = toRemove.length - 1; i >= 0; i--) {
        remaining.splice(toRemove[i], 1);
      }

      // Determine phase name
      const phaseName = this.generatePhaseName(phaseFixes, phaseNum);

      phases.push({
        phase: phaseNum,
        name: phaseName,
        description: this.generatePhaseDescription(phaseFixes),
        fixes: phaseFixes,
        estimatedDuration: this.estimatePhaseDuration(phaseFixes),
        prerequisites: phaseNum > 1 ? [`Phase ${phaseNum - 1} completed`] : [],
        residualRisk: this.calculateResidualRisk(remaining),
      });

      phaseNum++;
    }

    return phases;
  }

  private generatePhaseName(fixes: PlannedFix[], phaseNum: number): string {
    // Determine dominant category
    const categories = fixes.map(f => f.vulnerability.type);
    const counts = new Map<string, number>();
    for (const cat of categories) {
      counts.set(cat, (counts.get(cat) || 0) + 1);
    }

    let maxCategory = '';
    let maxCount = 0;
    for (const [cat, count] of counts) {
      if (count > maxCount) {
        maxCount = count;
        maxCategory = cat;
      }
    }

    const severities = fixes.map(f => f.vulnerability.severity);
    const hasCritical = severities.includes('critical');
    const hasHigh = severities.includes('high');

    if (hasCritical) {
      return `Critical Security Fixes (Phase ${phaseNum})`;
    } else if (hasHigh) {
      return `High Priority Fixes (Phase ${phaseNum})`;
    } else if (maxCategory) {
      return `${this.formatType(maxCategory)} Remediation (Phase ${phaseNum})`;
    }

    return `Security Fixes Phase ${phaseNum}`;
  }

  private formatType(type: string): string {
    return type.split('-').map(w => w.charAt(0).toUpperCase() + w.slice(1)).join(' ');
  }

  private generatePhaseDescription(fixes: PlannedFix[]): string {
    const types = [...new Set(fixes.map(f => f.vulnerability.type))];
    const count = fixes.length;

    return `Fix ${count} vulnerabilities including: ${types.map(t => this.formatType(t)).join(', ')}`;
  }

  private estimatePhaseDuration(fixes: PlannedFix[]): Duration {
    const totalHours = fixes.reduce((sum, f) => sum + f.effort.hours, 0);
    const hoursPerDay = 6; // Effective development hours

    const days = Math.ceil(totalHours / (this.options.teamSize * hoursPerDay));

    if (days <= 5) {
      return { value: days, unit: 'days' };
    } else {
      return { value: Math.ceil(days / 5), unit: 'weeks' };
    }
  }

  private calculateResidualRisk(remainingFixes: PlannedFix[]): RiskLevel {
    const criticalCount = remainingFixes.filter(f => f.vulnerability.severity === 'critical').length;
    const highCount = remainingFixes.filter(f => f.vulnerability.severity === 'high').length;

    if (criticalCount > 0) return 'critical';
    if (highCount > 2) return 'high';
    if (highCount > 0 || remainingFixes.length > 5) return 'medium';
    if (remainingFixes.length > 0) return 'low';
    return 'minimal';
  }

  private calculatePriorityScore(vuln: Vulnerability, fix: Fix): number {
    const severityScores = { critical: 100, high: 75, medium: 50, low: 25, info: 10 };
    const severityScore = severityScores[vuln.severity as keyof typeof severityScores] || 50;

    // Adjust by confidence
    const confidenceAdjustment = fix.confidence * 20;

    // Additional weight based on CWE count
    const cweAdjustment = (vuln.cwes?.length || 0) * 2;

    return severityScore + confidenceAdjustment + cweAdjustment;
  }

  private estimateEffort(vuln: Vulnerability, fix: Fix): EffortEstimate {
    // Base hours by vulnerability type
    const baseHours: Record<string, number> = {
      'sql-injection': 4,
      'xss': 3,
      'path-traversal': 2,
      'hardcoded-secret': 1,
      'weak-crypto': 2,
      'command-injection': 4,
      'insecure-deserialization': 5,
      'xxe': 3,
      'ssrf': 4,
    };

    const hours = baseHours[vuln.type] || 3;

    // Adjust by number of edits
    const editAdjustment = fix.edits.length * 0.5;

    // Determine complexity
    let complexity: EffortEstimate['complexity'] = 'low';
    if (fix.breakingChange || fix.edits.length > 5) {
      complexity = 'high';
    } else if (fix.edits.length > 2 || vuln.severity === 'critical') {
      complexity = 'medium';
    }

    const totalHours = hours + editAdjustment;

    return {
      hours: Math.ceil(totalHours),
      confidence: fix.confidence,
      complexity,
      testingHours: Math.ceil(totalHours * 0.5),
      reviewHours: Math.ceil(totalHours * 0.25),
    };
  }

  private calculateTotalEffort(plannedFixes: PlannedFix[]): EffortEstimate {
    const totalHours = plannedFixes.reduce((sum, f) => sum + f.effort.hours, 0);
    const totalTesting = plannedFixes.reduce((sum, f) => sum + f.effort.testingHours, 0);
    const totalReview = plannedFixes.reduce((sum, f) => sum + f.effort.reviewHours, 0);

    let complexity: EffortEstimate['complexity'] = 'low';
    if (totalHours > 100) complexity = 'very-high';
    else if (totalHours > 50) complexity = 'high';
    else if (totalHours > 20) complexity = 'medium';

    return {
      hours: totalHours,
      confidence: 0.7, // Overall estimate confidence
      complexity,
      testingHours: totalTesting,
      reviewHours: totalReview,
    };
  }

  private calculateRiskReduction(vulnerabilities: Vulnerability[]): RiskReduction {
    const counts = { critical: 0, high: 0, medium: 0, low: 0 };
    const scores = { critical: 100, high: 75, medium: 50, low: 25 };

    let initialRisk = 0;

    for (const vuln of vulnerabilities) {
      const sev = vuln.severity as keyof typeof counts;
      if (counts[sev] !== undefined) {
        counts[sev]++;
        initialRisk += scores[sev] || 0;
      }
    }

    return {
      initialRisk,
      finalRisk: 0, // Assuming all fixed
      reductionPercent: 100,
      criticalFixed: counts.critical,
      highFixed: counts.high,
      mediumFixed: counts.medium,
      lowFixed: counts.low,
    };
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create a remediation planner
 */
export function createRemediationPlanner(options?: RemediationPlannerOptions): RemediationPlanner {
  return new RemediationPlanner(options);
}

/**
 * Quick create a plan from scan results
 */
export function quickCreatePlan(
  scanResult: ScanResult,
  fixes: Fix[]
): RemediationPlan {
  const planner = createRemediationPlanner();
  return planner.createPlan(scanResult, fixes);
}
