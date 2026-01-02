/**
 * Requirements Decomposer
 * 
 * Decomposes complex requirements into smaller, manageable units
 * 
 * @packageDocumentation
 * @module requirements/decomposer
 * 
 * @see REQ-RA-004 - Requirements Decomposition
 * @see Article II - Complete Requirements Specification
 */

/**
 * Decomposition strategy
 */
export type DecompositionStrategy = 
  | 'functional'    // By function/feature
  | 'behavioral'    // By behavior/scenario
  | 'structural'    // By component/module
  | 'temporal'      // By phase/timeline
  | 'stakeholder'   // By stakeholder needs
  | 'risk-based';   // By risk priority

/**
 * Complexity level
 */
export type ComplexityLevel = 'low' | 'medium' | 'high' | 'very-high';

/**
 * Decomposable requirement
 */
export interface DecomposableRequirement {
  /** Requirement ID */
  id: string;
  /** Title */
  title: string;
  /** Description */
  description: string;
  /** Type */
  type: 'functional' | 'non-functional' | 'constraint';
  /** Priority */
  priority: 'must' | 'should' | 'could' | 'wont';
  /** Complexity */
  complexity?: ComplexityLevel;
  /** Dependencies */
  dependencies?: string[];
  /** Stakeholders */
  stakeholders?: string[];
  /** Acceptance criteria */
  acceptanceCriteria?: string[];
}

/**
 * Decomposed requirement unit
 */
export interface RequirementUnit {
  /** Unit ID */
  id: string;
  /** Parent ID */
  parentId: string;
  /** Title */
  title: string;
  /** Description */
  description: string;
  /** Type */
  type: 'functional' | 'non-functional' | 'constraint';
  /** Granularity level */
  level: number;
  /** Estimated effort (hours) */
  estimatedEffort?: number;
  /** Assigned component */
  component?: string;
  /** Acceptance criteria */
  acceptanceCriteria: string[];
  /** Testable */
  testable: boolean;
  /** Dependencies */
  dependencies: string[];
  /** Tags */
  tags: string[];
}

/**
 * Decomposition result
 */
export interface DecompositionResult {
  /** Original requirement */
  original: DecomposableRequirement;
  /** Strategy used */
  strategy: DecompositionStrategy;
  /** Decomposed units */
  units: RequirementUnit[];
  /** Hierarchy tree */
  hierarchy: DecompositionNode;
  /** Statistics */
  stats: {
    totalUnits: number;
    avgDepth: number;
    maxDepth: number;
    estimatedTotalEffort?: number;
  };
  /** Recommendations */
  recommendations: string[];
}

/**
 * Decomposition tree node
 */
export interface DecompositionNode {
  /** Unit */
  unit: RequirementUnit;
  /** Children */
  children: DecompositionNode[];
}

/**
 * Decomposition config
 */
export interface DecomposerConfig {
  /** Default strategy */
  defaultStrategy: DecompositionStrategy;
  /** Max decomposition depth */
  maxDepth: number;
  /** Target unit size (hours) */
  targetUnitSize: number;
  /** Auto-generate acceptance criteria */
  autoAcceptanceCriteria: boolean;
  /** Auto-estimate effort */
  autoEstimate: boolean;
  /** Component mapping */
  componentMapping?: Record<string, string[]>;
}

/**
 * Default configuration
 */
export const DEFAULT_DECOMPOSER_CONFIG: DecomposerConfig = {
  defaultStrategy: 'functional',
  maxDepth: 4,
  targetUnitSize: 4, // 4 hours
  autoAcceptanceCriteria: true,
  autoEstimate: true,
};

/**
 * Complexity indicators
 */
const COMPLEXITY_INDICATORS = {
  keywords: {
    high: ['complex', 'multiple', 'various', 'all', 'every', 'integrate', 'synchronize'],
    medium: ['several', 'some', 'process', 'manage', 'handle'],
    low: ['single', 'simple', 'basic', 'display', 'show'],
  },
  patterns: {
    conjunction: /\band\b/gi,
    disjunction: /\bor\b/gi,
    conditional: /\bif\b.*\bthen\b/gi,
    iteration: /\bfor each\b|\bfor all\b|\bevery\b/gi,
  },
};

/**
 * Requirements Decomposer
 */
export class RequirementsDecomposer {
  private config: DecomposerConfig;

  constructor(config?: Partial<DecomposerConfig>) {
    this.config = { ...DEFAULT_DECOMPOSER_CONFIG, ...config };
  }

  /**
   * Decompose a requirement
   */
  decompose(
    requirement: DecomposableRequirement,
    strategy?: DecompositionStrategy
  ): DecompositionResult {
    const effectiveStrategy = strategy ?? this.config.defaultStrategy;
    
    // Analyze complexity
    const complexity = requirement.complexity ?? this.analyzeComplexity(requirement);

    // Decompose based on strategy
    const units = this.performDecomposition(requirement, effectiveStrategy, complexity);

    // Build hierarchy
    const hierarchy = this.buildHierarchy(units);

    // Calculate statistics
    const stats = this.calculateStats(units, hierarchy);

    // Generate recommendations
    const recommendations = this.generateRecommendations(requirement, units, stats);

    return {
      original: requirement,
      strategy: effectiveStrategy,
      units,
      hierarchy,
      stats,
      recommendations,
    };
  }

  /**
   * Analyze requirement complexity
   */
  analyzeComplexity(requirement: DecomposableRequirement): ComplexityLevel {
    const text = `${requirement.title} ${requirement.description}`.toLowerCase();
    let score = 0;

    // Check keywords
    for (const keyword of COMPLEXITY_INDICATORS.keywords.high) {
      if (text.includes(keyword)) score += 3;
    }
    for (const keyword of COMPLEXITY_INDICATORS.keywords.medium) {
      if (text.includes(keyword)) score += 2;
    }
    for (const keyword of COMPLEXITY_INDICATORS.keywords.low) {
      if (text.includes(keyword)) score -= 1;
    }

    // Check patterns
    const conjunctions = (text.match(COMPLEXITY_INDICATORS.patterns.conjunction) ?? []).length;
    const disjunctions = (text.match(COMPLEXITY_INDICATORS.patterns.disjunction) ?? []).length;
    const conditionals = (text.match(COMPLEXITY_INDICATORS.patterns.conditional) ?? []).length;
    const iterations = (text.match(COMPLEXITY_INDICATORS.patterns.iteration) ?? []).length;

    score += conjunctions * 2;
    score += disjunctions * 1.5;
    score += conditionals * 2;
    score += iterations * 2.5;

    // Check acceptance criteria count
    if (requirement.acceptanceCriteria) {
      score += requirement.acceptanceCriteria.length * 1.5;
    }

    // Check dependencies
    if (requirement.dependencies) {
      score += requirement.dependencies.length;
    }

    // Determine level
    if (score >= 15) return 'very-high';
    if (score >= 10) return 'high';
    if (score >= 5) return 'medium';
    return 'low';
  }

  /**
   * Perform decomposition
   */
  private performDecomposition(
    requirement: DecomposableRequirement,
    strategy: DecompositionStrategy,
    complexity: ComplexityLevel
  ): RequirementUnit[] {
    const units: RequirementUnit[] = [];

    switch (strategy) {
      case 'functional':
        units.push(...this.decomposeFunctional(requirement, complexity));
        break;
      case 'behavioral':
        units.push(...this.decomposeBehavioral(requirement, complexity));
        break;
      case 'structural':
        units.push(...this.decomposeStructural(requirement, complexity));
        break;
      case 'temporal':
        units.push(...this.decomposeTemporal(requirement, complexity));
        break;
      case 'stakeholder':
        units.push(...this.decomposeByStakeholder(requirement, complexity));
        break;
      case 'risk-based':
        units.push(...this.decomposeByRisk(requirement, complexity));
        break;
    }

    // Recursively decompose if units are still too large
    const refinedUnits: RequirementUnit[] = [];
    for (const unit of units) {
      if (this.shouldDecomposeMore(unit)) {
        const subUnits = this.decomposeUnit(unit, strategy);
        refinedUnits.push(...subUnits);
      } else {
        refinedUnits.push(unit);
      }
    }

    return refinedUnits;
  }

  /**
   * Functional decomposition
   */
  private decomposeFunctional(
    requirement: DecomposableRequirement,
    _complexity: ComplexityLevel
  ): RequirementUnit[] {
    const units: RequirementUnit[] = [];
    const desc = requirement.description;

    // Split by conjunctions
    const parts = desc.split(/\band\b/i).map((p: string) => p.trim()).filter(Boolean);

    if (parts.length > 1) {
      for (let i = 0; i < parts.length; i++) {
        units.push(this.createUnit(requirement, parts[i], 1, `func-${i + 1}`));
      }
    } else {
      // Identify functional aspects
      const aspects = this.identifyFunctionalAspects(desc);
      for (let i = 0; i < aspects.length; i++) {
        units.push(this.createUnit(requirement, aspects[i], 1, `func-${i + 1}`));
      }
    }

    // If no decomposition possible, return single unit
    if (units.length === 0) {
      units.push(this.createUnit(requirement, desc, 1, 'func-1'));
    }

    return units;
  }

  /**
   * Behavioral decomposition
   */
  private decomposeBehavioral(
    requirement: DecomposableRequirement,
    _complexity: ComplexityLevel
  ): RequirementUnit[] {
    const units: RequirementUnit[] = [];
    
    // Create units for each acceptance criterion
    if (requirement.acceptanceCriteria?.length) {
      for (let i = 0; i < requirement.acceptanceCriteria.length; i++) {
        const criterion = requirement.acceptanceCriteria[i];
        units.push(this.createUnit(
          requirement,
          `Behavior: ${criterion}`,
          1,
          `behav-${i + 1}`
        ));
      }
    } else {
      // Generate behavioral scenarios
      const scenarios = this.generateScenarios(requirement);
      for (let i = 0; i < scenarios.length; i++) {
        units.push(this.createUnit(requirement, scenarios[i], 1, `behav-${i + 1}`));
      }
    }

    return units;
  }

  /**
   * Structural decomposition
   */
  private decomposeStructural(
    requirement: DecomposableRequirement,
    _complexity: ComplexityLevel
  ): RequirementUnit[] {
    const units: RequirementUnit[] = [];
    const components = this.identifyComponents(requirement.description);

    for (let i = 0; i < components.length; i++) {
      const unit = this.createUnit(
        requirement,
        `${components[i]} component implementation`,
        1,
        `struct-${i + 1}`
      );
      unit.component = components[i];
      units.push(unit);
    }

    if (units.length === 0) {
      units.push(this.createUnit(requirement, requirement.description, 1, 'struct-1'));
    }

    return units;
  }

  /**
   * Temporal decomposition
   */
  private decomposeTemporal(
    requirement: DecomposableRequirement,
    _complexity: ComplexityLevel
  ): RequirementUnit[] {
    const phases = ['setup', 'execution', 'validation', 'cleanup'];
    const units: RequirementUnit[] = [];

    for (let i = 0; i < phases.length; i++) {
      const phase = phases[i];
      units.push(this.createUnit(
        requirement,
        `${phase.charAt(0).toUpperCase() + phase.slice(1)} phase: ${requirement.title}`,
        1,
        `temp-${phase}`
      ));
    }

    return units;
  }

  /**
   * Stakeholder-based decomposition
   */
  private decomposeByStakeholder(
    requirement: DecomposableRequirement,
    _complexity: ComplexityLevel
  ): RequirementUnit[] {
    const stakeholders = requirement.stakeholders ?? ['user', 'system', 'admin'];
    const units: RequirementUnit[] = [];

    for (let i = 0; i < stakeholders.length; i++) {
      const stakeholder = stakeholders[i];
      units.push(this.createUnit(
        requirement,
        `${stakeholder} perspective: ${requirement.title}`,
        1,
        `stake-${stakeholder}`
      ));
    }

    return units;
  }

  /**
   * Risk-based decomposition
   */
  private decomposeByRisk(
    requirement: DecomposableRequirement,
    _complexity: ComplexityLevel
  ): RequirementUnit[] {
    const riskAreas = ['core-functionality', 'edge-cases', 'error-handling', 'performance'];
    const units: RequirementUnit[] = [];

    for (let i = 0; i < riskAreas.length; i++) {
      const area = riskAreas[i];
      units.push(this.createUnit(
        requirement,
        `${area.replace(/-/g, ' ')}: ${requirement.title}`,
        1,
        `risk-${area}`
      ));
    }

    return units;
  }

  /**
   * Create a requirement unit
   */
  private createUnit(
    parent: DecomposableRequirement,
    description: string,
    level: number,
    suffix: string
  ): RequirementUnit {
    const id = `${parent.id}-${suffix}`;
    const title = this.generateTitle(description);
    
    const unit: RequirementUnit = {
      id,
      parentId: parent.id,
      title,
      description,
      type: parent.type,
      level,
      testable: this.isTestable(description),
      dependencies: [],
      tags: this.extractTags(description),
      acceptanceCriteria: [],
    };

    // Auto-generate acceptance criteria
    if (this.config.autoAcceptanceCriteria) {
      unit.acceptanceCriteria = this.generateAcceptanceCriteria(description);
    }

    // Auto-estimate effort
    if (this.config.autoEstimate) {
      unit.estimatedEffort = this.estimateEffort(description);
    }

    return unit;
  }

  /**
   * Check if unit should be decomposed more
   */
  private shouldDecomposeMore(unit: RequirementUnit): boolean {
    if (unit.level >= this.config.maxDepth) return false;
    if (unit.estimatedEffort && unit.estimatedEffort <= this.config.targetUnitSize) return false;
    
    // Check complexity of unit
    const complexity = this.analyzeUnitComplexity(unit);
    return complexity === 'high' || complexity === 'very-high';
  }

  /**
   * Analyze unit complexity
   */
  private analyzeUnitComplexity(unit: RequirementUnit): ComplexityLevel {
    const text = `${unit.title} ${unit.description}`.toLowerCase();
    const conjunctions = (text.match(/\band\b/gi) ?? []).length;
    
    if (conjunctions >= 3) return 'very-high';
    if (conjunctions >= 2) return 'high';
    if (conjunctions >= 1) return 'medium';
    return 'low';
  }

  /**
   * Decompose a single unit further
   */
  private decomposeUnit(unit: RequirementUnit, strategy: DecompositionStrategy): RequirementUnit[] {
    const parentReq: DecomposableRequirement = {
      id: unit.id,
      title: unit.title,
      description: unit.description,
      type: unit.type,
      priority: 'should',
    };

    const subUnits = this.performDecomposition(parentReq, strategy, 'medium');
    
    // Update levels and parent IDs
    for (const sub of subUnits) {
      sub.level = unit.level + 1;
      sub.parentId = unit.id;
    }

    return subUnits;
  }

  /**
   * Identify functional aspects
   */
  private identifyFunctionalAspects(description: string): string[] {
    const aspects: string[] = [];
    
    // Look for verb phrases
    const verbPatterns = [
      /(?:must|shall|should|will)\s+(\w+\s+\w+(?:\s+\w+)?)/gi,
      /(?:to|can|able to)\s+(\w+\s+\w+(?:\s+\w+)?)/gi,
    ];

    for (const pattern of verbPatterns) {
      let match;
      while ((match = pattern.exec(description)) !== null) {
        aspects.push(match[1].trim());
      }
    }

    // If no aspects found, split by commas
    if (aspects.length === 0) {
      const commaParts = description.split(',').map((p) => p.trim()).filter((p) => p.length > 10);
      aspects.push(...commaParts);
    }

    return aspects.length > 0 ? aspects : [description];
  }

  /**
   * Generate behavioral scenarios
   */
  private generateScenarios(requirement: DecomposableRequirement): string[] {
    const scenarios: string[] = [];

    // Generate typical scenarios
    scenarios.push(`Given valid input, when ${requirement.title.toLowerCase()}, then operation succeeds`);
    scenarios.push(`Given invalid input, when ${requirement.title.toLowerCase()}, then appropriate error is returned`);
    scenarios.push(`Given edge case, when ${requirement.title.toLowerCase()}, then system handles gracefully`);

    return scenarios;
  }

  /**
   * Identify components from description
   */
  private identifyComponents(description: string): string[] {
    const components: string[] = [];
    
    // Common component keywords
    const componentPatterns = [
      /\b(UI|interface|frontend)\b/gi,
      /\b(API|service|backend)\b/gi,
      /\b(database|storage|persistence)\b/gi,
      /\b(validation|verification)\b/gi,
      /\b(authentication|authorization|security)\b/gi,
      /\b(logging|monitoring|metrics)\b/gi,
    ];

    for (const pattern of componentPatterns) {
      if (pattern.test(description)) {
        const match = description.match(pattern);
        if (match) {
          components.push(match[0].toLowerCase());
        }
      }
    }

    // Use component mapping if available
    if (this.config.componentMapping) {
      for (const [component, keywords] of Object.entries(this.config.componentMapping)) {
        if (keywords.some((k) => description.toLowerCase().includes(k.toLowerCase()))) {
          components.push(component);
        }
      }
    }

    return [...new Set(components)];
  }

  /**
   * Generate title from description
   */
  private generateTitle(description: string): string {
    // Take first sentence or first N words
    const firstSentence = description.split(/[.!?]/)[0];
    const words = firstSentence.split(/\s+/).slice(0, 8);
    return words.join(' ').replace(/[,;:]$/, '');
  }

  /**
   * Check if description is testable
   */
  private isTestable(description: string): boolean {
    const testablePatterns = [
      /\b(must|shall|should|will)\b/i,
      /\b(returns?|produces?|generates?|displays?)\b/i,
      /\b(validates?|verifies?|checks?)\b/i,
      /\b(within|less than|at least|exactly)\b/i,
    ];

    return testablePatterns.some((p) => p.test(description));
  }

  /**
   * Extract tags from description
   */
  private extractTags(description: string): string[] {
    const tags: string[] = [];
    const tagPatterns: Array<[RegExp, string]> = [
      [/\b(security|auth)\b/i, 'security'],
      [/\b(performance|speed|fast)\b/i, 'performance'],
      [/\b(UI|interface|display)\b/i, 'ui'],
      [/\b(API|service|endpoint)\b/i, 'api'],
      [/\b(database|storage|persist)\b/i, 'data'],
      [/\b(validation|verify)\b/i, 'validation'],
      [/\b(error|exception|fail)\b/i, 'error-handling'],
    ];

    for (const [pattern, tag] of tagPatterns) {
      if (pattern.test(description)) {
        tags.push(tag);
      }
    }

    return tags;
  }

  /**
   * Generate acceptance criteria
   */
  private generateAcceptanceCriteria(description: string): string[] {
    const criteria: string[] = [];
    
    // Extract measurable aspects
    if (/\b(must|shall|should)\b/i.test(description)) {
      criteria.push(`Verify that: ${description.replace(/^.*?(must|shall|should)\s*/i, '')}`);
    }

    // Add testability criteria
    if (this.isTestable(description)) {
      criteria.push('Unit tests cover this functionality');
      criteria.push('Integration test validates end-to-end behavior');
    }

    if (criteria.length === 0) {
      criteria.push(`Implementation matches specification: ${description.substring(0, 50)}...`);
    }

    return criteria;
  }

  /**
   * Estimate effort in hours
   */
  private estimateEffort(description: string): number {
    let baseEffort = 2; // Base hours

    // Adjust based on complexity indicators
    const conjunctions = (description.match(/\band\b/gi) ?? []).length;
    baseEffort += conjunctions * 1;

    const conditionals = (description.match(/\bif\b/gi) ?? []).length;
    baseEffort += conditionals * 1.5;

    // Adjust based on keywords
    if (/\bintegrat/i.test(description)) baseEffort += 2;
    if (/\bsecurity|auth/i.test(description)) baseEffort += 2;
    if (/\bperformance/i.test(description)) baseEffort += 1;

    return Math.round(baseEffort * 2) / 2; // Round to 0.5 hours
  }

  /**
   * Build hierarchy tree
   */
  private buildHierarchy(units: RequirementUnit[]): DecompositionNode {
    const rootUnit = units.find((u) => u.level === 1) ?? units[0];
    
    const buildNode = (unit: RequirementUnit): DecompositionNode => {
      const children = units
        .filter((u) => u.parentId === unit.id && u.id !== unit.id)
        .map((u) => buildNode(u));

      return { unit, children };
    };

    return buildNode(rootUnit);
  }

  /**
   * Calculate statistics
   */
  private calculateStats(
    units: RequirementUnit[],
    _hierarchy: DecompositionNode
  ): DecompositionResult['stats'] {
    const depths = units.map((u) => u.level);
    const avgDepth = depths.reduce((a, b) => a + b, 0) / depths.length;
    const maxDepth = Math.max(...depths);

    const totalEffort = units
      .filter((u) => u.estimatedEffort)
      .reduce((sum, u) => sum + (u.estimatedEffort ?? 0), 0);

    return {
      totalUnits: units.length,
      avgDepth,
      maxDepth,
      estimatedTotalEffort: totalEffort > 0 ? totalEffort : undefined,
    };
  }

  /**
   * Generate recommendations
   */
  private generateRecommendations(
    _requirement: DecomposableRequirement,
    units: RequirementUnit[],
    stats: DecompositionResult['stats']
  ): string[] {
    const recommendations: string[] = [];

    // Check unit count
    if (units.length > 10) {
      recommendations.push('Consider grouping related units to reduce complexity');
    }
    if (units.length < 2) {
      recommendations.push('Requirement may need further decomposition');
    }

    // Check testability
    const untestable = units.filter((u) => !u.testable);
    if (untestable.length > 0) {
      recommendations.push(`${untestable.length} unit(s) may need clearer testability criteria`);
    }

    // Check dependencies
    const noDeps = units.filter((u) => u.dependencies.length === 0 && u.level > 1);
    if (noDeps.length > units.length / 2) {
      recommendations.push('Consider identifying dependencies between units');
    }

    // Check effort distribution
    if (stats.estimatedTotalEffort) {
      const avgEffort = stats.estimatedTotalEffort / units.length;
      if (avgEffort > this.config.targetUnitSize * 2) {
        recommendations.push('Units may be too large, consider further decomposition');
      }
    }

    if (recommendations.length === 0) {
      recommendations.push('Decomposition looks well-balanced');
    }

    return recommendations;
  }

  /**
   * Export decomposition as markdown
   */
  exportMarkdown(result: DecompositionResult): string {
    const lines: string[] = [];

    lines.push(`# Decomposition: ${result.original.title}`);
    lines.push('');
    lines.push(`**Strategy:** ${result.strategy}`);
    lines.push(`**Total Units:** ${result.stats.totalUnits}`);
    lines.push(`**Max Depth:** ${result.stats.maxDepth}`);
    if (result.stats.estimatedTotalEffort) {
      lines.push(`**Estimated Total Effort:** ${result.stats.estimatedTotalEffort}h`);
    }
    lines.push('');

    lines.push('## Original Requirement');
    lines.push('');
    lines.push(`> ${result.original.description}`);
    lines.push('');

    lines.push('## Decomposed Units');
    lines.push('');

    const renderUnit = (unit: RequirementUnit, indent: string) => {
      lines.push(`${indent}- **${unit.id}**: ${unit.title}`);
      if (unit.estimatedEffort) {
        lines.push(`${indent}  - Effort: ${unit.estimatedEffort}h`);
      }
      if (unit.acceptanceCriteria.length > 0) {
        lines.push(`${indent}  - Criteria: ${unit.acceptanceCriteria[0]}`);
      }
    };

    const renderNode = (node: DecompositionNode, depth: number) => {
      const indent = '  '.repeat(depth);
      renderUnit(node.unit, indent);
      for (const child of node.children) {
        renderNode(child, depth + 1);
      }
    };

    renderNode(result.hierarchy, 0);
    lines.push('');

    lines.push('## Recommendations');
    lines.push('');
    for (const rec of result.recommendations) {
      lines.push(`- ${rec}`);
    }

    return lines.join('\n');
  }
}

/**
 * Create requirements decomposer instance
 */
export function createRequirementsDecomposer(
  config?: Partial<DecomposerConfig>
): RequirementsDecomposer {
  return new RequirementsDecomposer(config);
}
