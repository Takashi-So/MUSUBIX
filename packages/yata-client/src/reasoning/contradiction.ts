/**
 * Contradiction Detector
 * 
 * Detects and resolves contradictions between knowledge sources
 * 
 * @packageDocumentation
 * @module reasoning/contradiction
 * 
 * @see REQ-NS-101 - Symbolic Reasoning
 * @see REQ-NS-104 - Contradiction Detection
 */

import type { KnowledgeNode, KnowledgeEdge } from '../types.js';

/**
 * Contradiction types
 */
export type ContradictionType =
  | 'logical'         // Direct logical contradiction (A and NOT A)
  | 'temporal'        // Timeline inconsistency
  | 'cardinality'     // Constraint violations
  | 'semantic'        // Meaning conflicts
  | 'structural'      // Architecture conflicts
  | 'requirement'     // Requirement conflicts
  | 'priority';       // Priority ordering conflicts

/**
 * Contradiction severity levels
 */
export type ContradictionSeverity = 'critical' | 'high' | 'medium' | 'low';

/**
 * Detected contradiction
 */
export interface Contradiction {
  /** Unique ID */
  id: string;
  /** Contradiction type */
  type: ContradictionType;
  /** Severity level */
  severity: ContradictionSeverity;
  /** Description */
  description: string;
  /** First conflicting element */
  element1: ConflictingElement;
  /** Second conflicting element */
  element2: ConflictingElement;
  /** Suggested resolutions */
  resolutions: Resolution[];
  /** Detected timestamp */
  detectedAt: number;
  /** Confidence in detection */
  confidence: number;
}

/**
 * Conflicting element
 */
export interface ConflictingElement {
  /** Element ID */
  id: string;
  /** Element type */
  type: string;
  /** Element content/value */
  content: string;
  /** Source document/location */
  source: string;
  /** Priority if applicable */
  priority?: number;
  /** Timestamp */
  timestamp?: number;
}

/**
 * Resolution suggestion
 */
export interface Resolution {
  /** Resolution ID */
  id: string;
  /** Resolution strategy */
  strategy: ResolutionStrategy;
  /** Description */
  description: string;
  /** Which element to prefer */
  preferElement?: 'element1' | 'element2' | 'neither' | 'merge';
  /** Confidence this will resolve */
  confidence: number;
  /** Side effects of resolution */
  sideEffects?: string[];
}

/**
 * Resolution strategies
 */
export type ResolutionStrategy =
  | 'prefer-newer'        // Use most recent
  | 'prefer-higher-priority'
  | 'prefer-more-specific'
  | 'merge-both'
  | 'escalate-to-user'
  | 'invalidate-both'
  | 'use-knowledge-graph'
  | 'majority-vote';

/**
 * Detection rule
 */
export interface DetectionRule {
  /** Rule ID */
  id: string;
  /** Rule name */
  name: string;
  /** Contradiction types this rule detects */
  types: ContradictionType[];
  /** Detection function */
  detect: (
    nodes: KnowledgeNode[],
    edges: KnowledgeEdge[],
    context: DetectionContext
  ) => Contradiction[];
}

/**
 * Detection context
 */
export interface DetectionContext {
  /** Current timestamp */
  now: number;
  /** Configuration */
  config: ContradictionDetectorConfig;
  /** Helper functions */
  helpers: DetectionHelpers;
}

/**
 * Detection helpers
 */
export interface DetectionHelpers {
  /** Generate unique ID */
  generateId: () => string;
  /** Calculate semantic similarity */
  semanticSimilarity: (text1: string, text2: string) => number;
  /** Parse requirement pattern */
  parseRequirement: (text: string) => RequirementParts | null;
}

/**
 * Parsed requirement parts
 */
export interface RequirementParts {
  condition?: string;
  subject: string;
  action: string;
  object?: string;
  constraint?: string;
}

/**
 * Detector configuration
 */
export interface ContradictionDetectorConfig {
  /** Enabled detection types */
  enabledTypes: ContradictionType[];
  /** Semantic similarity threshold */
  similarityThreshold: number;
  /** Minimum confidence to report */
  minimumConfidence: number;
  /** Maximum results */
  maxResults: number;
  /** Enable auto-resolution */
  autoResolve: boolean;
  /** Default resolution strategy */
  defaultStrategy: ResolutionStrategy;
}

/**
 * Default configuration
 */
export const DEFAULT_DETECTOR_CONFIG: ContradictionDetectorConfig = {
  enabledTypes: ['logical', 'requirement', 'structural', 'semantic'],
  similarityThreshold: 0.7,
  minimumConfidence: 0.6,
  maxResults: 50,
  autoResolve: false,
  defaultStrategy: 'escalate-to-user',
};

/**
 * Detection report
 */
export interface DetectionReport {
  /** Detection timestamp */
  timestamp: number;
  /** Total contradictions found */
  totalFound: number;
  /** Contradictions by type */
  byType: Record<ContradictionType, number>;
  /** Contradictions by severity */
  bySeverity: Record<ContradictionSeverity, number>;
  /** Contradictions list */
  contradictions: Contradiction[];
  /** Auto-resolved count */
  autoResolved: number;
}

/**
 * Contradiction Detector
 * 
 * Detects contradictions in knowledge and requirements
 */
export class ContradictionDetector {
  private config: ContradictionDetectorConfig;
  private rules: Map<string, DetectionRule> = new Map();
  private idCounter = 0;

  constructor(config?: Partial<ContradictionDetectorConfig>) {
    this.config = { ...DEFAULT_DETECTOR_CONFIG, ...config };
    this.initializeBuiltinRules();
  }

  /**
   * Initialize built-in detection rules
   */
  private initializeBuiltinRules(): void {
    // Logical contradiction rule
    this.addRule({
      id: 'logical-negation',
      name: 'Logical Negation',
      types: ['logical'],
      detect: (nodes, _edges, ctx) => {
        const contradictions: Contradiction[] = [];
        const statements = nodes.filter((n) => n.type === 'statement' || n.type === 'requirement');

        for (let i = 0; i < statements.length; i++) {
          for (let j = i + 1; j < statements.length; j++) {
            const s1 = statements[i];
            const s2 = statements[j];

            // Check for direct negation patterns
            if (this.isNegation(s1.properties.text as string, s2.properties.text as string)) {
              contradictions.push({
                id: ctx.helpers.generateId(),
                type: 'logical',
                severity: 'critical',
                description: 'Direct logical contradiction detected',
                element1: this.nodeToElement(s1),
                element2: this.nodeToElement(s2),
                resolutions: this.generateResolutions('logical', s1, s2),
                detectedAt: ctx.now,
                confidence: 0.95,
              });
            }
          }
        }

        return contradictions;
      },
    });

    // Requirement conflict rule
    this.addRule({
      id: 'requirement-conflict',
      name: 'Requirement Conflict',
      types: ['requirement'],
      detect: (nodes, _edges, ctx) => {
        const contradictions: Contradiction[] = [];
        const requirements = nodes.filter((n) => n.type === 'requirement');

        for (let i = 0; i < requirements.length; i++) {
          for (let j = i + 1; j < requirements.length; j++) {
            const r1 = requirements[i];
            const r2 = requirements[j];

            const text1 = r1.properties.text as string;
            const text2 = r2.properties.text as string;

            // Check for conflicting actions on same subject
            const parts1 = ctx.helpers.parseRequirement(text1);
            const parts2 = ctx.helpers.parseRequirement(text2);

            if (parts1 && parts2 && parts1.subject === parts2.subject) {
              if (this.actionsConflict(parts1.action, parts2.action)) {
                contradictions.push({
                  id: ctx.helpers.generateId(),
                  type: 'requirement',
                  severity: 'high',
                  description: `Requirements specify conflicting actions for "${parts1.subject}"`,
                  element1: this.nodeToElement(r1),
                  element2: this.nodeToElement(r2),
                  resolutions: this.generateResolutions('requirement', r1, r2),
                  detectedAt: ctx.now,
                  confidence: 0.85,
                });
              }
            }
          }
        }

        return contradictions;
      },
    });

    // Priority conflict rule
    this.addRule({
      id: 'priority-conflict',
      name: 'Priority Conflict',
      types: ['priority'],
      detect: (nodes, edges, ctx) => {
        const contradictions: Contradiction[] = [];

        // Find dependency edges
        const dependencies = edges.filter((e) => e.type === 'depends-on');

        for (const dep of dependencies) {
          const source = nodes.find((n) => n.id === dep.sourceId);
          const target = nodes.find((n) => n.id === dep.targetId);

          if (source && target) {
            const sourcePriority = (source.properties.priority as number) ?? 0;
            const targetPriority = (target.properties.priority as number) ?? 0;

            // Higher priority depending on lower priority is suspicious
            if (sourcePriority < targetPriority) {
              contradictions.push({
                id: ctx.helpers.generateId(),
                type: 'priority',
                severity: 'medium',
                description: 'High-priority item depends on lower-priority item',
                element1: this.nodeToElement(source),
                element2: this.nodeToElement(target),
                resolutions: [
                  {
                    id: ctx.helpers.generateId(),
                    strategy: 'prefer-higher-priority',
                    description: 'Elevate priority of dependency',
                    confidence: 0.7,
                  },
                ],
                detectedAt: ctx.now,
                confidence: 0.75,
              });
            }
          }
        }

        return contradictions;
      },
    });

    // Temporal conflict rule
    this.addRule({
      id: 'temporal-conflict',
      name: 'Temporal Conflict',
      types: ['temporal'],
      detect: (nodes, edges, ctx) => {
        const contradictions: Contradiction[] = [];

        // Find before/after edges
        const temporalEdges = edges.filter(
          (e) => e.type === 'before' || e.type === 'after' || e.type === 'during'
        );

        // Build temporal graph and check for cycles
        const cycles = this.findTemporalCycles(nodes, temporalEdges);

        for (const cycle of cycles) {
          if (cycle.length >= 2) {
            const first = nodes.find((n) => n.id === cycle[0]);
            const last = nodes.find((n) => n.id === cycle[cycle.length - 1]);

            if (first && last) {
              contradictions.push({
                id: ctx.helpers.generateId(),
                type: 'temporal',
                severity: 'high',
                description: `Temporal cycle detected involving ${cycle.length} items`,
                element1: this.nodeToElement(first),
                element2: this.nodeToElement(last),
                resolutions: [
                  {
                    id: ctx.helpers.generateId(),
                    strategy: 'escalate-to-user',
                    description: 'Review temporal relationships',
                    confidence: 0.6,
                  },
                ],
                detectedAt: ctx.now,
                confidence: 0.9,
              });
            }
          }
        }

        return contradictions;
      },
    });
  }

  /**
   * Add detection rule
   */
  addRule(rule: DetectionRule): void {
    this.rules.set(rule.id, rule);
  }

  /**
   * Remove detection rule
   */
  removeRule(ruleId: string): boolean {
    return this.rules.delete(ruleId);
  }

  /**
   * Detect contradictions in knowledge
   */
  detect(
    nodes: KnowledgeNode[],
    edges: KnowledgeEdge[]
  ): DetectionReport {
    const now = Date.now();
    const allContradictions: Contradiction[] = [];

    const context: DetectionContext = {
      now,
      config: this.config,
      helpers: {
        generateId: () => `contra-${++this.idCounter}`,
        semanticSimilarity: this.semanticSimilarity.bind(this),
        parseRequirement: this.parseRequirement.bind(this),
      },
    };

    // Run all enabled rules
    for (const rule of this.rules.values()) {
      const isEnabled = rule.types.some((t) =>
        this.config.enabledTypes.includes(t)
      );

      if (isEnabled) {
        const found = rule.detect(nodes, edges, context);
        allContradictions.push(...found);
      }
    }

    // Filter by confidence
    const filtered = allContradictions
      .filter((c) => c.confidence >= this.config.minimumConfidence)
      .slice(0, this.config.maxResults);

    // Auto-resolve if enabled
    let autoResolved = 0;
    if (this.config.autoResolve) {
      autoResolved = this.autoResolve(filtered);
    }

    // Build report
    const report: DetectionReport = {
      timestamp: now,
      totalFound: filtered.length,
      byType: this.countByType(filtered),
      bySeverity: this.countBySeverity(filtered),
      contradictions: filtered,
      autoResolved,
    };

    return report;
  }

  /**
   * Check if one statement negates another
   */
  private isNegation(text1: string, text2: string): boolean {
    const negationPatterns = [
      [/shall/, /shall not/],
      [/must/, /must not/],
      [/will/, /will not/],
      [/can/, /cannot/],
      [/is/, /is not/],
      [/are/, /are not/],
      [/enable/, /disable/],
      [/allow/, /deny|prevent/],
      [/require/, /prohibit/],
    ];

    const lower1 = text1.toLowerCase();
    const lower2 = text2.toLowerCase();

    for (const [pos, neg] of negationPatterns) {
      if (
        (pos.test(lower1) && neg.test(lower2)) ||
        (neg.test(lower1) && pos.test(lower2))
      ) {
        // Check if they're about the same thing
        const sim = this.semanticSimilarity(
          lower1.replace(pos, '').replace(neg, ''),
          lower2.replace(pos, '').replace(neg, '')
        );
        if (sim > this.config.similarityThreshold) {
          return true;
        }
      }
    }

    return false;
  }

  /**
   * Check if actions conflict
   */
  private actionsConflict(action1: string, action2: string): boolean {
    const conflictPairs = [
      ['encrypt', 'store in plaintext'],
      ['allow', 'deny'],
      ['enable', 'disable'],
      ['require', 'make optional'],
      ['synchronous', 'asynchronous'],
      ['block', 'allow'],
    ];

    const lower1 = action1.toLowerCase();
    const lower2 = action2.toLowerCase();

    for (const [a, b] of conflictPairs) {
      if (
        (lower1.includes(a) && lower2.includes(b)) ||
        (lower1.includes(b) && lower2.includes(a))
      ) {
        return true;
      }
    }

    return false;
  }

  /**
   * Simple semantic similarity (Jaccard-like)
   */
  private semanticSimilarity(text1: string, text2: string): number {
    const words1 = new Set(text1.toLowerCase().split(/\W+/).filter(Boolean));
    const words2 = new Set(text2.toLowerCase().split(/\W+/).filter(Boolean));

    const intersection = new Set([...words1].filter((w) => words2.has(w)));
    const union = new Set([...words1, ...words2]);

    return intersection.size / union.size;
  }

  /**
   * Parse EARS requirement
   */
  private parseRequirement(text: string): RequirementParts | null {
    // Simple EARS pattern matching
    const patterns = [
      // Event-driven: When X, the system shall Y
      /when\s+(.+?),\s*the\s+(.+?)\s+shall\s+(.+)/i,
      // State-driven: While X, the system shall Y
      /while\s+(.+?),\s*the\s+(.+?)\s+shall\s+(.+)/i,
      // Ubiquitous: The system shall Y
      /the\s+(.+?)\s+shall\s+(.+)/i,
    ];

    for (const pattern of patterns) {
      const match = text.match(pattern);
      if (match) {
        if (match.length === 4) {
          return {
            condition: match[1],
            subject: match[2],
            action: match[3],
          };
        } else if (match.length === 3) {
          return {
            subject: match[1],
            action: match[2],
          };
        }
      }
    }

    return null;
  }

  /**
   * Find temporal cycles using DFS
   */
  private findTemporalCycles(
    nodes: KnowledgeNode[],
    edges: KnowledgeEdge[]
  ): string[][] {
    const cycles: string[][] = [];
    const visited = new Set<string>();
    const path: string[] = [];
    const pathSet = new Set<string>();

    const dfs = (nodeId: string): void => {
      if (pathSet.has(nodeId)) {
        // Found cycle
        const cycleStart = path.indexOf(nodeId);
        cycles.push(path.slice(cycleStart));
        return;
      }

      if (visited.has(nodeId)) return;

      visited.add(nodeId);
      path.push(nodeId);
      pathSet.add(nodeId);

      // Find outgoing edges
      const outgoing = edges.filter((e) => e.sourceId === nodeId);
      for (const edge of outgoing) {
        dfs(edge.targetId);
      }

      path.pop();
      pathSet.delete(nodeId);
    };

    for (const node of nodes) {
      dfs(node.id);
    }

    return cycles;
  }

  /**
   * Convert node to conflicting element
   */
  private nodeToElement(node: KnowledgeNode): ConflictingElement {
    return {
      id: node.id,
      type: node.type,
      content: (node.properties.text as string) ?? JSON.stringify(node.properties),
      source: (node.properties.source as string) ?? 'unknown',
      priority: node.properties.priority as number | undefined,
    };
  }

  /**
   * Generate resolution suggestions
   */
  private generateResolutions(
    type: ContradictionType,
    node1: KnowledgeNode,
    node2: KnowledgeNode
  ): Resolution[] {
    const resolutions: Resolution[] = [];
    const idGen = () => `res-${++this.idCounter}`;

    // Time-based resolution
    const time1 = node1.properties.timestamp as number | undefined;
    const time2 = node2.properties.timestamp as number | undefined;
    if (time1 && time2) {
      resolutions.push({
        id: idGen(),
        strategy: 'prefer-newer',
        description: 'Use the more recently updated version',
        preferElement: time1 > time2 ? 'element1' : 'element2',
        confidence: 0.7,
      });
    }

    // Priority-based resolution
    const prio1 = node1.properties.priority as number | undefined;
    const prio2 = node2.properties.priority as number | undefined;
    if (prio1 !== undefined && prio2 !== undefined && prio1 !== prio2) {
      resolutions.push({
        id: idGen(),
        strategy: 'prefer-higher-priority',
        description: 'Use the higher priority item',
        preferElement: prio1 < prio2 ? 'element1' : 'element2',
        confidence: 0.8,
      });
    }

    // Merge if possible
    if (type === 'semantic' || type === 'requirement') {
      resolutions.push({
        id: idGen(),
        strategy: 'merge-both',
        description: 'Merge both items into a unified version',
        preferElement: 'merge',
        confidence: 0.6,
      });
    }

    // Always offer escalation
    resolutions.push({
      id: idGen(),
      strategy: 'escalate-to-user',
      description: 'Request user decision',
      confidence: 1.0,
    });

    return resolutions;
  }

  /**
   * Auto-resolve contradictions
   */
  private autoResolve(contradictions: Contradiction[]): number {
    let resolved = 0;

    for (const contradiction of contradictions) {
      const bestResolution = contradiction.resolutions.find(
        (r) => r.strategy === this.config.defaultStrategy
      );

      if (bestResolution && bestResolution.confidence >= 0.8) {
        // Mark as auto-resolved (in real impl would update knowledge graph)
        resolved++;
      }
    }

    return resolved;
  }

  /**
   * Count contradictions by type
   */
  private countByType(
    contradictions: Contradiction[]
  ): Record<ContradictionType, number> {
    const counts: Record<ContradictionType, number> = {
      logical: 0,
      temporal: 0,
      cardinality: 0,
      semantic: 0,
      structural: 0,
      requirement: 0,
      priority: 0,
    };

    for (const c of contradictions) {
      counts[c.type]++;
    }

    return counts;
  }

  /**
   * Count contradictions by severity
   */
  private countBySeverity(
    contradictions: Contradiction[]
  ): Record<ContradictionSeverity, number> {
    const counts: Record<ContradictionSeverity, number> = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
    };

    for (const c of contradictions) {
      counts[c.severity]++;
    }

    return counts;
  }
}

/**
 * Create contradiction detector instance
 */
export function createContradictionDetector(
  config?: Partial<ContradictionDetectorConfig>
): ContradictionDetector {
  return new ContradictionDetector(config);
}
