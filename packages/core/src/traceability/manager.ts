/**
 * Traceability Manager
 * 
 * Manages bidirectional traceability between requirements, design, and code
 * 
 * @packageDocumentation
 * @module traceability/manager
 * 
 * @see REQ-TRA-001 - Bidirectional Traceability
 * @see Article IV - Traceability Requirements
 */

/**
 * Traceable artifact types
 */
export type ArtifactType =
  | 'requirement'
  | 'design'
  | 'code'
  | 'test'
  | 'task'
  | 'documentation';

/**
 * Trace link types
 */
export type TraceLinkType =
  | 'derives'        // Requirement derives from requirement
  | 'implements'     // Code implements requirement
  | 'satisfies'      // Design satisfies requirement
  | 'verifies'       // Test verifies requirement
  | 'decomposes'     // Decomposes into sub-elements
  | 'relates'        // General relationship
  | 'conflicts';     // Potential conflict

/**
 * Traceable artifact
 */
export interface TraceableArtifact {
  /** Unique identifier */
  id: string;
  /** Artifact type */
  type: ArtifactType;
  /** Display name */
  name: string;
  /** Description */
  description?: string;
  /** Version */
  version?: string;
  /** Status */
  status: ArtifactStatus;
  /** Source file/location */
  source?: {
    file: string;
    line?: number;
    column?: number;
  };
  /** Metadata */
  metadata?: Record<string, unknown>;
  /** Created timestamp */
  createdAt: string;
  /** Updated timestamp */
  updatedAt: string;
}

/**
 * Artifact status
 */
export type ArtifactStatus =
  | 'draft'
  | 'active'
  | 'deprecated'
  | 'deleted';

/**
 * Trace link between artifacts
 */
export interface TraceLink {
  /** Link identifier */
  id: string;
  /** Source artifact ID */
  sourceId: string;
  /** Target artifact ID */
  targetId: string;
  /** Link type */
  type: TraceLinkType;
  /** Confidence score (0-1) */
  confidence: number;
  /** Is manually verified */
  verified: boolean;
  /** Rationale for link */
  rationale?: string;
  /** Created by (user/system) */
  createdBy: string;
  /** Created timestamp */
  createdAt: string;
}

/**
 * Traceability matrix entry
 */
export interface MatrixEntry {
  /** Requirement ID */
  requirementId: string;
  /** Design artifacts */
  designs: string[];
  /** Code artifacts */
  code: string[];
  /** Test artifacts */
  tests: string[];
  /** Coverage score (0-1) */
  coverage: number;
  /** Status */
  status: 'covered' | 'partial' | 'uncovered';
}

/**
 * Traceability gap
 */
export interface TraceabilityGap {
  /** Artifact with gap */
  artifactId: string;
  /** Gap type */
  gapType: 'no-parent' | 'no-child' | 'no-test' | 'no-impl';
  /** Severity */
  severity: 'high' | 'medium' | 'low';
  /** Description */
  description: string;
  /** Suggestions */
  suggestions: string[];
}

/**
 * Traceability report
 */
export interface TraceabilityReport {
  /** Generated timestamp */
  generatedAt: string;
  /** Total artifacts */
  totalArtifacts: number;
  /** Total links */
  totalLinks: number;
  /** Coverage statistics */
  coverage: {
    requirements: CoverageStats;
    designs: CoverageStats;
    code: CoverageStats;
    tests: CoverageStats;
  };
  /** Identified gaps */
  gaps: TraceabilityGap[];
  /** Matrix (requirements view) */
  matrix: MatrixEntry[];
}

/**
 * Coverage statistics
 */
export interface CoverageStats {
  /** Total items */
  total: number;
  /** Covered items */
  covered: number;
  /** Partial items */
  partial: number;
  /** Uncovered items */
  uncovered: number;
  /** Coverage percentage */
  percentage: number;
}

/**
 * Traceability Manager configuration
 */
export interface TraceabilityConfig {
  /** Auto-detect links from code comments */
  autoDetect: boolean;
  /** Minimum confidence for auto-detected links */
  autoDetectThreshold: number;
  /** Require verification for links */
  requireVerification: boolean;
  /** Gap detection severity levels */
  gapSeverity: {
    noParent: 'high' | 'medium' | 'low';
    noChild: 'high' | 'medium' | 'low';
    noTest: 'high' | 'medium' | 'low';
    noImpl: 'high' | 'medium' | 'low';
  };
}

/**
 * Default configuration
 */
export const DEFAULT_TRACEABILITY_CONFIG: TraceabilityConfig = {
  autoDetect: true,
  autoDetectThreshold: 0.7,
  requireVerification: false,
  gapSeverity: {
    noParent: 'low',
    noChild: 'medium',
    noTest: 'high',
    noImpl: 'high',
  },
};

/**
 * Traceability Manager
 * 
 * Manages artifacts and their trace links
 */
export class TraceabilityManager {
  private config: TraceabilityConfig;
  private artifacts = new Map<string, TraceableArtifact>();
  private links = new Map<string, TraceLink>();
  private artifactsByType = new Map<ArtifactType, Set<string>>();

  constructor(config?: Partial<TraceabilityConfig>) {
    this.config = { ...DEFAULT_TRACEABILITY_CONFIG, ...config };
    
    // Initialize type index
    const types: ArtifactType[] = ['requirement', 'design', 'code', 'test', 'task', 'documentation'];
    for (const type of types) {
      this.artifactsByType.set(type, new Set());
    }
  }

  /**
   * Register an artifact
   */
  registerArtifact(artifact: TraceableArtifact): void {
    this.artifacts.set(artifact.id, artifact);
    this.artifactsByType.get(artifact.type)?.add(artifact.id);
  }

  /**
   * Register multiple artifacts
   */
  registerArtifacts(artifacts: TraceableArtifact[]): void {
    for (const artifact of artifacts) {
      this.registerArtifact(artifact);
    }
  }

  /**
   * Get artifact by ID
   */
  getArtifact(id: string): TraceableArtifact | undefined {
    return this.artifacts.get(id);
  }

  /**
   * Get artifacts by type
   */
  getArtifactsByType(type: ArtifactType): TraceableArtifact[] {
    const ids = this.artifactsByType.get(type) ?? new Set();
    return Array.from(ids)
      .map((id) => this.artifacts.get(id))
      .filter((a): a is TraceableArtifact => a !== undefined);
  }

  /**
   * Create a trace link
   */
  createLink(
    sourceId: string,
    targetId: string,
    type: TraceLinkType,
    options?: {
      confidence?: number;
      rationale?: string;
      createdBy?: string;
      verified?: boolean;
    }
  ): TraceLink {
    const source = this.artifacts.get(sourceId);
    const target = this.artifacts.get(targetId);

    if (!source) {
      throw new Error(`Source artifact not found: ${sourceId}`);
    }
    if (!target) {
      throw new Error(`Target artifact not found: ${targetId}`);
    }

    const link: TraceLink = {
      id: `${sourceId}-${type}-${targetId}`,
      sourceId,
      targetId,
      type,
      confidence: options?.confidence ?? 1.0,
      verified: options?.verified ?? !this.config.requireVerification,
      rationale: options?.rationale,
      createdBy: options?.createdBy ?? 'system',
      createdAt: new Date().toISOString(),
    };

    this.links.set(link.id, link);
    return link;
  }

  /**
   * Get links from an artifact
   */
  getLinksFrom(artifactId: string): TraceLink[] {
    return Array.from(this.links.values())
      .filter((link) => link.sourceId === artifactId);
  }

  /**
   * Get links to an artifact
   */
  getLinksTo(artifactId: string): TraceLink[] {
    return Array.from(this.links.values())
      .filter((link) => link.targetId === artifactId);
  }

  /**
   * Get all links for an artifact (both directions)
   */
  getAllLinks(artifactId: string): TraceLink[] {
    return Array.from(this.links.values())
      .filter((link) => link.sourceId === artifactId || link.targetId === artifactId);
  }

  /**
   * Find path between two artifacts
   */
  findPath(
    fromId: string,
    toId: string,
    maxDepth: number = 5
  ): string[] | null {
    const visited = new Set<string>();
    const queue: Array<{ id: string; path: string[] }> = [
      { id: fromId, path: [fromId] },
    ];

    while (queue.length > 0) {
      const { id, path } = queue.shift()!;

      if (id === toId) {
        return path;
      }

      if (path.length >= maxDepth || visited.has(id)) {
        continue;
      }

      visited.add(id);

      // Get connected artifacts
      const links = this.getAllLinks(id);
      for (const link of links) {
        const nextId = link.sourceId === id ? link.targetId : link.sourceId;
        if (!visited.has(nextId)) {
          queue.push({ id: nextId, path: [...path, nextId] });
        }
      }
    }

    return null;
  }

  /**
   * Get downstream artifacts (artifacts that depend on this one)
   */
  getDownstream(artifactId: string): TraceableArtifact[] {
    const downstream = new Set<string>();
    const queue = [artifactId];

    while (queue.length > 0) {
      const current = queue.shift()!;
      const links = this.getLinksFrom(current);
      
      for (const link of links) {
        if (!downstream.has(link.targetId)) {
          downstream.add(link.targetId);
          queue.push(link.targetId);
        }
      }
    }

    return Array.from(downstream)
      .map((id) => this.artifacts.get(id))
      .filter((a): a is TraceableArtifact => a !== undefined);
  }

  /**
   * Get upstream artifacts (artifacts this one depends on)
   */
  getUpstream(artifactId: string): TraceableArtifact[] {
    const upstream = new Set<string>();
    const queue = [artifactId];

    while (queue.length > 0) {
      const current = queue.shift()!;
      const links = this.getLinksTo(current);
      
      for (const link of links) {
        if (!upstream.has(link.sourceId)) {
          upstream.add(link.sourceId);
          queue.push(link.sourceId);
        }
      }
    }

    return Array.from(upstream)
      .map((id) => this.artifacts.get(id))
      .filter((a): a is TraceableArtifact => a !== undefined);
  }

  /**
   * Generate traceability matrix
   */
  generateMatrix(): MatrixEntry[] {
    const requirements = this.getArtifactsByType('requirement');
    const matrix: MatrixEntry[] = [];

    for (const req of requirements) {
      const downstream = this.getDownstream(req.id);
      
      const designs = downstream
        .filter((a) => a.type === 'design')
        .map((a) => a.id);
      
      const code = downstream
        .filter((a) => a.type === 'code')
        .map((a) => a.id);
      
      const tests = downstream
        .filter((a) => a.type === 'test')
        .map((a) => a.id);

      // Calculate coverage
      let coverage = 0;
      if (designs.length > 0) coverage += 0.3;
      if (code.length > 0) coverage += 0.4;
      if (tests.length > 0) coverage += 0.3;

      matrix.push({
        requirementId: req.id,
        designs,
        code,
        tests,
        coverage,
        status: coverage >= 0.9 ? 'covered' : coverage > 0 ? 'partial' : 'uncovered',
      });
    }

    return matrix;
  }

  /**
   * Detect traceability gaps
   */
  detectGaps(): TraceabilityGap[] {
    const gaps: TraceabilityGap[] = [];

    // Check requirements
    for (const req of this.getArtifactsByType('requirement')) {
      // No downstream links
      if (this.getLinksFrom(req.id).length === 0) {
        gaps.push({
          artifactId: req.id,
          gapType: 'no-child',
          severity: this.config.gapSeverity.noChild,
          description: `Requirement ${req.id} has no implementing artifacts`,
          suggestions: [
            'Create design elements that satisfy this requirement',
            'Link existing design or code to this requirement',
          ],
        });
      }

      // No test coverage
      const downstream = this.getDownstream(req.id);
      const hasTest = downstream.some((a) => a.type === 'test');
      if (!hasTest) {
        gaps.push({
          artifactId: req.id,
          gapType: 'no-test',
          severity: this.config.gapSeverity.noTest,
          description: `Requirement ${req.id} has no test coverage`,
          suggestions: [
            'Create tests that verify this requirement',
            'Link existing tests to this requirement chain',
          ],
        });
      }
    }

    // Check code artifacts
    for (const code of this.getArtifactsByType('code')) {
      const upstream = this.getLinksTo(code.id);
      if (upstream.length === 0) {
        gaps.push({
          artifactId: code.id,
          gapType: 'no-parent',
          severity: this.config.gapSeverity.noParent,
          description: `Code ${code.id} is not linked to any requirement`,
          suggestions: [
            'Link this code to a requirement it implements',
            'Create a requirement for this functionality',
          ],
        });
      }
    }

    // Check designs without implementation
    for (const design of this.getArtifactsByType('design')) {
      const downstream = this.getDownstream(design.id);
      const hasImpl = downstream.some((a) => a.type === 'code');
      if (!hasImpl) {
        gaps.push({
          artifactId: design.id,
          gapType: 'no-impl',
          severity: this.config.gapSeverity.noImpl,
          description: `Design ${design.id} has no implementation`,
          suggestions: [
            'Implement this design in code',
            'Link existing code to this design',
          ],
        });
      }
    }

    return gaps;
  }

  /**
   * Generate traceability report
   */
  generateReport(): TraceabilityReport {
    const matrix = this.generateMatrix();
    const gaps = this.detectGaps();

    const calculateStats = (type: ArtifactType): CoverageStats => {
      const artifacts = this.getArtifactsByType(type);
      let covered = 0;
      let partial = 0;

      for (const artifact of artifacts) {
        const links = this.getAllLinks(artifact.id);
        if (links.length > 1) {
          covered++;
        } else if (links.length === 1) {
          partial++;
        }
      }

      const total = artifacts.length;
      return {
        total,
        covered,
        partial,
        uncovered: total - covered - partial,
        percentage: total > 0 ? ((covered + partial * 0.5) / total) * 100 : 0,
      };
    };

    return {
      generatedAt: new Date().toISOString(),
      totalArtifacts: this.artifacts.size,
      totalLinks: this.links.size,
      coverage: {
        requirements: calculateStats('requirement'),
        designs: calculateStats('design'),
        code: calculateStats('code'),
        tests: calculateStats('test'),
      },
      gaps,
      matrix,
    };
  }

  /**
   * Auto-detect links from code annotations
   */
  autoDetectLinks(
    codeContent: string,
    codeArtifactId: string
  ): TraceLink[] {
    if (!this.config.autoDetect) {
      return [];
    }

    const detectedLinks: TraceLink[] = [];

    // Pattern: @see REQ-XXX, @implements REQ-XXX, @satisfies DES-XXX
    const patterns = [
      { regex: /@see\s+(REQ-\w+)/gi, type: 'relates' as TraceLinkType },
      { regex: /@implements\s+(REQ-\w+)/gi, type: 'implements' as TraceLinkType },
      { regex: /@satisfies\s+(DES-\w+)/gi, type: 'satisfies' as TraceLinkType },
      { regex: /@verifies\s+(REQ-\w+)/gi, type: 'verifies' as TraceLinkType },
    ];

    for (const { regex, type } of patterns) {
      let match;
      while ((match = regex.exec(codeContent)) !== null) {
        const targetId = match[1];
        if (this.artifacts.has(targetId)) {
          try {
            const link = this.createLink(codeArtifactId, targetId, type, {
              confidence: this.config.autoDetectThreshold,
              rationale: 'Auto-detected from code annotation',
              createdBy: 'auto-detect',
              verified: false,
            });
            detectedLinks.push(link);
          } catch {
            // Link creation failed (e.g., duplicate)
          }
        }
      }
    }

    return detectedLinks;
  }

  /**
   * Export to JSON
   */
  toJSON(): {
    artifacts: TraceableArtifact[];
    links: TraceLink[];
  } {
    return {
      artifacts: Array.from(this.artifacts.values()),
      links: Array.from(this.links.values()),
    };
  }

  /**
   * Import from JSON
   */
  fromJSON(data: {
    artifacts: TraceableArtifact[];
    links: TraceLink[];
  }): void {
    for (const artifact of data.artifacts) {
      this.registerArtifact(artifact);
    }
    for (const link of data.links) {
      this.links.set(link.id, link);
    }
  }

  /**
   * Clear all data
   */
  clear(): void {
    this.artifacts.clear();
    this.links.clear();
    for (const set of this.artifactsByType.values()) {
      set.clear();
    }
  }
}

/**
 * Create traceability manager instance
 */
export function createTraceabilityManager(
  config?: Partial<TraceabilityConfig>
): TraceabilityManager {
  return new TraceabilityManager(config);
}
