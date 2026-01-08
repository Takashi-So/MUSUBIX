/**
 * EnhancedVersionSpace - Extended Version Space Algebra
 * @module @nahisaho/musubix-synthesis
 * @see TSK-SY-102
 * @see DES-SY-102
 * @see REQ-SYN-002
 *
 * Version Space Algebra拡張による効率的な仮説空間管理
 * - 信頼度ベースのポイント管理
 * - 複数のマージ戦略（intersection, union）
 * - 圧縮・折りたたみ機能
 * - 遅延評価サポート
 */

// =============================================================================
// Types
// =============================================================================

/**
 * Merge strategy for version spaces
 */
export type MergeStrategy = 'intersection' | 'union';

/**
 * Version space configuration
 */
export interface VersionSpaceConfig {
  /** Maximum number of points */
  maxPoints?: number;
  /** Enable compression of similar points */
  enableCompression?: boolean;
  /** Default merge strategy */
  mergeStrategy?: MergeStrategy;
  /** Enable lazy evaluation */
  enableLazyEvaluation?: boolean;
}

/**
 * Input/output example
 */
export interface Example {
  input: unknown;
  output: unknown;
}

/**
 * A point in the version space
 */
export interface VersionSpacePoint {
  /** Unique identifier */
  id: string;
  /** Program representation */
  program: string;
  /** Examples this program satisfies */
  examples: Example[];
  /** Is the program consistent with all examples? */
  consistent: boolean;
  /** Confidence score (0-1) */
  confidence: number;
  /** Optional: program AST or structured representation */
  ast?: unknown;
  /** Optional: metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Statistics about the version space
 */
export interface VersionSpaceStatistics {
  /** Total number of points */
  totalPoints: number;
  /** Number of consistent points */
  consistentPoints: number;
  /** Number of merge operations performed */
  mergeCount: number;
  /** Number of collapse operations */
  collapseCount: number;
  /** Average confidence score */
  averageConfidence: number;
  /** Highest confidence score */
  maxConfidence: number;
  /** Lowest confidence score */
  minConfidence: number;
}

/**
 * EnhancedVersionSpace interface
 */
export interface EnhancedVersionSpace {
  /**
   * Add a point to the version space
   */
  add(point: VersionSpacePoint): boolean;

  /**
   * Get a point by id
   */
  get(id: string): VersionSpacePoint | undefined;

  /**
   * Remove a point by id
   */
  remove(id: string): boolean;

  /**
   * Get the number of points
   */
  size(): number;

  /**
   * Merge with another version space
   */
  merge(
    other: EnhancedVersionSpace,
    strategy?: MergeStrategy
  ): EnhancedVersionSpace;

  /**
   * Collapse similar points
   */
  collapse(): number;

  /**
   * Filter points by minimum confidence
   */
  filterByConfidence(minConfidence: number): VersionSpacePoint[];

  /**
   * Get the best (highest confidence) program
   */
  getBestProgram(): VersionSpacePoint | undefined;

  /**
   * Get all programs sorted by confidence
   */
  getAllPrograms(): VersionSpacePoint[];

  /**
   * Get statistics
   */
  getStatistics(): VersionSpaceStatistics;

  /**
   * Clear all points
   */
  clear(): void;

  /**
   * Clone the version space
   */
  clone(): EnhancedVersionSpace;

  /**
   * Serialize to JSON
   */
  toJSON(): string;

  /**
   * Restore from JSON
   */
  fromJSON(json: string): void;
}

// =============================================================================
// Default Implementation
// =============================================================================

/**
 * Default implementation of EnhancedVersionSpace
 */
class DefaultEnhancedVersionSpace implements EnhancedVersionSpace {
  private config: Required<VersionSpaceConfig>;
  private points: Map<string, VersionSpacePoint>;
  private mergeCount: number;
  private collapseCount: number;

  constructor(config: VersionSpaceConfig = {}) {
    this.config = {
      maxPoints: config.maxPoints ?? 1000,
      enableCompression: config.enableCompression ?? true,
      mergeStrategy: config.mergeStrategy ?? 'intersection',
      enableLazyEvaluation: config.enableLazyEvaluation ?? true,
    };

    this.points = new Map();
    this.mergeCount = 0;
    this.collapseCount = 0;
  }

  add(point: VersionSpacePoint): boolean {
    // Check capacity
    if (this.points.size >= this.config.maxPoints) {
      // Evict lowest confidence point
      this.evictLowestConfidence();
    }

    // Add the point
    this.points.set(point.id, { ...point });
    return true;
  }

  get(id: string): VersionSpacePoint | undefined {
    const point = this.points.get(id);
    return point ? { ...point } : undefined;
  }

  remove(id: string): boolean {
    return this.points.delete(id);
  }

  size(): number {
    return this.points.size;
  }

  merge(
    other: EnhancedVersionSpace,
    strategy?: MergeStrategy
  ): EnhancedVersionSpace {
    const mergeStrategy = strategy ?? this.config.mergeStrategy;
    const result = new DefaultEnhancedVersionSpace(this.config);

    // Get all programs from both spaces
    const thisPrograms = this.getAllPrograms();
    const otherPrograms = other.getAllPrograms();

    if (mergeStrategy === 'union') {
      // Union: add all points from both spaces
      for (const point of thisPrograms) {
        result.add(point);
      }
      for (const point of otherPrograms) {
        if (!result.get(point.id)) {
          result.add(point);
        }
      }
    } else {
      // Intersection: only add points present in both or with matching programs
      const otherProgramSet = new Set(otherPrograms.map((p) => p.program));
      const thisProgramSet = new Set(thisPrograms.map((p) => p.program));

      for (const point of thisPrograms) {
        if (otherProgramSet.has(point.program)) {
          result.add(point);
        }
      }

      for (const point of otherPrograms) {
        if (thisProgramSet.has(point.program) && !result.get(point.id)) {
          result.add(point);
        }
      }

      // If intersection is empty, keep the highest confidence from each
      if (result.size() === 0) {
        const best1 = this.getBestProgram();
        const best2 = other.getBestProgram();
        if (best1) result.add(best1);
        if (best2 && !result.get(best2.id)) result.add(best2);
      }
    }

    this.mergeCount++;
    return result;
  }

  collapse(): number {
    if (!this.config.enableCompression) {
      return 0;
    }

    // Group by program text
    const groups = new Map<string, VersionSpacePoint[]>();

    for (const point of this.points.values()) {
      const existing = groups.get(point.program);
      if (existing) {
        existing.push(point);
      } else {
        groups.set(point.program, [point]);
      }
    }

    // Collapse groups into single points with merged confidence
    let collapsedCount = 0;

    for (const [_program, group] of groups) {
      if (group.length > 1) {
        // Keep the one with highest confidence, merge examples
        group.sort((a, b) => b.confidence - a.confidence);
        const kept = group[0];

        // Merge examples from all points
        const allExamples: Example[] = [];
        for (const point of group) {
          allExamples.push(...point.examples);
        }
        kept.examples = this.deduplicateExamples(allExamples);

        // Update confidence (weighted average)
        const totalConf = group.reduce((sum, p) => sum + p.confidence, 0);
        kept.confidence = totalConf / group.length;

        // Remove duplicates
        for (let i = 1; i < group.length; i++) {
          this.points.delete(group[i].id);
          collapsedCount++;
        }

        // Update the kept point
        this.points.set(kept.id, kept);
      }
    }

    if (collapsedCount > 0) {
      this.collapseCount++;
    }

    return collapsedCount;
  }

  filterByConfidence(minConfidence: number): VersionSpacePoint[] {
    return Array.from(this.points.values()).filter(
      (p) => p.confidence >= minConfidence
    );
  }

  getBestProgram(): VersionSpacePoint | undefined {
    if (this.points.size === 0) {
      return undefined;
    }

    let best: VersionSpacePoint | undefined;
    for (const point of this.points.values()) {
      if (!best || point.confidence > best.confidence) {
        best = point;
      }
    }

    return best ? { ...best } : undefined;
  }

  getAllPrograms(): VersionSpacePoint[] {
    return Array.from(this.points.values())
      .sort((a, b) => b.confidence - a.confidence)
      .map((p) => ({ ...p }));
  }

  getStatistics(): VersionSpaceStatistics {
    const points = Array.from(this.points.values());

    if (points.length === 0) {
      return {
        totalPoints: 0,
        consistentPoints: 0,
        mergeCount: this.mergeCount,
        collapseCount: this.collapseCount,
        averageConfidence: 0,
        maxConfidence: 0,
        minConfidence: 0,
      };
    }

    const consistentPoints = points.filter((p) => p.consistent).length;
    const confidences = points.map((p) => p.confidence);
    const avgConfidence =
      confidences.reduce((a, b) => a + b, 0) / confidences.length;

    return {
      totalPoints: points.length,
      consistentPoints,
      mergeCount: this.mergeCount,
      collapseCount: this.collapseCount,
      averageConfidence: avgConfidence,
      maxConfidence: Math.max(...confidences),
      minConfidence: Math.min(...confidences),
    };
  }

  clear(): void {
    this.points.clear();
  }

  clone(): EnhancedVersionSpace {
    const cloned = new DefaultEnhancedVersionSpace(this.config);

    for (const point of this.points.values()) {
      cloned.add({ ...point, examples: [...point.examples] });
    }

    cloned.mergeCount = this.mergeCount;
    cloned.collapseCount = this.collapseCount;

    return cloned;
  }

  toJSON(): string {
    return JSON.stringify({
      config: this.config,
      points: Array.from(this.points.entries()),
      mergeCount: this.mergeCount,
      collapseCount: this.collapseCount,
    });
  }

  fromJSON(json: string): void {
    const data = JSON.parse(json);

    if (data.points) {
      this.points.clear();
      for (const [id, point] of data.points) {
        this.points.set(id, point);
      }
    }

    if (data.mergeCount !== undefined) {
      this.mergeCount = data.mergeCount;
    }

    if (data.collapseCount !== undefined) {
      this.collapseCount = data.collapseCount;
    }
  }

  // =========================================================================
  // Private Methods
  // =========================================================================

  private evictLowestConfidence(): void {
    let lowest: { id: string; confidence: number } | undefined;

    for (const [id, point] of this.points.entries()) {
      if (!lowest || point.confidence < lowest.confidence) {
        lowest = { id, confidence: point.confidence };
      }
    }

    if (lowest) {
      this.points.delete(lowest.id);
    }
  }

  private deduplicateExamples(examples: Example[]): Example[] {
    const seen = new Set<string>();
    const result: Example[] = [];

    for (const ex of examples) {
      const key = JSON.stringify(ex);
      if (!seen.has(key)) {
        seen.add(key);
        result.push(ex);
      }
    }

    return result;
  }
}

// =============================================================================
// Factory Function
// =============================================================================

/**
 * Create an EnhancedVersionSpace instance
 * @param config - Optional configuration
 * @returns EnhancedVersionSpace instance
 */
export function createEnhancedVersionSpace(
  config: VersionSpaceConfig = {}
): EnhancedVersionSpace {
  return new DefaultEnhancedVersionSpace(config);
}

export { DefaultEnhancedVersionSpace };
