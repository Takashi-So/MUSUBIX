/**
 * TrajectoryLogger
 * 
 * Search trajectory logging with JSON/Parquet export
 * 
 * @packageDocumentation
 * @module neural-search/logging
 * 
 * @see TSK-NS-107 - TrajectoryLogger実装
 * @see REQ-NS-107 - 探索軌跡ログ要件
 */

/**
 * Branch record in the search trajectory
 */
export interface BranchRecord {
  id: string;
  parentId: string | null;
  depth: number;
  score: number;
  timestamp: Date;
  state: Record<string, unknown>;
}

/**
 * Complete trajectory data
 */
export interface TrajectoryData {
  branches: BranchRecord[];
  totalBranches: number;
  maxDepth: number;
  bestScore: number;
  averageScore: number;
  branchesByDepth: Record<number, number>;
  startTime?: Date;
  endTime?: Date;
}

/**
 * Export format type
 */
export type TrajectoryExportFormat = 'json' | 'parquet';

/**
 * Parquet schema for trajectory data
 */
export interface ParquetSchema {
  name: string;
  type: string;
  fields: Array<{ name: string; type: string }>;
}

/**
 * Parquet export result
 */
export interface ParquetExport {
  schema: ParquetSchema;
  data: Array<Record<string, unknown>>;
}

/**
 * TrajectoryLogger interface
 */
export interface TrajectoryLogger {
  /**
   * Log a branch record
   */
  logBranch(branch: BranchRecord): void;

  /**
   * Export trajectory in specified format
   */
  export(format: TrajectoryExportFormat): string;

  /**
   * Get current trajectory data
   */
  getTrajectory(): TrajectoryData;

  /**
   * Clear all logged data
   */
  clear(): void;
}

/**
 * Default TrajectoryLogger implementation
 */
class DefaultTrajectoryLogger implements TrajectoryLogger {
  private branches: BranchRecord[] = [];
  private startTime?: Date;

  /**
   * Log a branch record
   */
  logBranch(branch: BranchRecord): void {
    if (!this.startTime) {
      this.startTime = new Date();
    }
    this.branches.push(branch);
  }

  /**
   * Export trajectory in specified format
   */
  export(format: TrajectoryExportFormat): string {
    if (format !== 'json' && format !== 'parquet') {
      throw new Error(`Invalid export format: ${format}. Use 'json' or 'parquet'.`);
    }

    if (format === 'json') {
      return this.exportJson();
    }
    return this.exportParquet();
  }

  /**
   * Export as JSON
   */
  private exportJson(): string {
    const trajectory = this.getTrajectory();
    return JSON.stringify(trajectory, (_key, value) => {
      if (value instanceof Date) {
        return value.toISOString();
      }
      return value;
    }, 2);
  }

  /**
   * Export as Parquet-compatible format
   */
  private exportParquet(): string {
    const schema: ParquetSchema = {
      name: 'TrajectoryData',
      type: 'record',
      fields: [
        { name: 'id', type: 'string' },
        { name: 'parentId', type: 'string' },
        { name: 'depth', type: 'int32' },
        { name: 'score', type: 'double' },
        { name: 'timestamp', type: 'timestamp' },
        { name: 'state', type: 'string' },
      ],
    };

    const data = this.branches.map(branch => ({
      id: branch.id,
      parentId: branch.parentId || '',
      depth: branch.depth,
      score: branch.score,
      timestamp: branch.timestamp.toISOString(),
      state: JSON.stringify(branch.state),
    }));

    const parquetExport: ParquetExport = { schema, data };
    return JSON.stringify(parquetExport, null, 2);
  }

  /**
   * Get current trajectory data
   */
  getTrajectory(): TrajectoryData {
    const totalBranches = this.branches.length;

    if (totalBranches === 0) {
      return {
        branches: [],
        totalBranches: 0,
        maxDepth: 0,
        bestScore: 0,
        averageScore: 0,
        branchesByDepth: {},
        startTime: this.startTime,
        endTime: new Date(),
      };
    }

    const maxDepth = Math.max(...this.branches.map(b => b.depth));
    const bestScore = Math.max(...this.branches.map(b => b.score));
    const averageScore = this.branches.reduce((sum, b) => sum + b.score, 0) / totalBranches;

    const branchesByDepth: Record<number, number> = {};
    for (const branch of this.branches) {
      branchesByDepth[branch.depth] = (branchesByDepth[branch.depth] || 0) + 1;
    }

    return {
      branches: [...this.branches],
      totalBranches,
      maxDepth,
      bestScore,
      averageScore,
      branchesByDepth,
      startTime: this.startTime,
      endTime: new Date(),
    };
  }

  /**
   * Clear all logged data
   */
  clear(): void {
    this.branches = [];
    this.startTime = undefined;
  }
}

/**
 * Create TrajectoryLogger instance
 */
export function createTrajectoryLogger(): TrajectoryLogger {
  return new DefaultTrajectoryLogger();
}

export { DefaultTrajectoryLogger };
