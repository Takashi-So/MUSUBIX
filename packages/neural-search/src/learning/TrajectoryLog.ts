/**
 * Trajectory Log
 * @module @nahisaho/musubix-neural-search
 * @description Logs and queries search trajectories
 * Traces to: REQ-NS-004 (探索履歴学習)
 */

import type {
  ITrajectoryLog,
  SearchTrajectory,
  TrajectoryStatistics,
} from '../types.js';

/**
 * Trajectory log implementation
 */
export class TrajectoryLog implements ITrajectoryLog {
  private trajectories: Map<string, SearchTrajectory>;
  private specIndex: Map<string, string[]>; // spec hash -> trajectory ids

  constructor() {
    this.trajectories = new Map();
    this.specIndex = new Map();
  }

  /**
   * Log a completed trajectory
   */
  log(trajectory: SearchTrajectory): void {
    this.trajectories.set(trajectory.id, trajectory);

    // Index by specification
    const specHash = this.hashSpec(trajectory.specification);
    const existing = this.specIndex.get(specHash) ?? [];
    existing.push(trajectory.id);
    this.specIndex.set(specHash, existing);
  }

  /**
   * Query trajectories by specification
   */
  queryBySpec(spec: string, limit: number = 10): SearchTrajectory[] {
    const specHash = this.hashSpec(spec);
    const ids = this.specIndex.get(specHash) ?? [];

    return ids
      .slice(0, limit)
      .map((id) => this.trajectories.get(id))
      .filter((t): t is SearchTrajectory => t !== undefined);
  }

  /**
   * Get successful trajectories
   */
  getSuccessful(limit: number = 10): SearchTrajectory[] {
    return Array.from(this.trajectories.values())
      .filter((t) => t.outcome.success)
      .sort((a, b) => b.outcome.finalScore - a.outcome.finalScore)
      .slice(0, limit);
  }

  /**
   * Get all trajectories
   */
  getAll(): SearchTrajectory[] {
    return Array.from(this.trajectories.values());
  }

  /**
   * Get trajectory by ID
   */
  get(id: string): SearchTrajectory | undefined {
    return this.trajectories.get(id);
  }

  /**
   * Get statistics
   */
  getStatistics(): TrajectoryStatistics {
    const all = Array.from(this.trajectories.values());
    const successful = all.filter((t) => t.outcome.success);

    const totalLength = all.reduce((sum, t) => sum + t.path.length, 0);
    const totalDuration = all.reduce(
      (sum, t) => sum + t.path.reduce((s, step) => s + step.duration, 0),
      0
    );

    return {
      totalTrajectories: all.length,
      successRate: all.length > 0 ? successful.length / all.length : 0,
      averageLength: all.length > 0 ? totalLength / all.length : 0,
      averageDuration: all.length > 0 ? totalDuration / all.length : 0,
    };
  }

  /**
   * Clear all trajectories
   */
  clear(): void {
    this.trajectories.clear();
    this.specIndex.clear();
  }

  /**
   * Get size
   */
  size(): number {
    return this.trajectories.size;
  }

  /**
   * Hash specification for indexing
   */
  private hashSpec(spec: string): string {
    // Simple hash: normalized lowercase
    return spec.toLowerCase().replace(/\s+/g, ' ').trim().substring(0, 100);
  }
}
