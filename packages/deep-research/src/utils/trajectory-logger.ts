// Trajectory Logger - Iteration Logging
// TSK-DR-004
// REQ: REQ-DR-CORE-010

import type { IterationLog } from '../types/index.js';

/**
 * Trajectory Logger for research iteration tracking
 * 
 * REQ: REQ-DR-CORE-010 - Log research trajectory for analysis
 * Supports JSON and Parquet export formats
 */
export class TrajectoryLogger {
  private logs: IterationLog[] = [];
  
  /**
   * Log an iteration
   */
  logIteration(log: IterationLog): void {
    this.logs.push(log);
    
    // Console output for real-time monitoring
    const actionDesc = this.formatAction(log.action);
    console.log(
      `[Iteration ${log.iteration}] ${actionDesc} | Tokens: ${log.tokensUsed} | Knowledge: +${log.knowledgeGained}`
    );
  }
  
  /**
   * Get all logs
   */
  getLogs(): IterationLog[] {
    return [...this.logs];
  }
  
  /**
   * Export logs in specified format
   * 
   * REQ: REQ-DR-CORE-010 - Parquet/JSON export
   */
  export(format: 'json' | 'parquet'): string | Buffer {
    if (format === 'json') {
      return JSON.stringify(this.logs, null, 2);
    } else if (format === 'parquet') {
      // TODO: Parquet export implementation (requires neural-search integration)
      // Will be implemented in TSK-DR-020 (Neural Search Integration)
      throw new Error('Parquet export not yet implemented. Use JSON format or implement neural-search integration first.');
    }
    
    throw new Error(`Unknown export format: ${format}`);
  }
  
  /**
   * Get summary statistics
   */
  getSummary(): {
    totalIterations: number;
    totalTokens: number;
    totalKnowledge: number;
    actions: Record<string, number>;
  } {
    const actions: Record<string, number> = {};
    
    for (const log of this.logs) {
      const actionType = log.action.type;
      actions[actionType] = (actions[actionType] || 0) + 1;
    }
    
    return {
      totalIterations: this.logs.length,
      totalTokens: this.logs.reduce((sum, log) => sum + log.tokensUsed, 0),
      totalKnowledge: this.logs.reduce((sum, log) => sum + log.knowledgeGained, 0),
      actions,
    };
  }
  
  /**
   * Clear all logs
   */
  clear(): void {
    this.logs = [];
  }
  
  /**
   * Format action for display
   */
  private formatAction(action: IterationLog['action']): string {
    switch (action.type) {
      case 'search':
        return `SEARCH "${action.query}" → ${action.resultsCount} results`;
      case 'read':
        return `READ ${action.url} → ${action.success ? 'SUCCESS' : 'FAILED'}`;
      case 'reason':
        return `REASON → +${action.knowledgeGained} knowledge`;
      case 'answer':
        return `ANSWER ${action.isDefinitive ? '(DEFINITIVE)' : '(TENTATIVE)'}: ${action.answer.slice(0, 50)}...`;
      default:
        return 'UNKNOWN ACTION';
    }
  }
}
