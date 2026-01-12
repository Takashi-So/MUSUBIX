/**
 * Watch Module Types
 */

/**
 * Issue severity levels
 */
export type IssueSeverity = 'error' | 'warning' | 'info';

/**
 * Issue detected by a runner
 */
export interface Issue {
  /** Issue severity */
  severity: IssueSeverity;
  /** Issue message */
  message: string;
  /** File path */
  file: string;
  /** Line number (1-based) */
  line?: number;
  /** Column number (1-based) */
  column?: number;
  /** Rule ID that triggered the issue */
  ruleId?: string;
  /** Additional context */
  context?: Record<string, unknown>;
}

/**
 * Task runner interface
 */
export interface TaskRunner {
  /** Runner name */
  readonly name: string;
  
  /**
   * Run the task on specified files
   * @param files Files to process
   * @returns Array of issues found
   */
  run(files: string[]): Promise<Issue[]>;
  
  /**
   * Check if runner supports the given file
   * @param file File path
   */
  supports(file: string): boolean;
}
