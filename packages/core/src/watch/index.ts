/**
 * Watch Module - File watching and auto-validation
 * 
 * @packageDocumentation
 */

export { FileWatcher, type WatchConfig, type FileChangeEvent } from './file-watcher.js';
export { TaskScheduler, type ScheduledTask, type TaskResult, type TaskType } from './task-scheduler.js';
export { ResultReporter, type ReportConfig, type WatchReport } from './result-reporter.js';
export { LintRunner, createLintRunner } from './runners/lint-runner.js';
export { TestRunner, createTestRunner } from './runners/test-runner.js';
export { SecurityRunner, createSecurityRunner } from './runners/security-runner.js';
export { EARSRunner, createEARSRunner } from './runners/ears-runner.js';
export { createWatchCommand } from './watch-command.js';
export type { TaskRunner, Issue } from './types.js';

