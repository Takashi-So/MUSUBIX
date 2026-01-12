/**
 * Watch Command - CLI for auto lint/test execution
 *
 * Implements: TSK-WATCH-007, DES-WATCH-006, REQ-WATCH-006
 */

import { Command } from 'commander';
import { resolve } from 'node:path';
import { FileWatcher } from './file-watcher.js';
import { TaskScheduler } from './task-scheduler.js';
import { ResultReporter } from './result-reporter.js';
import { LintRunner } from './runners/lint-runner.js';
import { TestRunner } from './runners/test-runner.js';
import { SecurityRunner } from './runners/security-runner.js';
import { EARSRunner } from './runners/ears-runner.js';
import type { TaskType } from './task-scheduler.js';

/**
 * Watch command options
 */
interface WatchOptions {
  lint?: boolean;
  test?: boolean;
  security?: boolean;
  ears?: boolean;
  debounce?: string;
  output?: string;
  json?: boolean;
  quiet?: boolean;
  ignore?: string[];
  extensions?: string[];
}

/**
 * Create the watch command
 */
export function createWatchCommand(): Command {
  const watch = new Command('watch')
    .description('Watch files and auto-run lint/test on changes')
    .argument('[paths...]', 'Paths to watch (default: src/)', ['src/'])
    .option('--lint', 'Run ESLint on changes', true)
    .option('--no-lint', 'Disable ESLint')
    .option('--test', 'Run related tests on changes', true)
    .option('--no-test', 'Disable test runner')
    .option('--security', 'Run security scan on changes', false)
    .option('--ears', 'Run EARS validation on .md files', false)
    .option('--debounce <ms>', 'Debounce time in ms', '300')
    .option('-o, --output <file>', 'Output JSON report to file')
    .option('--json', 'Output in JSON format')
    .option('-q, --quiet', 'Suppress info messages')
    .option('--ignore <patterns...>', 'Additional ignore patterns')
    .option('--extensions <exts...>', 'File extensions to watch')
    .action(async (paths: string[], options: WatchOptions) => {
      await runWatch(paths, options);
    });

  return watch;
}

/**
 * Run the watch mode
 */
async function runWatch(paths: string[], options: WatchOptions): Promise<void> {
  const cwd = process.cwd();
  const resolvedPaths = paths.map((p) => resolve(cwd, p));

  // Default extensions based on enabled runners
  const defaultExtensions: string[] = [];
  if (options.lint !== false || options.test !== false || options.security) {
    defaultExtensions.push('.ts', '.tsx', '.js', '.jsx', '.mjs', '.cjs');
  }
  if (options.ears) {
    defaultExtensions.push('.md');
  }
  if (options.security) {
    defaultExtensions.push('.py', '.rb', '.rs', '.go', '.c', '.h');
  }

  const extensions = options.extensions ?? defaultExtensions;

  // Create components
  const watcher = new FileWatcher({
    paths: resolvedPaths,
    ignore: options.ignore ?? [],
    debounceMs: parseInt(options.debounce ?? '300', 10),
    extensions,
  });

  const debounceMs = parseInt(options.debounce ?? '300', 10);
  const scheduler = new TaskScheduler(debounceMs);

  const reporter = new ResultReporter({
    outputDir: options.output ?? '.musubix/watch',
    format: options.quiet ? 'json' : 'both',
    verbose: !options.quiet,
    colors: process.stdout.isTTY ?? false,
  });

  // Register enabled runners
  const enabledTasks: TaskType[] = [];

  if (options.lint !== false) {
    scheduler.registerRunner('lint', new LintRunner());
    enabledTasks.push('lint');
  }

  if (options.test !== false) {
    scheduler.registerRunner('test', new TestRunner());
    enabledTasks.push('test');
  }

  if (options.security) {
    scheduler.registerRunner('security', new SecurityRunner());
    enabledTasks.push('security');
  }

  if (options.ears) {
    scheduler.registerRunner('ears', new EARSRunner());
    enabledTasks.push('ears');
  }

  // Handle file changes
  watcher.on('change', (event) => {
    for (const taskType of enabledTasks) {
      scheduler.schedule(taskType, event.files);
    }
  });

  // Handle task completion
  scheduler.on('complete', (result) => {
    reporter.report(result);
  });

  // Handle errors
  watcher.on('error', (error) => {
    console.error('\x1b[31m❌ Watcher error:\x1b[0m', error.message);
  });

  scheduler.on('error', (error) => {
    console.error('\x1b[31m❌ Scheduler error:\x1b[0m', error.message);
  });

  // Start watching
  if (!options.quiet) {
    console.log('\x1b[36m🔍 MUSUBIX Watch Mode\x1b[0m');
    console.log(`   Watching: ${resolvedPaths.join(', ')}`);
    console.log(`   Runners: ${enabledTasks.join(', ') || 'none'}`);
    console.log(`   Extensions: ${extensions.join(', ')}`);
    console.log(`   Debounce: ${options.debounce ?? 300}ms`);
    console.log('');
    console.log('\x1b[33mPress Ctrl+C to stop\x1b[0m');
    console.log('');
  }

  await watcher.start();

  // Keep process running
  await new Promise<void>((resolve) => {
    process.on('SIGINT', async () => {
      if (!options.quiet) {
        console.log('\n\x1b[33m⏹️ Stopping watch mode...\x1b[0m');
      }

      await watcher.stop();

      // Generate final report if output file specified
      if (options.output) {
        const report = reporter.getLatestReport();
        if (!options.quiet) {
          console.log(`\n📊 Report saved to: ${options.output}`);
          console.log(`   Total issues: ${report.summary.issues}`);
        }
      }

      resolve();
      process.exit(0);
    });
  });
}

/**
 * Export for CLI integration
 */
export default createWatchCommand;
