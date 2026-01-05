/**
 * Performance CLI Command
 *
 * @module cli/commands/perf
 * @traces REQ-PERF-005, DES-PERF-005
 */

import type { Command } from 'commander';
import { ExitCode, getGlobalOptions, outputResult } from '../base.js';
import {
  runStandardBenchmarks,
  formatBenchmarkSuiteResult,
  getMemoryMonitor,
  formatMemoryReport,
  getGlobalCache,
  measure,
} from '../../perf/index.js';
import { VERSION } from '../../version.js';

/**
 * Register the perf command
 */
export function registerPerfCommand(program: Command): void {
  const perf = program
    .command('perf')
    .description('Performance benchmarks and monitoring');

  // Benchmark subcommand
  perf
    .command('benchmark')
    .description('Run all performance benchmarks')
    .option('--json', 'Output in JSON format')
    .action(async (options: { json?: boolean }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        if (!globalOpts.quiet) {
          console.log('Running MUSUBIX benchmarks...\n');
        }

        const suite = await runStandardBenchmarks();

        if (options.json || globalOpts.json) {
          outputResult(suite, globalOpts);
        } else {
          console.log(formatBenchmarkSuiteResult(suite));
        }

        const allPassed = suite.passRate === 1;
        process.exit(allPassed ? ExitCode.SUCCESS : ExitCode.VALIDATION_ERROR);
      } catch (error) {
        outputResult(
          {
            success: false,
            error: error instanceof Error ? error.message : String(error),
          },
          globalOpts
        );
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // Startup time subcommand
  perf
    .command('startup')
    .description('Measure CLI startup time')
    .option('-n, --iterations <n>', 'Number of iterations', '5')
    .action(async (options: { iterations: string }) => {
      const globalOpts = getGlobalOptions(program);
      const iterations = parseInt(options.iterations, 10);

      try {
        if (!globalOpts.quiet) {
          console.log(`Measuring startup time (${iterations} iterations)...\n`);
        }

        const times: number[] = [];

        for (let i = 0; i < iterations; i++) {
          const { duration } = await measure(async () => {
            // Simulate startup by dynamically importing core modules
            await import('../../index.js');
          });
          times.push(duration);
        }

        const avg = times.reduce((a, b) => a + b, 0) / times.length;
        const min = Math.min(...times);
        const max = Math.max(...times);

        const result = {
          iterations,
          average: `${avg.toFixed(2)}ms`,
          min: `${min.toFixed(2)}ms`,
          max: `${max.toFixed(2)}ms`,
          target: '400ms',
          passed: avg < 400,
        };

        if (globalOpts.json) {
          outputResult(result, globalOpts);
        } else {
          console.log('Startup Time Results:');
          console.log(`  Iterations: ${iterations}`);
          console.log(`  Average:    ${result.average}`);
          console.log(`  Min:        ${result.min}`);
          console.log(`  Max:        ${result.max}`);
          console.log(`  Target:     ${result.target}`);
          console.log(`  Status:     ${result.passed ? '✓ PASS' : '✗ FAIL'}`);
        }

        process.exit(result.passed ? ExitCode.SUCCESS : ExitCode.VALIDATION_ERROR);
      } catch (error) {
        outputResult(
          {
            success: false,
            error: error instanceof Error ? error.message : String(error),
          },
          globalOpts
        );
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // Memory subcommand
  perf
    .command('memory')
    .description('Show memory usage')
    .option('--watch', 'Continuously monitor memory')
    .option('-i, --interval <ms>', 'Watch interval in milliseconds', '1000')
    .action(async (options: { watch?: boolean; interval: string }) => {
      const globalOpts = getGlobalOptions(program);
      const monitor = getMemoryMonitor();

      try {
        if (options.watch) {
          console.log('Monitoring memory (Ctrl+C to stop)...\n');

          const intervalMs = parseInt(options.interval, 10);
          const stop = monitor.startSampling(intervalMs);

          const displayInterval = setInterval(() => {
            console.clear();
            console.log(`MUSUBIX Memory Monitor - v${VERSION}\n`);
            console.log(formatMemoryReport(monitor.report()));
          }, intervalMs);

          process.on('SIGINT', () => {
            stop();
            clearInterval(displayInterval);
            console.log('\n\nStopped monitoring.');
            process.exit(ExitCode.SUCCESS);
          });
        } else {
          const report = monitor.report();

          if (globalOpts.json) {
            outputResult(report, globalOpts);
          } else {
            console.log(formatMemoryReport(report));
          }

          process.exit(ExitCode.SUCCESS);
        }
      } catch (error) {
        outputResult(
          {
            success: false,
            error: error instanceof Error ? error.message : String(error),
          },
          globalOpts
        );
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // Cache stats subcommand
  perf
    .command('cache-stats')
    .description('Show cache statistics')
    .action(async () => {
      const globalOpts = getGlobalOptions(program);

      try {
        const cache = getGlobalCache();

        const stats = {
          patterns: cache.patterns.stats(),
          ontology: cache.ontology.stats(),
          validation: cache.validation.stats(),
          ast: cache.ast.stats(),
        };

        if (globalOpts.json) {
          outputResult(stats, globalOpts);
        } else {
          console.log('Cache Statistics:\n');

          for (const [name, s] of Object.entries(stats)) {
            console.log(`${name}:`);
            console.log(`  Size:      ${s.size}/${s.maxSize}`);
            console.log(`  Hits:      ${s.hits}`);
            console.log(`  Misses:    ${s.misses}`);
            console.log(`  Hit Rate:  ${(s.hitRate * 100).toFixed(1)}%`);
            console.log(`  Evictions: ${s.evictions}`);
            console.log('');
          }
        }

        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        outputResult(
          {
            success: false,
            error: error instanceof Error ? error.message : String(error),
          },
          globalOpts
        );
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // Cache clear subcommand
  perf
    .command('cache-clear')
    .description('Clear all caches')
    .action(async () => {
      const globalOpts = getGlobalOptions(program);

      try {
        const cache = getGlobalCache();

        cache.patterns.clear();
        cache.ontology.clear();
        cache.validation.clear();
        cache.ast.clear();

        if (!globalOpts.quiet) {
          console.log('All caches cleared.');
        }

        outputResult({ success: true, message: 'Caches cleared' }, globalOpts);
        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        outputResult(
          {
            success: false,
            error: error instanceof Error ? error.message : String(error),
          },
          globalOpts
        );
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });
}
