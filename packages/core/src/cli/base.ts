/**
 * CLI Base Module
 * 
 * Provides the foundation for MUSUBIX command-line interface
 * 
 * @packageDocumentation
 * @module cli
 * 
 * @see REQ-ARC-002 - CLI Interface
 * @see DES-MUSUBIX-001 Section 3.2 - CLI Interface Design
 */

import { Command } from 'commander';
import { VERSION } from '../index.js';

/**
 * Exit codes for CLI commands
 * @see DES-MUSUBIX-001 Section 3.2.3
 */
export const ExitCode = {
  SUCCESS: 0,
  GENERAL_ERROR: 1,
  ARGUMENT_ERROR: 2,
  FILE_NOT_FOUND: 3,
  VALIDATION_ERROR: 4,
  SERVICE_ERROR: 5,
} as const;

export type ExitCode = (typeof ExitCode)[keyof typeof ExitCode];

/**
 * CLI output format options
 */
export type OutputFormat = 'text' | 'json' | 'yaml';

/**
 * Global CLI options
 */
export interface GlobalOptions {
  verbose: boolean;
  json: boolean;
  config?: string;
  quiet: boolean;
}

/**
 * Create the main CLI program
 */
export function createProgram(): Command {
  const program = new Command();

  program
    .name('musubix')
    .description('MUSUBIX - Neuro-Symbolic AI Coding System')
    .version(VERSION, '-v, --version', 'Display version number')
    .option('--verbose', 'Enable verbose output', false)
    .option('--json', 'Output in JSON format', false)
    .option('--config <path>', 'Path to configuration file')
    .option('-q, --quiet', 'Suppress non-essential output', false)
    .configureHelp({
      sortSubcommands: true,
      sortOptions: true,
    });

  return program;
}

/**
 * Get global options from command
 */
export function getGlobalOptions(command: Command): GlobalOptions {
  const opts = command.optsWithGlobals();
  return {
    verbose: opts.verbose ?? false,
    json: opts.json ?? false,
    config: opts.config,
    quiet: opts.quiet ?? false,
  };
}

/**
 * Output result based on format option
 */
export function outputResult<T>(
  data: T,
  options: { json?: boolean; quiet?: boolean }
): void {
  if (options.quiet) {
    return;
  }
  
  if (options.json) {
    console.log(JSON.stringify(data, null, 2));
  } else {
    console.log(data);
  }
}

/**
 * Handle CLI errors
 */
export function handleError(error: Error, options: GlobalOptions): never {
  if (options.json) {
    console.error(JSON.stringify({
      success: false,
      error: {
        name: error.name,
        message: error.message,
        stack: options.verbose ? error.stack : undefined,
      },
    }, null, 2));
  } else {
    console.error(`Error: ${error.message}`);
    if (options.verbose && error.stack) {
      console.error(error.stack);
    }
  }
  process.exit(ExitCode.GENERAL_ERROR);
}
