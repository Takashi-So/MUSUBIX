/**
 * CLI Commands Index
 * 
 * @packageDocumentation
 * @module cli/commands
 */

import type { Command } from 'commander';
import { registerInitCommand } from './init.js';
import { registerHelpCommand } from './help.js';

/**
 * Register all CLI commands
 */
export function registerCommands(program: Command): void {
  registerInitCommand(program);
  registerHelpCommand(program);
  
  // Future commands will be registered here:
  // registerRequirementsCommand(program);
  // registerDesignCommand(program);
  // registerCodegenCommand(program);
  // registerTestCommand(program);
  // registerTraceCommand(program);
  // registerExplainCommand(program);
}

export { registerInitCommand } from './init.js';
export { registerHelpCommand } from './help.js';
