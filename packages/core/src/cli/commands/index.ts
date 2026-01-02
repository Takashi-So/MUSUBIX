/**
 * CLI Commands Index
 * 
 * @packageDocumentation
 * @module cli/commands
 * 
 * @see REQ-CLI-001〜006 - CLI Commands
 * @see DES-MUSUBIX-001 Section 16-C - CLI設計
 * @see TSK-062〜080 - CLI実装タスク
 */

import type { Command } from 'commander';
import { registerInitCommand } from './init.js';
import { registerHelpCommand } from './help.js';
import { registerSkillsCommand } from './skills.js';
import { registerRequirementsCommand } from './requirements.js';
import { registerDesignCommand } from './design.js';
import { registerCodegenCommand } from './codegen.js';
import { registerTestCommand } from './test.js';
import { registerTraceCommand } from './trace.js';
import { registerExplainCommand } from './explain.js';

/**
 * Register all CLI commands
 * 
 * @see Article II - CLI Interface (Constitution)
 */
export function registerCommands(program: Command): void {
  // Core commands
  registerInitCommand(program);
  registerHelpCommand(program);
  registerSkillsCommand(program);
  
  // SDD workflow commands (REQ-CLI-001〜006)
  registerRequirementsCommand(program);
  registerDesignCommand(program);
  registerCodegenCommand(program);
  registerTestCommand(program);
  registerTraceCommand(program);
  registerExplainCommand(program);
}

// Core command exports
export { registerInitCommand } from './init.js';
export { registerHelpCommand } from './help.js';
export { registerSkillsCommand } from './skills.js';

// SDD workflow command exports
export { registerRequirementsCommand } from './requirements.js';
export { registerDesignCommand } from './design.js';
export { registerCodegenCommand } from './codegen.js';
export { registerTestCommand } from './test.js';
export { registerTraceCommand } from './trace.js';
export { registerExplainCommand } from './explain.js';
