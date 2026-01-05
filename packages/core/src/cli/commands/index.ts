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
import { registerLearnCommand } from './learn.js';
import { registerOntologyCommand } from './ontology.js';
import { registerReplCommand } from './repl.js';
import { registerPerfCommand } from './perf.js';
import { registerKgprCommands } from './kgpr.js';
import { registerTasksCommand } from './tasks.js';

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
  
  // Self-learning commands (REQ-LEARN-001〜006)
  registerLearnCommand(program);
  
  // Ontology commands (REQ-INT-003)
  registerOntologyCommand(program);
  
  // Interactive REPL (REQ-CLI-v1.5.0)
  registerReplCommand(program);
  
  // Performance monitoring (REQ-PERF-v1.5.1)
  registerPerfCommand(program);
  
  // Knowledge Graph PR (KGPR) commands
  registerKgprCommands(program);
  
  // Task management commands
  registerTasksCommand(program);
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

// Self-learning command export
export { registerLearnCommand } from './learn.js';

// Ontology command export
export { registerOntologyCommand } from './ontology.js';

// Interactive REPL command export
export { registerReplCommand } from './repl.js';

// Performance monitoring command export
export { registerPerfCommand } from './perf.js';

// KGPR command export
export { registerKgprCommands } from './kgpr.js';

// Tasks command export
export { registerTasksCommand } from './tasks.js';
