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
import { registerDesignCommand } from './design/index.js';
import { registerCodegenCommand } from './codegen.js';
import { registerTestCommand } from './test.js';
import { registerTraceCommand } from './trace.js';
import { registerExplainCommand } from './explain.js';
import { registerLearnCommand } from './learn.js';
import { registerOntologyCommand } from './ontology.js';
import { registerReplCommand } from './repl.js';
import { registerPerfCommand } from './perf.js';
import { registerTasksCommand } from './tasks.js';
import { registerScaffoldCommand } from './scaffold.js';
import { registerSynthesisCommands } from './synthesis.js';
import { registerCodeGraphCommand } from './codegraph.js';
import { registerDeepResearchCommand } from './deep-research.js';

// Git-Native Knowledge System commands (v3.0.0)
import { registerKnowledgeCommands } from './knowledge.js';
import { registerPolicyCommands } from './policy.js';
import { registerDecisionCommands } from './decision.js';

// DX Enhancement commands (v3.1.0)
import { registerWatchCommand } from './watch.js';

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
  
  // Task management commands
  registerTasksCommand(program);
  
  // Project scaffolding commands (IMP-SDD-001)
  registerScaffoldCommand(program);
  
  // Synthesis commands (REQ-SY-v2.2.0)
  registerSynthesisCommands(program);
  
  // CodeGraph commands (REQ-CG-001)
  registerCodeGraphCommand(program);
  
  // Git-Native Knowledge System commands (v3.0.0)
  registerKnowledgeCommands(program);
  registerPolicyCommands(program);
  registerDecisionCommands(program);
  
  // DX Enhancement commands (v3.1.0)
  registerWatchCommand(program);
  
  // Deep Research commands (v3.4.0)
  registerDeepResearchCommand(program);
}

// Core command exports
export { registerInitCommand } from './init.js';
export { registerHelpCommand } from './help.js';
export { registerSkillsCommand } from './skills.js';

// SDD workflow command exports
export { registerRequirementsCommand } from './requirements.js';
export { registerDesignCommand } from './design/index.js';
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

// Tasks command export
export { registerTasksCommand } from './tasks.js';

// Scaffold command export (IMP-SDD-001)
export { registerScaffoldCommand } from './scaffold.js';
export type { ScaffoldStats, ScaffoldResult } from './scaffold.js';
export { _checkDirectory as checkDirectory } from './scaffold.js';

// Codegen types and functions (v3.3.10)
// Note: GeneratedCode and GenerationResult are also in codegen/generator.js
// Use CLI-specific names to avoid conflicts
export type { 
  GeneratedSkeleton, 
  FullSkeletonOptions,
  CodegenOptions,
} from './codegen.js';
export { generateFullSkeleton } from './codegen.js';

// Synthesis command export (REQ-SY-v2.2.0)
export { registerSynthesisCommands } from './synthesis.js';

// CodeGraph command export (REQ-CG-001)
export { registerCodeGraphCommand } from './codegraph.js';

// Git-Native Knowledge System command exports (v3.0.0)
export { registerKnowledgeCommands } from './knowledge.js';
export { registerPolicyCommands } from './policy.js';
export { registerDecisionCommands } from './decision.js';

// DX Enhancement command exports (v3.1.0)
export { registerWatchCommand } from './watch.js';

// Deep Research command exports (v3.4.0)
export { registerDeepResearchCommand } from './deep-research.js';
