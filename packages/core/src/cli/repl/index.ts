/**
 * REPL Module - Interactive CLI Mode
 *
 * @module cli/repl
 * @traces REQ-CLI-v1.5.0, DES-CLI-v1.5.0
 */

// Types
export type {
  CommandResult,
  CompletionResult,
  CommandDefinition,
  OptionDefinition,
  ProjectContext,
  ReplConfig,
  OutputFormat,
  ReplEvent,
  ReplEventHandler,
} from './types.js';

export { DEFAULT_REPL_CONFIG } from './types.js';

// Components
export { ReplEngine, createReplEngine } from './repl-engine.js';
export { CommandCompleter, createCommandCompleter, MUSUBIX_COMMANDS } from './command-completer.js';
export { HistoryManager, createHistoryManager } from './history-manager.js';
export { SessionState, createSessionState } from './session-state.js';
export { PromptRenderer, createPromptRenderer } from './prompt-renderer.js';
export { OutputFormatter, createOutputFormatter } from './output-formatter.js';
