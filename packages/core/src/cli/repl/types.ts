/**
 * REPL Types - Type definitions for Interactive CLI Mode
 *
 * @module cli/repl/types
 * @traces DES-CLI-v1.5.0
 */

/**
 * Result of command execution
 */
export interface CommandResult {
  /** Whether the command succeeded */
  success: boolean;
  /** Command output */
  output: string;
  /** Error if command failed */
  error?: Error;
  /** Exit code (0 = success) */
  exitCode: number;
  /** Execution duration in ms */
  duration?: number;
}

/**
 * Result of completion
 */
export interface CompletionResult {
  /** Array of completion candidates */
  completions: string[];
  /** The prefix being completed */
  prefix: string;
}

/**
 * Command definition for completion
 */
export interface CommandDefinition {
  /** Command name */
  name: string;
  /** Available subcommands */
  subcommands?: string[];
  /** Available options */
  options?: OptionDefinition[];
  /** Command description */
  description: string;
  /** Example usage */
  examples?: string[];
}

/**
 * Option definition
 */
export interface OptionDefinition {
  /** Option name (e.g., '--file') */
  name: string;
  /** Short alias (e.g., '-f') */
  alias?: string;
  /** Description */
  description: string;
  /** Whether option takes a value */
  takesValue?: boolean;
  /** Value type hint */
  valueType?: 'file' | 'string' | 'number' | 'boolean';
}

/**
 * Project context for prompt
 */
export interface ProjectContext {
  /** Project name */
  name?: string;
  /** Current SDD phase */
  phase?: 'requirements' | 'design' | 'implementation' | 'test';
  /** Project root path */
  path?: string;
}

/**
 * REPL configuration
 */
export interface ReplConfig {
  /** History settings */
  history: {
    /** Max history entries */
    maxSize: number;
    /** History file path */
    filePath: string;
  };
  /** Prompt settings */
  prompt: {
    /** Show project name */
    showProject: boolean;
    /** Show current phase */
    showPhase: boolean;
    /** Use colors */
    useColor: boolean;
    /** Default prompt string */
    defaultPrompt: string;
  };
  /** Completion settings */
  completion: {
    /** Enable completion */
    enabled: boolean;
    /** Max suggestions */
    maxSuggestions: number;
  };
  /** Output settings */
  output: {
    /** Default format */
    defaultFormat: 'json' | 'table' | 'yaml';
    /** Enable paging */
    paging: boolean;
    /** Page size */
    pageSize: number;
  };
}

/**
 * Output format type
 */
export type OutputFormat = 'json' | 'table' | 'yaml' | 'auto';

/**
 * REPL event types
 */
export type ReplEvent =
  | { type: 'start' }
  | { type: 'stop' }
  | { type: 'command'; command: string }
  | { type: 'result'; result: CommandResult }
  | { type: 'error'; error: Error };

/**
 * REPL event handler
 */
export type ReplEventHandler = (event: ReplEvent) => void;

/**
 * Default REPL configuration
 */
export const DEFAULT_REPL_CONFIG: ReplConfig = {
  history: {
    maxSize: 1000,
    filePath: '~/.musubix/history',
  },
  prompt: {
    showProject: true,
    showPhase: true,
    useColor: true,
    defaultPrompt: 'musubix> ',
  },
  completion: {
    enabled: true,
    maxSuggestions: 10,
  },
  output: {
    defaultFormat: 'table',
    paging: true,
    pageSize: 50,
  },
};
