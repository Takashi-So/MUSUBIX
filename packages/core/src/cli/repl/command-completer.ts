/**
 * Command Completer - Provides auto-completion for commands
 *
 * @module cli/repl/command-completer
 * @traces DES-CLI-002, REQ-CLI-002
 * @pattern Strategy - Different completion strategies for different contexts
 */

import * as fs from 'fs';
import * as path from 'path';
import type { CommandDefinition, CompletionResult } from './types.js';

/**
 * Command completer for REPL
 *
 * Provides TAB completion for commands, subcommands, options, and file paths.
 */
export class CommandCompleter {
  private commands: Map<string, CommandDefinition> = new Map();
  private maxSuggestions: number;

  constructor(options: { maxSuggestions?: number } = {}) {
    this.maxSuggestions = options.maxSuggestions ?? 10;
  }

  /**
   * Register command definitions for completion
   * @param commands - Command definitions
   */
  registerCommands(commands: CommandDefinition[]): void {
    for (const cmd of commands) {
      this.commands.set(cmd.name, cmd);
    }
  }

  /**
   * Get completions for partial input
   * @param line - Current input line
   * @param cursor - Cursor position
   * @returns Completion result
   */
  complete(line: string, cursor: number): CompletionResult {
    const beforeCursor = line.substring(0, cursor);
    const parts = this.tokenize(beforeCursor);

    if (parts.length === 0) {
      // Empty input - show all commands
      return {
        completions: Array.from(this.commands.keys()).slice(0, this.maxSuggestions),
        prefix: '',
      };
    }

    const lastPart = parts[parts.length - 1];

    // Check if completing an option
    if (lastPart.startsWith('--')) {
      return this.completeOption(parts, lastPart);
    }

    if (lastPart.startsWith('-') && lastPart.length === 2) {
      return this.completeShortOption(parts, lastPart);
    }

    // Check if completing a file path
    if (lastPart.includes('/') || lastPart.includes('.')) {
      return this.completeFilePath(lastPart);
    }

    // First part - complete command name
    if (parts.length === 1) {
      return this.completeCommand(lastPart);
    }

    // Subsequent parts - complete subcommand or argument
    const commandName = parts[0];
    const command = this.commands.get(commandName);

    if (command && parts.length === 2) {
      return this.completeSubcommand(command, lastPart);
    }

    // Try file path completion as fallback
    return this.completeFilePath(lastPart);
  }

  /**
   * Tokenize input line
   */
  private tokenize(line: string): string[] {
    const tokens: string[] = [];
    let current = '';
    let inQuote = false;
    let quoteChar = '';

    for (const char of line) {
      if (inQuote) {
        if (char === quoteChar) {
          inQuote = false;
        } else {
          current += char;
        }
      } else if (char === '"' || char === "'") {
        inQuote = true;
        quoteChar = char;
      } else if (char === ' ' || char === '\t') {
        if (current) {
          tokens.push(current);
          current = '';
        }
      } else {
        current += char;
      }
    }

    if (current || line.endsWith(' ')) {
      tokens.push(current);
    }

    return tokens;
  }

  /**
   * Complete command name
   */
  private completeCommand(prefix: string): CompletionResult {
    const matches = Array.from(this.commands.keys())
      .filter((name) => name.startsWith(prefix.toLowerCase()))
      .slice(0, this.maxSuggestions);

    return {
      completions: matches,
      prefix,
    };
  }

  /**
   * Complete subcommand
   */
  private completeSubcommand(command: CommandDefinition, prefix: string): CompletionResult {
    if (!command.subcommands) {
      return { completions: [], prefix };
    }

    const matches = command.subcommands
      .filter((sub) => sub.startsWith(prefix.toLowerCase()))
      .slice(0, this.maxSuggestions);

    return {
      completions: matches,
      prefix,
    };
  }

  /**
   * Complete option (--option)
   */
  private completeOption(parts: string[], prefix: string): CompletionResult {
    const commandName = parts[0];
    const command = this.commands.get(commandName);

    if (!command?.options) {
      return { completions: [], prefix };
    }

    const optionPrefix = prefix.slice(2); // Remove '--'
    const matches = command.options
      .filter((opt) => opt.name.slice(2).startsWith(optionPrefix))
      .map((opt) => opt.name)
      .slice(0, this.maxSuggestions);

    return {
      completions: matches,
      prefix,
    };
  }

  /**
   * Complete short option (-o)
   */
  private completeShortOption(parts: string[], prefix: string): CompletionResult {
    const commandName = parts[0];
    const command = this.commands.get(commandName);

    if (!command?.options) {
      return { completions: [], prefix };
    }

    const optionPrefix = prefix.slice(1); // Remove '-'
    const matches = command.options
      .filter((opt) => opt.alias && opt.alias.slice(1).startsWith(optionPrefix))
      .map((opt) => opt.alias!)
      .slice(0, this.maxSuggestions);

    return {
      completions: matches,
      prefix,
    };
  }

  /**
   * Complete file path
   */
  private completeFilePath(prefix: string): CompletionResult {
    try {
      const expandedPath = prefix.startsWith('~')
        ? path.join(process.env.HOME || '', prefix.slice(1))
        : prefix;

      const dir = path.dirname(expandedPath);
      const base = path.basename(expandedPath);
      const resolvedDir = path.resolve(dir || '.');

      if (!fs.existsSync(resolvedDir)) {
        return { completions: [], prefix };
      }

      const entries = fs.readdirSync(resolvedDir);
      const matches = entries
        .filter((entry) => entry.startsWith(base))
        .map((entry) => {
          const fullPath = path.join(resolvedDir, entry);
          const isDir = fs.statSync(fullPath).isDirectory();
          const relativePath = path.join(dir, entry);
          return isDir ? relativePath + '/' : relativePath;
        })
        .slice(0, this.maxSuggestions);

      return {
        completions: matches,
        prefix,
      };
    } catch {
      return { completions: [], prefix };
    }
  }

  /**
   * Get all registered commands
   */
  getCommands(): CommandDefinition[] {
    return Array.from(this.commands.values());
  }
}

/**
 * Default MUSUBIX command definitions
 */
export const MUSUBIX_COMMANDS: CommandDefinition[] = [
  {
    name: 'requirements',
    subcommands: ['analyze', 'validate', 'map', 'search'],
    options: [
      { name: '--file', alias: '-f', description: 'Input file', takesValue: true, valueType: 'file' },
      { name: '--output', alias: '-o', description: 'Output file', takesValue: true, valueType: 'file' },
      { name: '--format', description: 'Output format', takesValue: true, valueType: 'string' },
    ],
    description: 'Requirements management commands',
    examples: ['requirements analyze ./specs/REQ-001.md', 'requirements validate ./specs/'],
  },
  {
    name: 'design',
    subcommands: ['generate', 'patterns', 'validate', 'c4', 'adr'],
    options: [
      { name: '--file', alias: '-f', description: 'Input file', takesValue: true, valueType: 'file' },
      { name: '--output', alias: '-o', description: 'Output directory', takesValue: true, valueType: 'file' },
      { name: '--format', description: 'Output format', takesValue: true, valueType: 'string' },
    ],
    description: 'Design generation commands',
    examples: ['design generate ./specs/REQ-001.md', 'design c4 ./design/'],
  },
  {
    name: 'codegen',
    subcommands: ['generate', 'analyze', 'security'],
    options: [
      { name: '--file', alias: '-f', description: 'Input file', takesValue: true, valueType: 'file' },
      { name: '--output', alias: '-o', description: 'Output directory', takesValue: true, valueType: 'file' },
      { name: '--language', alias: '-l', description: 'Target language', takesValue: true, valueType: 'string' },
    ],
    description: 'Code generation commands',
    examples: ['codegen generate ./design/DES-001.md', 'codegen security ./src/'],
  },
  {
    name: 'test',
    subcommands: ['generate', 'coverage'],
    options: [
      { name: '--file', alias: '-f', description: 'Input file', takesValue: true, valueType: 'file' },
      { name: '--output', alias: '-o', description: 'Output directory', takesValue: true, valueType: 'file' },
    ],
    description: 'Test generation commands',
    examples: ['test generate ./src/', 'test coverage ./src/'],
  },
  {
    name: 'trace',
    subcommands: ['matrix', 'impact', 'validate'],
    options: [
      { name: '--id', description: 'Artifact ID', takesValue: true, valueType: 'string' },
      { name: '--output', alias: '-o', description: 'Output file', takesValue: true, valueType: 'file' },
    ],
    description: 'Traceability commands',
    examples: ['trace matrix', 'trace impact REQ-001'],
  },
  {
    name: 'learn',
    subcommands: ['status', 'feedback', 'patterns', 'add-pattern', 'remove-pattern', 'recommend', 'decay', 'export', 'import', 'best-practices'],
    options: [
      { name: '--id', description: 'Pattern or feedback ID', takesValue: true, valueType: 'string' },
      { name: '--output', alias: '-o', description: 'Output file', takesValue: true, valueType: 'file' },
      { name: '--category', alias: '-c', description: 'Filter by category', takesValue: true, valueType: 'string' },
    ],
    description: 'Self-learning system commands',
    examples: ['learn status', 'learn best-practices --category code'],
  },
  {
    name: 'explain',
    subcommands: ['why', 'graph'],
    options: [
      { name: '--id', description: 'Artifact ID', takesValue: true, valueType: 'string' },
      { name: '--output', alias: '-o', description: 'Output file', takesValue: true, valueType: 'file' },
    ],
    description: 'Explanation generation commands',
    examples: ['explain why REQ-001', 'explain graph DES-001'],
  },
  {
    name: 'ontology',
    subcommands: ['validate', 'check-circular', 'stats'],
    options: [
      { name: '--file', alias: '-f', description: 'Input file', takesValue: true, valueType: 'file' },
    ],
    description: 'Ontology validation commands',
    examples: ['ontology validate -f ./knowledge.json', 'ontology check-circular -f ./knowledge.json'],
  },
  {
    name: 'help',
    subcommands: [],
    options: [],
    description: 'Show help information',
    examples: ['help', 'help requirements'],
  },
  {
    name: 'exit',
    subcommands: [],
    options: [],
    description: 'Exit REPL session',
    examples: ['exit'],
  },
  {
    name: 'quit',
    subcommands: [],
    options: [],
    description: 'Exit REPL session (alias for exit)',
    examples: ['quit'],
  },
  {
    name: 'history',
    subcommands: [],
    options: [
      { name: '--clear', description: 'Clear history', takesValue: false },
      { name: '--search', alias: '-s', description: 'Search pattern', takesValue: true, valueType: 'string' },
    ],
    description: 'Show command history',
    examples: ['history', 'history --search req'],
  },
  {
    name: 'set',
    subcommands: [],
    options: [],
    description: 'Set session variable (VAR=value)',
    examples: ['set PROJECT=my-project', 'set OUTPUT_FORMAT=json'],
  },
  {
    name: 'env',
    subcommands: [],
    options: [],
    description: 'Show session variables',
    examples: ['env'],
  },
  {
    name: 'clear',
    subcommands: [],
    options: [],
    description: 'Clear terminal screen',
    examples: ['clear'],
  },
];

/**
 * Create a new command completer with default MUSUBIX commands
 */
export function createCommandCompleter(options?: { maxSuggestions?: number }): CommandCompleter {
  const completer = new CommandCompleter(options);
  completer.registerCommands(MUSUBIX_COMMANDS);
  return completer;
}
