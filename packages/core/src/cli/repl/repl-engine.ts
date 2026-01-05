/**
 * REPL Engine - Interactive command-line interface
 *
 * @module cli/repl/repl-engine
 * @traces DES-CLI-001, REQ-CLI-001
 * @pattern Facade - Provides unified interface to REPL subsystems
 */

import * as readline from 'readline';
import { spawn } from 'child_process';
import type { CommandResult, ReplConfig, ReplEvent, ReplEventHandler } from './types.js';
import { DEFAULT_REPL_CONFIG } from './types.js';
import { HistoryManager, createHistoryManager } from './history-manager.js';
import { CommandCompleter, createCommandCompleter } from './command-completer.js';
import { SessionState, createSessionState } from './session-state.js';
import { PromptRenderer, createPromptRenderer } from './prompt-renderer.js';
import { OutputFormatter, createOutputFormatter } from './output-formatter.js';

/**
 * REPL Engine - Main controller for interactive CLI
 *
 * Coordinates readline, history, completion, and command execution.
 */
export class ReplEngine {
  private rl: readline.Interface | null = null;
  private running: boolean = false;
  private config: ReplConfig;

  private history: HistoryManager;
  private completer: CommandCompleter;
  private session: SessionState;
  private prompt: PromptRenderer;
  private formatter: OutputFormatter;
  private eventHandlers: ReplEventHandler[] = [];

  constructor(config?: Partial<ReplConfig>) {
    this.config = { ...DEFAULT_REPL_CONFIG, ...config };
    this.history = createHistoryManager(this.config.history);
    this.completer = createCommandCompleter({ maxSuggestions: this.config.completion.maxSuggestions });
    this.session = createSessionState();
    this.prompt = createPromptRenderer(this.config.prompt);
    this.formatter = createOutputFormatter({ defaultFormat: this.config.output.defaultFormat });
  }

  /**
   * Start REPL session
   */
  async start(): Promise<void> {
    if (this.running) {
      return;
    }

    this.running = true;
    this.emit({ type: 'start' });

    // Load history
    await this.history.load();

    // Create readline interface
    this.rl = readline.createInterface({
      input: process.stdin,
      output: process.stdout,
      completer: (line: string) => this.handleComplete(line),
      prompt: this.prompt.render(),
      historySize: this.config.history.maxSize,
    });

    // Setup event handlers
    this.setupEventHandlers();

    // Display welcome message
    this.displayWelcome();

    // Start prompt loop
    this.rl.prompt();

    // Wait for close
    return new Promise((resolve) => {
      this.rl?.on('close', () => {
        this.running = false;
        resolve();
      });
    });
  }

  /**
   * Execute a command string
   */
  async execute(command: string): Promise<CommandResult> {
    const startTime = Date.now();
    const trimmed = command.trim();

    this.emit({ type: 'command', command: trimmed });

    // Handle empty command
    if (!trimmed) {
      return { success: true, output: '', exitCode: 0 };
    }

    // Expand variables
    const expanded = this.session.expand(trimmed);

    try {
      // Parse command
      const [cmd, ...args] = this.parseCommand(expanded);

      // Handle built-in commands
      const result = await this.executeBuiltin(cmd, args);

      if (result) {
        result.duration = Date.now() - startTime;
        this.session.setLastResult(result);
        this.emit({ type: 'result', result });
        return result;
      }

      // Execute external command (delegate to CLI)
      const extResult = await this.executeExternal(cmd, args);
      extResult.duration = Date.now() - startTime;
      this.session.setLastResult(extResult);
      this.emit({ type: 'result', result: extResult });
      return extResult;
    } catch (error) {
      const result: CommandResult = {
        success: false,
        output: '',
        error: error instanceof Error ? error : new Error(String(error)),
        exitCode: 1,
        duration: Date.now() - startTime,
      };
      this.session.setLastResult(result);
      this.emit({ type: 'error', error: result.error! });
      return result;
    }
  }

  /**
   * Stop REPL session gracefully
   */
  async stop(): Promise<void> {
    if (!this.running) {
      return;
    }

    // Save history
    await this.history.save();

    // Close readline
    this.rl?.close();
    this.rl = null;
    this.running = false;

    this.emit({ type: 'stop' });
  }

  /**
   * Check if REPL is running
   */
  isRunning(): boolean {
    return this.running;
  }

  /**
   * Add event handler
   */
  on(handler: ReplEventHandler): void {
    this.eventHandlers.push(handler);
  }

  /**
   * Get session state
   */
  getSession(): SessionState {
    return this.session;
  }

  /**
   * Get history manager
   */
  getHistory(): HistoryManager {
    return this.history;
  }

  /**
   * Setup readline event handlers
   */
  private setupEventHandlers(): void {
    if (!this.rl) return;

    this.rl.on('line', async (line: string) => {
      const trimmed = line.trim();

      if (trimmed) {
        // Add to history
        this.history.add(trimmed);

        // Execute command
        const result = await this.execute(trimmed);

        // Display result
        this.displayResult(result);

        // Update prompt based on result
        this.prompt.setErrorState(!result.success);
      }

      // Show next prompt
      if (this.running) {
        this.rl?.setPrompt(this.prompt.render());
        this.rl?.prompt();
      }
    });

    this.rl.on('SIGINT', () => {
      console.log('\n(Use "exit" or "quit" to leave REPL)');
      this.prompt.setErrorState(false);
      this.rl?.setPrompt(this.prompt.render());
      this.rl?.prompt();
    });
  }

  /**
   * Handle TAB completion
   */
  private handleComplete(line: string): [string[], string] {
    const result = this.completer.complete(line, line.length);
    return [result.completions, result.prefix];
  }

  /**
   * Parse command string into parts
   */
  private parseCommand(command: string): string[] {
    const parts: string[] = [];
    let current = '';
    let inQuote = false;
    let quoteChar = '';

    for (const char of command) {
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
          parts.push(current);
          current = '';
        }
      } else {
        current += char;
      }
    }

    if (current) {
      parts.push(current);
    }

    return parts;
  }

  /**
   * Execute built-in REPL command
   */
  private async executeBuiltin(cmd: string, args: string[]): Promise<CommandResult | null> {
    switch (cmd.toLowerCase()) {
      case 'exit':
      case 'quit':
        await this.stop();
        return { success: true, output: 'Goodbye!', exitCode: 0 };

      case 'help':
        return this.showHelp(args[0]);

      case '?':
        return this.showHelp(args[0]);

      case 'history':
        return this.showHistory(args);

      case 'set':
        return this.setVariable(args);

      case 'env':
        return this.showEnvironment();

      case 'clear':
        console.clear();
        return { success: true, output: '', exitCode: 0 };

      default:
        return null; // Not a built-in command
    }
  }

  /**
   * Execute external CLI command
   */
  private async executeExternal(cmd: string, args: string[]): Promise<CommandResult> {
    const fullCommand = [cmd, ...args].join(' ');
    
    // Check if command exists
    const commandDef = this.completer.getCommands().find(c => c.name === cmd);
    if (!commandDef) {
      return {
        success: false,
        output: '',
        error: new Error(`Unknown command: ${cmd}\nType 'help' for available commands.`),
        exitCode: 127,
      };
    }

    // Execute CLI command via subprocess
    return new Promise((resolve) => {
      const cliArgs = [cmd, ...args];
      const child = spawn('npx', ['musubix', ...cliArgs], {
        stdio: ['pipe', 'pipe', 'pipe'],
        shell: true,
      });

      let stdout = '';
      let stderr = '';

      child.stdout?.on('data', (data) => {
        stdout += data.toString();
      });

      child.stderr?.on('data', (data) => {
        stderr += data.toString();
      });

      child.on('close', (code) => {
        const exitCode = code ?? 0;
        if (exitCode === 0) {
          resolve({
            success: true,
            output: stdout || `Command '${fullCommand}' executed successfully`,
            exitCode,
          });
        } else {
          resolve({
            success: false,
            output: stdout,
            error: new Error(stderr || `Command failed with exit code ${exitCode}`),
            exitCode,
          });
        }
      });

      child.on('error', (err) => {
        resolve({
          success: false,
          output: '',
          error: err,
          exitCode: 1,
        });
      });
    });
  }

  /**
   * Show help
   */
  private showHelp(command?: string): CommandResult {
    const commands = this.completer.getCommands();

    if (command) {
      const cmd = commands.find((c) => c.name === command);
      if (cmd) {
        let output = `${cmd.name} - ${cmd.description}\n\n`;
        if (cmd.subcommands && cmd.subcommands.length > 0) {
          output += `Subcommands:\n  ${cmd.subcommands.join(', ')}\n\n`;
        }
        if (cmd.options && cmd.options.length > 0) {
          output += 'Options:\n';
          for (const opt of cmd.options) {
            const alias = opt.alias ? `, ${opt.alias}` : '';
            output += `  ${opt.name}${alias}  ${opt.description}\n`;
          }
          output += '\n';
        }
        if (cmd.examples && cmd.examples.length > 0) {
          output += 'Examples:\n';
          for (const ex of cmd.examples) {
            output += `  ${ex}\n`;
          }
        }
        return { success: true, output, exitCode: 0 };
      }
      return {
        success: false,
        output: '',
        error: new Error(`Unknown command: ${command}`),
        exitCode: 1,
      };
    }

    // Show all commands
    let output = 'Available commands:\n\n';
    for (const cmd of commands) {
      output += `  ${cmd.name.padEnd(15)} ${cmd.description}\n`;
    }
    output += '\nType "help <command>" for more information.';
    return { success: true, output, exitCode: 0 };
  }

  /**
   * Show history
   */
  private showHistory(args: string[]): CommandResult {
    if (args.includes('--clear')) {
      this.history.clear();
      return { success: true, output: 'History cleared.', exitCode: 0 };
    }

    const searchIdx = args.indexOf('--search');
    if (searchIdx !== -1 && args[searchIdx + 1]) {
      const pattern = args[searchIdx + 1];
      const matches = this.history.search(pattern);
      if (matches.length === 0) {
        return { success: true, output: 'No matching commands found.', exitCode: 0 };
      }
      const output = matches.map((cmd, i) => `${i + 1}. ${cmd}`).join('\n');
      return { success: true, output, exitCode: 0 };
    }

    const all = this.history.getAll();
    if (all.length === 0) {
      return { success: true, output: 'No history.', exitCode: 0 };
    }
    const output = all.map((cmd, i) => `${i + 1}. ${cmd}`).join('\n');
    return { success: true, output, exitCode: 0 };
  }

  /**
   * Set session variable
   */
  private setVariable(args: string[]): CommandResult {
    if (args.length === 0) {
      return {
        success: false,
        output: '',
        error: new Error('Usage: set VAR=value'),
        exitCode: 1,
      };
    }

    const assignment = args.join(' ');
    const match = assignment.match(/^([A-Z_][A-Z0-9_]*)=(.*)$/i);
    if (!match) {
      return {
        success: false,
        output: '',
        error: new Error('Invalid assignment. Usage: set VAR=value'),
        exitCode: 1,
      };
    }

    const [, varName, value] = match;
    this.session.set(varName, value);
    return { success: true, output: `${varName}=${value}`, exitCode: 0 };
  }

  /**
   * Show environment variables
   */
  private showEnvironment(): CommandResult {
    const vars = this.session.getAll();
    if (Object.keys(vars).length === 0) {
      return { success: true, output: 'No session variables set.', exitCode: 0 };
    }
    const output = this.formatter.formatTable(
      Object.entries(vars).map(([key, value]) => ({ Variable: key, Value: value }))
    );
    return { success: true, output, exitCode: 0 };
  }

  /**
   * Display welcome message
   */
  private displayWelcome(): void {
    console.log(`
╔══════════════════════════════════════════════════════════════╗
║               MUSUBIX Interactive CLI v1.5.0                 ║
║   Neuro-Symbolic AI Integration System - REPL Mode          ║
╠══════════════════════════════════════════════════════════════╣
║  Type 'help' for available commands                          ║
║  Type 'exit' or 'quit' to leave                              ║
║  Press TAB for auto-completion                               ║
╚══════════════════════════════════════════════════════════════╝
`);
  }

  /**
   * Display command result
   */
  private displayResult(result: CommandResult): void {
    if (result.error) {
      console.error(`\x1b[31mError: ${result.error.message}\x1b[0m`);
    } else if (result.output) {
      console.log(result.output);
    }
  }

  /**
   * Emit event to handlers
   */
  private emit(event: ReplEvent): void {
    for (const handler of this.eventHandlers) {
      try {
        handler(event);
      } catch {
        // Ignore handler errors
      }
    }
  }
}

/**
 * Create a new REPL engine
 */
export function createReplEngine(config?: Partial<ReplConfig>): ReplEngine {
  return new ReplEngine(config);
}
