// VS Code Extension Integration
// TSK-DR-021
// REQ: REQ-DR-INT-006
// DES: DES-DR-v3.4.0 Section 5.5

/**
 * Configuration for VS Code Extension integration
 */
export interface VSCodeExtensionConfig {
  /** Command prefix (default: musubix.deepResearch) */
  commandPrefix?: string;
  /** Enable progress notifications */
  enableProgress?: boolean;
  /** Output channel name */
  outputChannelName?: string;
}

/**
 * Default configuration
 */
const DEFAULT_CONFIG: Required<VSCodeExtensionConfig> = {
  commandPrefix: 'musubix.deepResearch',
  enableProgress: true,
  outputChannelName: 'MUSUBIX Deep Research',
};

/**
 * Research result for display
 */
export interface ResearchResult {
  query: string;
  summary: string;
  findings: string[];
  sources: string[];
  timestamp: string;
}

/**
 * VS Code Extension Integration
 * 
 * Integrates Deep Research with VS Code extension.
 * 
 * Features:
 * - Command registration
 * - Progress notifications
 * - Result display in output channel
 * - Configuration management
 * 
 * Note: This integration provides the interface only.
 * Actual VS Code extension activation and command handling
 * must be implemented in the extension's activate() function.
 */
export class VSCodeExtensionIntegration {
  private vscode: any = null; // typeof import('vscode')
  private config: Required<VSCodeExtensionConfig>;
  private outputChannel: any = null; // vscode.OutputChannel
  private commands: Map<string, () => void> = new Map();

  constructor(config?: VSCodeExtensionConfig) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  /**
   * Initialize the VS Code integration
   * 
   * @param vscodeModule - VS Code API module
   */
  async initialize(vscodeModule?: any): Promise<void> {
    if (vscodeModule) {
      this.vscode = vscodeModule;
    } else {
      // Try to load VS Code API dynamically
      try {
        this.vscode = await import('vscode' as any);
      } catch (error) {
        console.warn('⚠️  VS Code API not available (running outside VS Code environment)');
        return;
      }
    }

    // Create output channel
    if (this.vscode?.window?.createOutputChannel) {
      this.outputChannel = this.vscode.window.createOutputChannel(
        this.config.outputChannelName
      );
      console.log(`📺 Output channel created: ${this.config.outputChannelName}`);
    }
  }

  /**
   * Check if VS Code API is available
   */
  async isAvailable(): Promise<boolean> {
    if (this.vscode) return true;

    try {
      const vscodeModule = await import('vscode' as any);
      return vscodeModule !== null;
    } catch {
      return false;
    }
  }

  /**
   * Register a command
   * 
   * @param commandName - Command name (without prefix)
   * @param handler - Command handler
   * @returns Disposable
   */
  registerCommand(
    commandName: string,
    handler: (...args: any[]) => any
  ): any {
    if (!this.vscode) {
      console.warn('⚠️  VS Code API not initialized');
      return null;
    }

    const fullCommandName = `${this.config.commandPrefix}.${commandName}`;
    
    const disposable = this.vscode.commands.registerCommand(
      fullCommandName,
      handler
    );

    this.commands.set(commandName, handler);
    console.log(`✅ Command registered: ${fullCommandName}`);

    return disposable;
  }

  /**
   * Execute a command
   * 
   * @param commandName - Command name
   * @param args - Command arguments
   */
  async executeCommand(commandName: string, ...args: any[]): Promise<any> {
    if (!this.vscode) {
      throw new Error('VS Code API not initialized');
    }

    const fullCommandName = `${this.config.commandPrefix}.${commandName}`;
    return await this.vscode.commands.executeCommand(fullCommandName, ...args);
  }

  /**
   * Show information message
   * 
   * @param message - Message text
   */
  async showInfo(message: string): Promise<void> {
    if (!this.vscode) {
      console.log(`ℹ️  ${message}`);
      return;
    }

    await this.vscode.window.showInformationMessage(message);
  }

  /**
   * Show error message
   * 
   * @param message - Error message
   */
  async showError(message: string): Promise<void> {
    if (!this.vscode) {
      console.error(`❌ ${message}`);
      return;
    }

    await this.vscode.window.showErrorMessage(message);
  }

  /**
   * Show progress notification
   * 
   * @param title - Progress title
   * @param task - Task function
   */
  async withProgress<T>(
    title: string,
    task: (progress: any) => Promise<T>
  ): Promise<T> {
    if (!this.vscode || !this.config.enableProgress) {
      // Fallback: just execute the task without progress UI
      return await task({ report: () => {} });
    }

    return await this.vscode.window.withProgress(
      {
        location: this.vscode.ProgressLocation.Notification,
        title,
        cancellable: false,
      },
      task
    );
  }

  /**
   * Write to output channel
   * 
   * @param text - Text to write
   */
  writeOutput(text: string): void {
    if (this.outputChannel) {
      this.outputChannel.appendLine(text);
    } else {
      console.log(text);
    }
  }

  /**
   * Show output channel
   */
  showOutputChannel(): void {
    if (this.outputChannel) {
      this.outputChannel.show();
    }
  }

  /**
   * Clear output channel
   */
  clearOutput(): void {
    if (this.outputChannel) {
      this.outputChannel.clear();
    }
  }

  /**
   * Display research result
   * 
   * @param result - Research result
   */
  displayResult(result: ResearchResult): void {
    this.clearOutput();
    this.writeOutput('='.repeat(80));
    this.writeOutput(`🔍 Deep Research Result`);
    this.writeOutput('='.repeat(80));
    this.writeOutput('');
    this.writeOutput(`Query: ${result.query}`);
    this.writeOutput(`Timestamp: ${result.timestamp}`);
    this.writeOutput('');
    this.writeOutput('─'.repeat(80));
    this.writeOutput('Summary');
    this.writeOutput('─'.repeat(80));
    this.writeOutput(result.summary);
    this.writeOutput('');
    this.writeOutput('─'.repeat(80));
    this.writeOutput('Findings');
    this.writeOutput('─'.repeat(80));
    result.findings.forEach((finding, index) => {
      this.writeOutput(`${index + 1}. ${finding}`);
    });
    this.writeOutput('');
    this.writeOutput('─'.repeat(80));
    this.writeOutput('Sources');
    this.writeOutput('─'.repeat(80));
    result.sources.forEach((source, index) => {
      this.writeOutput(`[${index + 1}] ${source}`);
    });
    this.writeOutput('');
    this.writeOutput('='.repeat(80));

    this.showOutputChannel();
  }

  /**
   * Get configuration value
   * 
   * @param key - Configuration key
   * @param defaultValue - Default value
   */
  getConfig<T>(key: string, defaultValue: T): T {
    if (!this.vscode) {
      return defaultValue;
    }

    const config = this.vscode.workspace.getConfiguration('musubix.deepResearch');
    return (config.get(key, defaultValue) as T);
  }

  /**
   * Update configuration value
   * 
   * @param key - Configuration key
   * @param value - New value
   */
  async updateConfig(key: string, value: any): Promise<void> {
    if (!this.vscode) {
      console.warn('⚠️  VS Code API not initialized');
      return;
    }

    const config = this.vscode.workspace.getConfiguration('musubix.deepResearch');
    await config.update(key, value, true);
  }

  /**
   * Get all registered commands
   */
  getRegisteredCommands(): string[] {
    return Array.from(this.commands.keys());
  }

  /**
   * Dispose resources
   */
  dispose(): void {
    if (this.outputChannel) {
      this.outputChannel.dispose();
    }
    this.commands.clear();
  }
}

/**
 * Factory function to create VS Code Extension integration
 */
export function createVSCodeExtensionIntegration(
  config?: VSCodeExtensionConfig
): VSCodeExtensionIntegration {
  return new VSCodeExtensionIntegration(config);
}

/**
 * Example activation function for VS Code extension
 * 
 * This should be used in the extension's src/extension.ts file:
 * 
 * ```typescript
 * import * as vscode from 'vscode';
 * import { createVSCodeExtensionIntegration } from '@nahisaho/musubix-deep-research';
 * 
 * export async function activate(context: vscode.ExtensionContext) {
 *   const integration = createVSCodeExtensionIntegration();
 *   await integration.initialize(vscode);
 *   
 *   const disposable = integration.registerCommand('run', async (query: string) => {
 *     await integration.withProgress('Running deep research...', async (progress) => {
 *       progress.report({ message: 'Analyzing query...' });
 *       // Perform research
 *       const result = await performResearch(query);
 *       integration.displayResult(result);
 *     });
 *   });
 *   
 *   context.subscriptions.push(disposable);
 * }
 * ```
 */
export function createExtensionActivationExample(): string {
  return `
import * as vscode from 'vscode';
import { createVSCodeExtensionIntegration } from '@nahisaho/musubix-deep-research';

export async function activate(context: vscode.ExtensionContext) {
  const integration = createVSCodeExtensionIntegration();
  await integration.initialize(vscode);
  
  // Register 'run' command
  const runCommand = integration.registerCommand('run', async () => {
    const query = await vscode.window.showInputBox({
      prompt: 'Enter your research query',
      placeHolder: 'e.g., How to implement TypeScript decorators?',
    });
    
    if (!query) return;
    
    await integration.withProgress(
      'Running deep research...',
      async (progress) => {
        progress.report({ message: 'Analyzing query...' });
        // Perform research here
        await integration.showInfo(\`Research completed for: \${query}\`);
      }
    );
  });
  
  context.subscriptions.push(runCommand);
}
`.trim();
}
