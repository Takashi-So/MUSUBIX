// VS Code Extension Integration Tests
// TSK-DR-021
// REQ: REQ-DR-INT-006

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  VSCodeExtensionIntegration,
  createVSCodeExtensionIntegration,
  type VSCodeExtensionConfig,
  type ResearchResult,
  createExtensionActivationExample,
} from './vscode-extension.js';

/**
 * Mock VS Code API
 */
function createMockVSCode() {
  const outputChannel = {
    appendLine: vi.fn(),
    show: vi.fn(),
    clear: vi.fn(),
    dispose: vi.fn(),
  };

  const commands = new Map<string, Function>();

  return {
    window: {
      createOutputChannel: vi.fn(() => outputChannel),
      showInformationMessage: vi.fn(),
      showErrorMessage: vi.fn(),
      withProgress: vi.fn(async (options, task) => {
        const progress = { report: vi.fn() };
        return await task(progress);
      }),
    },
    commands: {
      registerCommand: vi.fn((name: string, handler: Function) => {
        commands.set(name, handler);
        return { dispose: vi.fn() };
      }),
      executeCommand: vi.fn(async (name: string, ...args: any[]) => {
        const handler = commands.get(name);
        if (handler) {
          return await handler(...args);
        }
        throw new Error(`Command not found: ${name}`);
      }),
    },
    workspace: {
      getConfiguration: vi.fn(() => ({
        get: vi.fn((key: string, defaultValue: any) => defaultValue),
        update: vi.fn(),
      })),
    },
    ProgressLocation: {
      Notification: 15,
    },
    _outputChannel: outputChannel,
    _commands: commands,
  };
}

describe('VS Code Extension Integration', () => {
  describe('Initialization', () => {
    it('should create instance with default config', () => {
      const integration = new VSCodeExtensionIntegration();
      expect(integration).toBeDefined();
      expect(integration.getRegisteredCommands()).toEqual([]);
    });

    it('should create instance with custom config', () => {
      const config: VSCodeExtensionConfig = {
        commandPrefix: 'custom.prefix',
        enableProgress: false,
        outputChannelName: 'Custom Channel',
      };
      const integration = new VSCodeExtensionIntegration(config);
      expect(integration).toBeDefined();
    });

    it('should initialize with VS Code module', async () => {
      const integration = new VSCodeExtensionIntegration();
      const mockVSCode = createMockVSCode();

      await integration.initialize(mockVSCode);

      expect(mockVSCode.window.createOutputChannel).toHaveBeenCalledWith(
        'MUSUBIX Deep Research'
      );
    });

    it('should handle initialization without VS Code module', async () => {
      const integration = new VSCodeExtensionIntegration();
      await integration.initialize();
      // Should not throw, just log warning
      expect(integration).toBeDefined();
    });
  });

  describe('Availability Check', () => {
    it('should return true after initialization', async () => {
      const integration = new VSCodeExtensionIntegration();
      const mockVSCode = createMockVSCode();
      await integration.initialize(mockVSCode);

      const available = await integration.isAvailable();
      expect(available).toBe(true);
    });

    it('should return false without initialization', async () => {
      const integration = new VSCodeExtensionIntegration();
      const available = await integration.isAvailable();
      expect(available).toBe(false);
    });
  });

  describe('Command Registration', () => {
    let integration: VSCodeExtensionIntegration;
    let mockVSCode: ReturnType<typeof createMockVSCode>;

    beforeEach(async () => {
      integration = new VSCodeExtensionIntegration();
      mockVSCode = createMockVSCode();
      await integration.initialize(mockVSCode);
    });

    it('should register command successfully', () => {
      const handler = vi.fn();
      const disposable = integration.registerCommand('test', handler);

      expect(disposable).toBeDefined();
      expect(mockVSCode.commands.registerCommand).toHaveBeenCalledWith(
        'musubix.deepResearch.test',
        handler
      );
      expect(integration.getRegisteredCommands()).toContain('test');
    });

    it('should execute registered command', async () => {
      const handler = vi.fn(() => 'result');
      integration.registerCommand('test', handler);

      await integration.executeCommand('test', 'arg1', 'arg2');

      expect(handler).toHaveBeenCalledWith('arg1', 'arg2');
    });

    it('should return null when registering without VS Code', () => {
      const uninitializedIntegration = new VSCodeExtensionIntegration();
      const disposable = uninitializedIntegration.registerCommand('test', vi.fn());

      expect(disposable).toBeNull();
    });
  });

  describe('Message Display', () => {
    let integration: VSCodeExtensionIntegration;
    let mockVSCode: ReturnType<typeof createMockVSCode>;

    beforeEach(async () => {
      integration = new VSCodeExtensionIntegration();
      mockVSCode = createMockVSCode();
      await integration.initialize(mockVSCode);
    });

    it('should show information message', async () => {
      await integration.showInfo('Test message');

      expect(mockVSCode.window.showInformationMessage).toHaveBeenCalledWith(
        'Test message'
      );
    });

    it('should show error message', async () => {
      await integration.showError('Error message');

      expect(mockVSCode.window.showErrorMessage).toHaveBeenCalledWith(
        'Error message'
      );
    });

    it('should handle messages without VS Code', async () => {
      const uninitializedIntegration = new VSCodeExtensionIntegration();
      await uninitializedIntegration.showInfo('Test');
      await uninitializedIntegration.showError('Error');
      // Should not throw, just log
      expect(uninitializedIntegration).toBeDefined();
    });
  });

  describe('Progress Notification', () => {
    let integration: VSCodeExtensionIntegration;
    let mockVSCode: ReturnType<typeof createMockVSCode>;

    beforeEach(async () => {
      integration = new VSCodeExtensionIntegration();
      mockVSCode = createMockVSCode();
      await integration.initialize(mockVSCode);
    });

    it('should show progress notification', async () => {
      const task = vi.fn(async (progress: any) => {
        progress.report({ message: 'Working...' });
        return 'result';
      });

      const result = await integration.withProgress('Test Progress', task);

      expect(result).toBe('result');
      expect(mockVSCode.window.withProgress).toHaveBeenCalled();
      expect(task).toHaveBeenCalled();
    });

    it('should execute task without progress when disabled', async () => {
      const integrationNoProgress = new VSCodeExtensionIntegration({
        enableProgress: false,
      });
      await integrationNoProgress.initialize(mockVSCode);

      const task = vi.fn(async () => 'result');
      const result = await integrationNoProgress.withProgress('Test', task);

      expect(result).toBe('result');
      expect(task).toHaveBeenCalled();
    });

    it('should execute task without VS Code API', async () => {
      const uninitializedIntegration = new VSCodeExtensionIntegration();
      const task = vi.fn(async () => 'result');

      const result = await uninitializedIntegration.withProgress('Test', task);

      expect(result).toBe('result');
      expect(task).toHaveBeenCalled();
    });
  });

  describe('Output Channel', () => {
    let integration: VSCodeExtensionIntegration;
    let mockVSCode: ReturnType<typeof createMockVSCode>;

    beforeEach(async () => {
      integration = new VSCodeExtensionIntegration();
      mockVSCode = createMockVSCode();
      await integration.initialize(mockVSCode);
    });

    it('should write to output channel', () => {
      integration.writeOutput('Test output');

      expect(mockVSCode._outputChannel.appendLine).toHaveBeenCalledWith(
        'Test output'
      );
    });

    it('should show output channel', () => {
      integration.showOutputChannel();

      expect(mockVSCode._outputChannel.show).toHaveBeenCalled();
    });

    it('should clear output channel', () => {
      integration.clearOutput();

      expect(mockVSCode._outputChannel.clear).toHaveBeenCalled();
    });
  });

  describe('Result Display', () => {
    let integration: VSCodeExtensionIntegration;
    let mockVSCode: ReturnType<typeof createMockVSCode>;

    beforeEach(async () => {
      integration = new VSCodeExtensionIntegration();
      mockVSCode = createMockVSCode();
      await integration.initialize(mockVSCode);
    });

    it('should display research result', () => {
      const result: ResearchResult = {
        query: 'Test query',
        summary: 'Test summary',
        findings: ['Finding 1', 'Finding 2'],
        sources: ['Source 1', 'Source 2'],
        timestamp: '2024-01-01T00:00:00Z',
      };

      integration.displayResult(result);

      expect(mockVSCode._outputChannel.clear).toHaveBeenCalled();
      expect(mockVSCode._outputChannel.appendLine).toHaveBeenCalled();
      expect(mockVSCode._outputChannel.show).toHaveBeenCalled();

      // Verify result formatting
      const calls = mockVSCode._outputChannel.appendLine.mock.calls;
      const output = calls.map(call => call[0]).join('\n');
      expect(output).toContain('Test query');
      expect(output).toContain('Test summary');
      expect(output).toContain('Finding 1');
      expect(output).toContain('Source 1');
    });
  });

  describe('Configuration', () => {
    let integration: VSCodeExtensionIntegration;
    let mockVSCode: ReturnType<typeof createMockVSCode>;

    beforeEach(async () => {
      integration = new VSCodeExtensionIntegration();
      mockVSCode = createMockVSCode();
      await integration.initialize(mockVSCode);
    });

    it('should get configuration value', () => {
      const value = integration.getConfig('testKey', 'defaultValue');
      expect(value).toBe('defaultValue');
    });

    it('should update configuration value', async () => {
      await integration.updateConfig('testKey', 'newValue');

      expect(mockVSCode.workspace.getConfiguration).toHaveBeenCalledWith(
        'musubix.deepResearch'
      );
      // Verify update was called on the returned config object
      const getConfigCalls = mockVSCode.workspace.getConfiguration.mock.results;
      if (getConfigCalls.length > 0) {
        const configObject = getConfigCalls[getConfigCalls.length - 1].value;
        expect(configObject.update).toHaveBeenCalledWith('testKey', 'newValue', true);
      }
    });

    it('should handle config without VS Code', () => {
      const uninitializedIntegration = new VSCodeExtensionIntegration();
      const value = uninitializedIntegration.getConfig('test', 'default');
      expect(value).toBe('default');
    });
  });

  describe('Disposal', () => {
    it('should dispose resources', async () => {
      const integration = new VSCodeExtensionIntegration();
      const mockVSCode = createMockVSCode();
      await integration.initialize(mockVSCode);

      integration.registerCommand('test', vi.fn());
      integration.dispose();

      expect(mockVSCode._outputChannel.dispose).toHaveBeenCalled();
      expect(integration.getRegisteredCommands()).toEqual([]);
    });
  });

  describe('Factory Function', () => {
    it('should create integration instance', () => {
      const integration = createVSCodeExtensionIntegration();
      expect(integration).toBeInstanceOf(VSCodeExtensionIntegration);
    });

    it('should create with custom config', () => {
      const config: VSCodeExtensionConfig = {
        commandPrefix: 'test.prefix',
      };
      const integration = createVSCodeExtensionIntegration(config);
      expect(integration).toBeInstanceOf(VSCodeExtensionIntegration);
    });
  });

  describe('Example Generation', () => {
    it('should generate activation example', () => {
      const example = createExtensionActivationExample();
      expect(example).toBeDefined();
      expect(example).toContain('activate');
      expect(example).toContain('vscode.ExtensionContext');
      expect(example).toContain('createVSCodeExtensionIntegration');
    });
  });

  describe('Error Handling', () => {
    it('should handle command execution without initialization', async () => {
      const integration = new VSCodeExtensionIntegration();

      await expect(
        integration.executeCommand('test')
      ).rejects.toThrow('VS Code API not initialized');
    });

    it('should handle command execution for non-existent command', async () => {
      const integration = new VSCodeExtensionIntegration();
      const mockVSCode = createMockVSCode();
      await integration.initialize(mockVSCode);

      await expect(
        integration.executeCommand('nonexistent')
      ).rejects.toThrow('Command not found');
    });

    it('should handle config update without VS Code', async () => {
      const integration = new VSCodeExtensionIntegration();
      await integration.updateConfig('test', 'value');
      // Should not throw, just log warning
      expect(integration).toBeDefined();
    });
  });
});

describe('VS Code Extension E2E Integration', () => {
  it('should perform full integration workflow', async () => {
    const integration = createVSCodeExtensionIntegration({
      commandPrefix: 'test.research',
      enableProgress: true,
      outputChannelName: 'Test Channel',
    });

    const mockVSCode = createMockVSCode();
    await integration.initialize(mockVSCode);

    // Register command
    const handler = vi.fn(async (query: string) => {
      await integration.showInfo(`Processing: ${query}`);
      return `Result for ${query}`;
    });
    const disposable = integration.registerCommand('run', handler);

    // Execute command with progress
    const result = await integration.withProgress(
      'Running research...',
      async (progress) => {
        progress.report({ message: 'Analyzing...' });
        return await integration.executeCommand('run', 'test query');
      }
    );

    expect(result).toBe('Result for test query');
    expect(handler).toHaveBeenCalledWith('test query');
    expect(mockVSCode.window.showInformationMessage).toHaveBeenCalledWith(
      'Processing: test query'
    );

    // Display result
    const researchResult: ResearchResult = {
      query: 'test query',
      summary: 'Summary',
      findings: ['Finding'],
      sources: ['Source'],
      timestamp: new Date().toISOString(),
    };
    integration.displayResult(researchResult);

    expect(mockVSCode._outputChannel.clear).toHaveBeenCalled();
    expect(mockVSCode._outputChannel.show).toHaveBeenCalled();

    // Cleanup
    integration.dispose();
    expect(disposable).toBeDefined();
  });
});
