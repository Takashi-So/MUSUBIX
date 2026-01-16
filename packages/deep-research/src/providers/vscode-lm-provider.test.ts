// VS Code LM Provider Tests
// TSK-DR-011

import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest';
import { VSCodeLMProvider } from './vscode-lm-provider.js';

describe('VSCodeLMProvider', () => {
  let provider: VSCodeLMProvider;
  let mockVSCode: any;

  beforeEach(() => {
    // Mock VS Code API
    mockVSCode = {
      lm: {
        selectChatModels: vi.fn(),
      },
      LanguageModelChatMessage: {
        User: vi.fn((content) => ({ role: 'user', content })),
      },
    };

    (globalThis as any).vscode = mockVSCode;
    provider = new VSCodeLMProvider('copilot-gpt-4');
  });

  afterEach(() => {
    delete (globalThis as any).vscode;
  });

  describe('generate', () => {
    it('should generate text using VS Code LM', async () => {
      const mockModel = {
        sendRequest: vi.fn().mockResolvedValue({
          text: (async function* () {
            yield 'Hello ';
            yield 'from ';
            yield 'VS Code LM!';
          })(),
        }),
      };

      mockVSCode.lm.selectChatModels.mockResolvedValue([mockModel]);

      const result = await provider.generate('Test prompt');

      expect(result).toBe('Hello from VS Code LM!');
      expect(mockVSCode.lm.selectChatModels).toHaveBeenCalledWith({
        vendor: 'copilot',
        family: 'copilot-gpt-4',
      });
      expect(mockModel.sendRequest).toHaveBeenCalled();
    });

    it('should include system prompt if provided', async () => {
      const mockModel = {
        sendRequest: vi.fn().mockResolvedValue({
          text: (async function* () {
            yield 'Response';
          })(),
        }),
      };

      mockVSCode.lm.selectChatModels.mockResolvedValue([mockModel]);

      await provider.generate('User prompt', {
        systemPrompt: 'You are a helpful assistant',
      });

      const messages = mockModel.sendRequest.mock.calls[0][0];
      expect(messages).toHaveLength(2);
      expect(messages[0].content).toBe('You are a helpful assistant');
      expect(messages[1].content).toBe('User prompt');
    });

    it('should pass generation options', async () => {
      const mockModel = {
        sendRequest: vi.fn().mockResolvedValue({
          text: (async function* () {
            yield 'Test';
          })(),
        }),
      };

      mockVSCode.lm.selectChatModels.mockResolvedValue([mockModel]);

      await provider.generate('Prompt', {
        maxTokens: 100,
        temperature: 0.7,
        stop: ['\n\n'],
      });

      const options = mockModel.sendRequest.mock.calls[0][1];
      expect(options.maxTokens).toBe(100);
      expect(options.temperature).toBe(0.7);
      expect(options.stopSequences).toEqual(['\n\n']);
    });

    it('should throw error if VS Code API not available', async () => {
      delete (globalThis as any).vscode;

      await expect(provider.generate('Test')).rejects.toThrow('VS Code API not available');
    });

    it('should throw error if no models found', async () => {
      mockVSCode.lm.selectChatModels.mockResolvedValue([]);

      await expect(provider.generate('Test')).rejects.toThrow('No models found');
    });
  });

  describe('isAvailable', () => {
    it('should return true when VS Code LM is available', async () => {
      mockVSCode.lm.selectChatModels.mockResolvedValue([{ name: 'copilot-gpt-4' }]);

      const available = await provider.isAvailable();

      expect(available).toBe(true);
    });

    it('should return false when VS Code API not available', async () => {
      delete (globalThis as any).vscode;

      const available = await provider.isAvailable();

      expect(available).toBe(false);
    });

    it('should return false when no models available', async () => {
      mockVSCode.lm.selectChatModels.mockResolvedValue([]);

      const available = await provider.isAvailable();

      expect(available).toBe(false);
    });

    it('should return false on API error', async () => {
      mockVSCode.lm.selectChatModels.mockRejectedValue(new Error('API error'));

      const available = await provider.isAvailable();

      expect(available).toBe(false);
    });
  });
});
