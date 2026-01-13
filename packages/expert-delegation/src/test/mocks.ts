/**
 * @nahisaho/musubix-expert-delegation
 * VS Code API Mocks
 *
 * DES-TST-001
 * Traces to: REQ-TST-001
 */

import type { LMProvider, RequestOptions, ProviderResponse, ModelInfo } from '../types/index.js';

/**
 * Mock Language Model
 */
export interface MockLanguageModel {
  id: string;
  name: string;
  family: string;
  version: string;
  maxInputTokens: number;
  vendor: string;
}

/**
 * Mock LLM Response
 */
export interface MockLLMResponse {
  content: string;
  finishReason?: 'stop' | 'length' | 'error';
  usage?: {
    promptTokens: number;
    completionTokens: number;
    totalTokens: number;
  };
}

/**
 * Mock VS Code Language Model Provider
 *
 * テスト用のモックLMプロバイダー。
 */
export class MockVSCodeLMProvider implements LMProvider {
  private responses: Map<string, MockLLMResponse> = new Map();
  private defaultResponse: MockLLMResponse = {
    content: 'Mock response',
    finishReason: 'stop',
    usage: {
      promptTokens: 100,
      completionTokens: 50,
      totalTokens: 150,
    },
  };
  private callCount = 0;
  private lastRequest: RequestOptions | null = null;
  private shouldFail = false;
  private failureError: Error | null = null;

  /**
   * レスポンスを設定
   */
  setResponse(pattern: string, response: MockLLMResponse): void {
    this.responses.set(pattern, response);
  }

  /**
   * デフォルトレスポンスを設定
   */
  setDefaultResponse(response: MockLLMResponse): void {
    this.defaultResponse = response;
  }

  /**
   * 失敗モードを設定
   */
  setFailure(error: Error): void {
    this.shouldFail = true;
    this.failureError = error;
  }

  /**
   * 失敗モードをリセット
   */
  clearFailure(): void {
    this.shouldFail = false;
    this.failureError = null;
  }

  /**
   * 呼び出しカウントを取得
   */
  getCallCount(): number {
    return this.callCount;
  }

  /**
   * 最後のリクエストを取得
   */
  getLastRequest(): RequestOptions | null {
    return this.lastRequest;
  }

  /**
   * 状態をリセット
   */
  reset(): void {
    this.responses.clear();
    this.callCount = 0;
    this.lastRequest = null;
    this.shouldFail = false;
    this.failureError = null;
  }

  /**
   * LMProvider.sendRequest の実装
   */
  async sendRequest(options: RequestOptions): Promise<ProviderResponse> {
    this.callCount++;
    this.lastRequest = options;

    if (this.shouldFail && this.failureError) {
      throw this.failureError;
    }

    // パターンマッチングでレスポンスを選択
    const userMessage = options.messages.find((m) => m.role === 'user')?.content ?? '';

    for (const [pattern, response] of this.responses) {
      if (userMessage.includes(pattern)) {
        return {
          content: response.content,
          finishReason: response.finishReason ?? 'stop',
          usage: response.usage,
        };
      }
    }

    return {
      content: this.defaultResponse.content,
      finishReason: this.defaultResponse.finishReason ?? 'stop',
      usage: this.defaultResponse.usage,
    };
  }

  /**
   * LMProvider.listModels の実装
   */
  async listModels(): Promise<ModelInfo[]> {
    return [
      {
        id: 'mock-gpt-4',
        name: 'Mock GPT-4',
        family: 'gpt-4',
        version: '4.0',
        maxInputTokens: 128000,
        vendor: 'mock',
      },
      {
        id: 'mock-claude-3',
        name: 'Mock Claude 3',
        family: 'claude-3',
        version: '3.0',
        maxInputTokens: 200000,
        vendor: 'mock',
      },
    ];
  }

  /**
   * LMProvider.selectModel の実装
   */
  async selectModel(): Promise<ModelInfo> {
    const models = await this.listModels();
    return models[0];
  }
}

/**
 * MockVSCodeLMProviderのファクトリ関数
 */
export function createMockVSCodeLMProvider(): MockVSCodeLMProvider {
  return new MockVSCodeLMProvider();
}

/**
 * VS Code API全体のモック
 */
export const mockVSCodeAPI = {
  lm: {
    selectChatModels: async () => [
      {
        id: 'mock-model',
        name: 'Mock Model',
        family: 'mock',
        version: '1.0',
        maxInputTokens: 100000,
        vendor: 'mock',
        sendRequest: async () => ({
          text: [{ value: 'Mock response' }],
        }),
      },
    ],
  },
  CancellationTokenSource: class {
    token = { isCancellationRequested: false };
    cancel() {
      this.token.isCancellationRequested = true;
    }
    dispose() {}
  },
  LanguageModelChatMessage: {
    User: (content: string) => ({ role: 'user', content }),
    Assistant: (content: string) => ({ role: 'assistant', content }),
  },
};
