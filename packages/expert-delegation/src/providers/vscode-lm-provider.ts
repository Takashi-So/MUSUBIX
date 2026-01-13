/**
 * @nahisaho/musubix-expert-delegation
 * VS Code LM Provider
 *
 * DES-PRV-001
 * Traces to: REQ-PRV-001
 */

import type {
  LMProvider,
  RequestOptions,
  ProviderResponse,
  ModelInfo,
  ModelCriteria,
} from '../types/index.js';
import { DelegationError } from '../types/errors.js';

// Promise-like type for VS Code API
type Thenable<T> = PromiseLike<T>;

// VS Code API types (imported dynamically at runtime)
interface VSCodeLM {
  selectChatModels(selector?: {
    family?: string;
    vendor?: string;
  }): Thenable<VSCodeLanguageModelChat[]>;
}

interface VSCodeLanguageModelChat {
  id: string;
  name: string;
  family: string;
  vendor: string;
  maxInputTokens: number;
  sendRequest(
    messages: VSCodeLanguageModelChatMessage[],
    options?: unknown,
    token?: { isCancellationRequested: boolean }
  ): Thenable<AsyncIterable<string>>;
}

interface VSCodeLanguageModelChatMessage {
  role: string;
  content: string;
}

interface VSCodeNamespace {
  lm: VSCodeLM;
  LanguageModelChatMessage: {
    User(content: string): VSCodeLanguageModelChatMessage;
    Assistant(content: string): VSCodeLanguageModelChatMessage;
  };
}

/**
 * VSCodeLMProviderを作成するファクトリ関数
 * @param vscodeAPI - VS Code API（オプション、テスト用）
 */
export function createVSCodeLMProvider(vscodeAPI?: VSCodeNamespace): VSCodeLMProvider {
  return new VSCodeLMProvider(vscodeAPI);
}

/**
 * VS Code Language Model Provider
 *
 * VS Code LM APIを使用してLLMにアクセスするプロバイダー。
 * GitHub Copilotの認証を活用し、追加のAPIキー設定を不要にする。
 */
export class VSCodeLMProvider implements LMProvider {
  private vscode: VSCodeNamespace | null = null;
  private currentModel: VSCodeLanguageModelChat | null = null;

  constructor(vscodeAPI?: VSCodeNamespace) {
    this.vscode = vscodeAPI ?? null;
  }

  /**
   * VS Code APIを遅延取得
   */
  private async getVSCode(): Promise<VSCodeNamespace> {
    if (this.vscode) {
      return this.vscode;
    }

    try {
      // VS Code環境で動的にインポート
      // eslint-disable-next-line @typescript-eslint/no-require-imports
      const vscodeModule = require('vscode') as VSCodeNamespace;
      this.vscode = vscodeModule;
      return vscodeModule;
    } catch {
      throw DelegationError.fromCode('PROVIDER_UNAVAILABLE', {
        reason: 'VS Code environment not available',
      });
    }
  }

  /**
   * プロンプトを送信してレスポンスを取得
   */
  async sendRequest(options: RequestOptions): Promise<ProviderResponse> {
    try {
      const vscode = await this.getVSCode();

      // モデル選択
      let model: VSCodeLanguageModelChat;
      if (options.model) {
        const models = await vscode.lm.selectChatModels();
        const found = models.find((m: VSCodeLanguageModelChat) => m.id === options.model);
        if (!found) {
          throw DelegationError.fromCode('MODEL_NOT_AVAILABLE', {
            requestedModel: options.model,
          });
        }
        model = found;
      } else if (this.currentModel) {
        model = this.currentModel;
      } else {
        const models = await vscode.lm.selectChatModels();
        if (models.length === 0) {
          throw DelegationError.fromCode('MODEL_NOT_AVAILABLE', {
            reason: 'No models available',
          });
        }
        model = models[0];
      }

      // メッセージをフォーマット
      const userContent = options.messages
        .filter(m => m.role === 'user')
        .map(m => m.content)
        .join('\n\n');
      
      const systemContent = options.messages
        .filter(m => m.role === 'system')
        .map(m => m.content)
        .join('\n\n');

      const prompt = systemContent
        ? `${systemContent}\n\n---\n\n${userContent}`
        : userContent;

      // メッセージ作成
      const messages = [vscode.LanguageModelChatMessage.User(prompt)];

      // リクエスト送信
      const response = await model.sendRequest(
        messages,
        undefined,
        options.cancellationToken
      );

      // ストリームレスポンスを収集
      const content = await this.collectResponse(response);

      return {
        content,
        finishReason: 'stop',
      };
    } catch (error) {
      if (error instanceof DelegationError) {
        throw error;
      }

      // タイムアウト判定
      if (error instanceof Error && error.message.includes('timeout')) {
        throw DelegationError.fromCode('TIMEOUT', {
          originalError: error.message,
        });
      }

      // 認証エラー判定
      if (error instanceof Error && error.message.includes('auth')) {
        throw DelegationError.fromCode('AUTHENTICATION_FAILED', {
          originalError: error.message,
        });
      }

      // レート制限判定
      if (error instanceof Error && error.message.includes('rate')) {
        throw DelegationError.fromCode('RATE_LIMITED', {
          originalError: error.message,
        });
      }

      throw DelegationError.fromCode('PROVIDER_UNAVAILABLE', {
        originalError: error instanceof Error ? error.message : String(error),
      });
    }
  }

  /**
   * ストリームレスポンスを収集
   */
  private async collectResponse(
    stream: AsyncIterable<string>
  ): Promise<string> {
    const chunks: string[] = [];
    for await (const chunk of stream) {
      chunks.push(chunk);
    }
    return chunks.join('');
  }

  /**
   * 利用可能なモデル一覧を取得
   */
  async listModels(): Promise<ModelInfo[]> {
    try {
      const vscode = await this.getVSCode();
      const models = await vscode.lm.selectChatModels();

      return models.map((m: VSCodeLanguageModelChat) => ({
        id: m.id,
        name: m.name,
        family: m.family,
        version: '', // VS Code LM APIにはversionがない
        vendor: m.vendor,
        maxInputTokens: m.maxInputTokens,
      }));
    } catch (error) {
      if (error instanceof DelegationError) {
        throw error;
      }
      throw DelegationError.fromCode('PROVIDER_UNAVAILABLE', {
        originalError: error instanceof Error ? error.message : String(error),
      });
    }
  }

  /**
   * 条件に合うモデルを選択
   */
  async selectModel(criteria: ModelCriteria): Promise<ModelInfo | null> {
    try {
      const vscode = await this.getVSCode();
      const models = await vscode.lm.selectChatModels({
        family: criteria.family,
        vendor: criteria.vendor,
      });

      // 最小トークン数でフィルタ
      const filtered = criteria.minTokens
        ? models.filter((m: VSCodeLanguageModelChat) => m.maxInputTokens >= criteria.minTokens!)
        : models;

      if (filtered.length === 0) {
        return null;
      }

      // 最もトークン数が多いモデルを選択
      const selected = filtered.reduce((best: VSCodeLanguageModelChat, current: VSCodeLanguageModelChat) =>
        current.maxInputTokens > best.maxInputTokens ? current : best
      );

      // 現在のモデルとして保持
      this.currentModel = models.find((m: VSCodeLanguageModelChat) => m.id === selected.id) ?? null;

      return {
        id: selected.id,
        name: selected.name,
        family: selected.family,
        version: '', // VS Code LM APIにはversionがない
        vendor: selected.vendor,
        maxInputTokens: selected.maxInputTokens,
      };
    } catch (error) {
      if (error instanceof DelegationError) {
        throw error;
      }
      throw DelegationError.fromCode('PROVIDER_UNAVAILABLE', {
        originalError: error instanceof Error ? error.message : String(error),
      });
    }
  }

  /**
   * プロバイダーが利用可能かチェック
   */
  async isAvailable(): Promise<boolean> {
    try {
      const vscode = await this.getVSCode();
      const models = await vscode.lm.selectChatModels();
      return models.length > 0;
    } catch {
      return false;
    }
  }

  /**
   * 現在選択されているモデルを取得
   */
  getCurrentModel(): ModelInfo | null {
    if (!this.currentModel) {
      return null;
    }
    return {
      id: this.currentModel.id,
      name: this.currentModel.name,
      family: this.currentModel.family,
      version: '', // VS Code LM APIにはversionがない
      vendor: this.currentModel.vendor,
      maxInputTokens: this.currentModel.maxInputTokens,
    };
  }
}
