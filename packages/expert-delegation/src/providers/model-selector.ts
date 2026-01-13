/**
 * @nahisaho/musubix-expert-delegation
 * Model Selector
 *
 * DES-PRV-002
 * Traces to: REQ-PRV-002
 */

import type { LMProvider, ModelInfo, ModelCriteria } from '../types/index.js';

/**
 * ModelSelectorを作成するファクトリ関数
 * @param provider - LMプロバイダー
 */
export function createModelSelector(provider: LMProvider): ModelSelector {
  return new ModelSelector(provider);
}

/**
 * モデル選択ヘルパー
 *
 * ファミリー、ベンダー、トークン数などの条件に基づいて
 * 最適なモデルを選択する。
 */
export class ModelSelector {
  constructor(private readonly provider: LMProvider) {}

  /**
   * 条件に合うモデルを選択（プロバイダーへ委譲）
   * @param criteria - モデル選択条件
   */
  async selectModel(criteria?: ModelCriteria): Promise<ModelInfo | null> {
    return this.provider.selectModel(criteria);
  }

  /**
   * ファミリーでモデルを選択
   * @param family - モデルファミリー（gpt-4, claude-3等）
   */
  async selectByFamily(family: string): Promise<ModelInfo | null> {
    return this.provider.selectModel({ family });
  }

  /**
   * ベンダーでモデルを選択
   * @param vendor - ベンダー（copilot, openai等）
   */
  async selectByVendor(vendor: string): Promise<ModelInfo | null> {
    return this.provider.selectModel({ vendor });
  }

  /**
   * プライマリモデルが利用不可の場合、セカンダリにフォールバック
   * @param primary - 優先モデル条件
   * @param secondary - フォールバック条件
   */
  async fallback(
    primary: ModelCriteria,
    secondary: ModelCriteria
  ): Promise<ModelInfo | null> {
    const primaryModel = await this.provider.selectModel(primary);
    if (primaryModel) {
      return primaryModel;
    }

    return this.provider.selectModel(secondary);
  }

  /**
   * 最大トークン数のモデルを選択
   */
  async selectLargestContext(): Promise<ModelInfo | null> {
    const models = await this.provider.listModels();
    if (models.length === 0) {
      return null;
    }

    return models.reduce((best, current) =>
      current.maxInputTokens > best.maxInputTokens ? current : best
    );
  }

  /**
   * 複数の条件を順番に試して最初に見つかったモデルを返す
   * @param criteriaList - 条件リスト（優先度順）
   */
  async selectFirst(criteriaList: ModelCriteria[]): Promise<ModelInfo | null> {
    for (const criteria of criteriaList) {
      const model = await this.provider.selectModel(criteria);
      if (model) {
        return model;
      }
    }
    return null;
  }
}
