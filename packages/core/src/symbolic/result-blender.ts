/**
 * @file result-blender.ts
 * @description ResultBlender - Neural/Symbolic結果の統合
 * @requirement REQ-ROUTE-003
 * @design DES-SYMB-001 §4.21
 * @task TSK-SYMB-015
 */

import type { Explanation, Evidence } from './types.js';

// ============================================================================
// Types
// ============================================================================

/**
 * ブレンド戦略
 */
export type BlendStrategy = 'neural_priority' | 'symbolic_priority' | 'confidence_weighted';

/**
 * 記号結果の検証ステータス
 */
export type SymbolicVerdict = 'valid' | 'invalid' | 'unknown' | 'partial';

/**
 * ニューラル結果
 */
export interface NeuralResult<T = unknown> {
  /** 候補/推奨 */
  output: T;
  /** 信頼度 (0-1) */
  confidence?: number;
  /** LLMのメタデータ */
  metadata?: {
    model?: string;
    tokens?: number;
    latencyMs?: number;
  };
}

/**
 * 記号結果
 */
export interface SymbolicResult {
  /** 検証結果 */
  verdict: SymbolicVerdict;
  /** 証跡 */
  evidence: Evidence[];
  /** 修正案（invalidの場合） */
  corrections?: string[];
  /** 違反リスト */
  violations?: Array<{
    rule: string;
    description: string;
    severity: 'critical' | 'high' | 'medium' | 'low';
  }>;
}

/**
 * 信頼度推定結果
 */
export interface ConfidenceEstimate {
  /** 総合信頼度 (0-1) */
  overall: number;
  /** 要素別信頼度 */
  breakdown?: {
    syntactic?: number;
    semantic?: number;
    structural?: number;
  };
}

/**
 * ソース帰属
 */
export interface Attribution {
  /** ニューラル割合 (%) */
  neuralPct: number;
  /** 記号割合 (%) */
  symbolicPct: number;
}

/**
 * ブレンド結果
 */
export interface BlendedResult<T = unknown> {
  /** 統合された結果 */
  blended: T;
  /** ソース帰属 */
  attribution: Attribution;
  /** 採用された戦略 */
  strategy: BlendStrategy;
  /** 結果タイプ */
  resultType: 'adopted' | 'modified' | 'rejected';
  /** 説明 */
  explanation: Explanation;
  /** 修正案（invalidの場合） */
  suggestedCorrections?: string[];
}

/**
 * Blender設定
 */
export interface ResultBlenderConfig {
  /** デフォルト戦略 */
  defaultStrategy?: BlendStrategy;
  /** 信頼度閾値（これ以上でニューラル採用） */
  confidenceThreshold?: number;
  /** symbolicがinvalidの場合にニューラル単独採用を許可するか */
  allowNeuralOnlyWhenInvalid?: boolean;
}

// ============================================================================
// Constants
// ============================================================================

/**
 * デフォルト設定
 */
export const DEFAULT_BLENDER_CONFIG: Required<ResultBlenderConfig> = {
  defaultStrategy: 'confidence_weighted',
  confidenceThreshold: 0.8,
  allowNeuralOnlyWhenInvalid: false,
};

// ============================================================================
// ResultBlender Class
// ============================================================================

/**
 * 結果ブレンダー
 * @description Neural/Symbolic結果を戦略に基づいて統合する
 */
export class ResultBlender<T = unknown> {
  private readonly config: Required<ResultBlenderConfig>;

  constructor(config: ResultBlenderConfig = {}) {
    this.config = { ...DEFAULT_BLENDER_CONFIG, ...config };
  }

  /**
   * 結果をブレンドする
   */
  blend(
    neuralResult: NeuralResult<T>,
    symbolicResult: SymbolicResult,
    options: {
      strategy?: BlendStrategy;
      confidence?: ConfidenceEstimate;
    } = {},
  ): BlendedResult<T> {
    const strategy = options.strategy ?? this.config.defaultStrategy;
    const confidence = options.confidence?.overall ?? neuralResult.confidence ?? 0.5;

    // symbolicがinvalidの場合の特別処理
    if (symbolicResult.verdict === 'invalid' && !this.config.allowNeuralOnlyWhenInvalid) {
      return this.handleInvalidSymbolic(neuralResult, symbolicResult, strategy);
    }

    // 戦略に基づいてブレンド
    switch (strategy) {
      case 'neural_priority':
        return this.blendNeuralPriority(neuralResult, symbolicResult, confidence);

      case 'symbolic_priority':
        return this.blendSymbolicPriority(neuralResult, symbolicResult, confidence);

      case 'confidence_weighted':
        return this.blendConfidenceWeighted(neuralResult, symbolicResult, confidence);

      default:
        throw new Error(`Unknown blend strategy: ${strategy}`);
    }
  }

  /**
   * symbolicがinvalidの場合の処理
   */
  private handleInvalidSymbolic(
    neuralResult: NeuralResult<T>,
    symbolicResult: SymbolicResult,
    strategy: BlendStrategy,
  ): BlendedResult<T> {
    return {
      blended: neuralResult.output,
      attribution: {
        neuralPct: 0,
        symbolicPct: 100,
      },
      strategy,
      resultType: 'rejected',
      explanation: {
        summary: 'Neural result rejected due to symbolic verification failure',
        reasoning: [
          'Symbolic verification returned: invalid',
          'Neural result cannot be adopted when symbolic verification fails',
          `${symbolicResult.violations?.length ?? 0} violation(s) detected`,
          'Corrections have been suggested based on symbolic analysis',
        ],
        evidence: symbolicResult.evidence,
        relatedRequirements: [],
      },
      suggestedCorrections: symbolicResult.corrections,
    };
  }

  /**
   * ニューラル優先戦略
   */
  private blendNeuralPriority(
    neuralResult: NeuralResult<T>,
    symbolicResult: SymbolicResult,
    _confidence: number,
  ): BlendedResult<T> {
    // ニューラル結果を採用し、記号結果は注釈として扱う
    const attribution: Attribution = {
      neuralPct: 80,
      symbolicPct: 20,
    };

    const resultType: 'adopted' | 'modified' =
      symbolicResult.verdict === 'valid' ? 'adopted' : 'modified';

    return {
      blended: neuralResult.output,
      attribution,
      strategy: 'neural_priority',
      resultType,
      explanation: {
        summary: `Neural result ${resultType} with symbolic verification as annotation`,
        reasoning: [
          'Strategy: neural_priority',
          `Neural confidence: ${((_confidence ?? 0.5) * 100).toFixed(0)}%`,
          `Symbolic verdict: ${symbolicResult.verdict}`,
          'Neural output adopted as primary result',
          'Symbolic evidence attached for reference',
        ],
        evidence: symbolicResult.evidence,
        relatedRequirements: [],
      },
    };
  }

  /**
   * 記号優先戦略
   */
  private blendSymbolicPriority(
    neuralResult: NeuralResult<T>,
    symbolicResult: SymbolicResult,
    confidence: number,
  ): BlendedResult<T> {
    // 記号結果を優先し、ニューラル結果は補助として扱う
    const attribution: Attribution = {
      neuralPct: 20,
      symbolicPct: 80,
    };

    // symbolicがvalidの場合はニューラル結果を採用
    // unknownの場合はニューラル結果を参考にしつつ修正を示唆
    const resultType: 'adopted' | 'modified' =
      symbolicResult.verdict === 'valid' ? 'adopted' : 'modified';

    return {
      blended: neuralResult.output,
      attribution,
      strategy: 'symbolic_priority',
      resultType,
      explanation: {
        summary: `Result determined by symbolic verification (${symbolicResult.verdict})`,
        reasoning: [
          'Strategy: symbolic_priority',
          `Symbolic verdict: ${symbolicResult.verdict}`,
          `Neural confidence: ${(confidence * 100).toFixed(0)}%`,
          'Symbolic verification takes precedence',
          symbolicResult.verdict === 'valid'
            ? 'Neural result validated and adopted'
            : 'Neural result requires modification based on symbolic analysis',
        ],
        evidence: symbolicResult.evidence,
        relatedRequirements: [],
      },
      suggestedCorrections:
        symbolicResult.verdict !== 'valid' ? symbolicResult.corrections : undefined,
    };
  }

  /**
   * 信頼度重み付け戦略
   */
  private blendConfidenceWeighted(
    neuralResult: NeuralResult<T>,
    symbolicResult: SymbolicResult,
    confidence: number,
  ): BlendedResult<T> {
    // 信頼度と検証結果に基づいて割合を決定
    let neuralPct: number;
    let symbolicPct: number;
    let resultType: 'adopted' | 'modified';

    if (symbolicResult.verdict === 'valid' && confidence >= this.config.confidenceThreshold) {
      // 高信頼度 + valid → ニューラル優位
      neuralPct = 70;
      symbolicPct = 30;
      resultType = 'adopted';
    } else if (symbolicResult.verdict === 'valid') {
      // 低信頼度 + valid → バランス
      neuralPct = 50;
      symbolicPct = 50;
      resultType = 'adopted';
    } else if (symbolicResult.verdict === 'unknown') {
      // unknown → 信頼度に応じて調整
      neuralPct = Math.round(confidence * 60 + 20);
      symbolicPct = 100 - neuralPct;
      resultType = 'modified';
    } else {
      // partial → 記号優位
      neuralPct = 30;
      symbolicPct = 70;
      resultType = 'modified';
    }

    return {
      blended: neuralResult.output,
      attribution: { neuralPct, symbolicPct },
      strategy: 'confidence_weighted',
      resultType,
      explanation: {
        summary: `Confidence-weighted blend: ${neuralPct}% neural, ${symbolicPct}% symbolic`,
        reasoning: [
          'Strategy: confidence_weighted',
          `Neural confidence: ${(confidence * 100).toFixed(0)}%`,
          `Confidence threshold: ${(this.config.confidenceThreshold * 100).toFixed(0)}%`,
          `Symbolic verdict: ${symbolicResult.verdict}`,
          `Attribution: neural=${neuralPct}%, symbolic=${symbolicPct}%`,
          resultType === 'adopted'
            ? 'Result adopted with high confidence'
            : 'Result may require modification',
        ],
        evidence: symbolicResult.evidence,
        relatedRequirements: [],
      },
      suggestedCorrections: resultType === 'modified' ? symbolicResult.corrections : undefined,
    };
  }

  /**
   * 設定を取得
   */
  getConfig(): Required<ResultBlenderConfig> {
    return { ...this.config };
  }

  /**
   * 戦略ごとの帰属割合を計算（事前確認用）
   */
  calculateAttribution(
    strategy: BlendStrategy,
    symbolicVerdict: SymbolicVerdict,
    confidence: number,
  ): Attribution {
    switch (strategy) {
      case 'neural_priority':
        return { neuralPct: 80, symbolicPct: 20 };

      case 'symbolic_priority':
        return { neuralPct: 20, symbolicPct: 80 };

      case 'confidence_weighted': {
        if (symbolicVerdict === 'valid' && confidence >= this.config.confidenceThreshold) {
          return { neuralPct: 70, symbolicPct: 30 };
        } else if (symbolicVerdict === 'valid') {
          return { neuralPct: 50, symbolicPct: 50 };
        } else if (symbolicVerdict === 'unknown') {
          const neuralPct = Math.round(confidence * 60 + 20);
          return { neuralPct, symbolicPct: 100 - neuralPct };
        }
        return { neuralPct: 30, symbolicPct: 70 };
      }

      default:
        return { neuralPct: 50, symbolicPct: 50 };
    }
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * ResultBlenderを作成
 */
export function createResultBlender<T = unknown>(config?: ResultBlenderConfig): ResultBlender<T> {
  return new ResultBlender<T>(config);
}

/**
 * 簡易ブレンド関数
 */
export function blendResults<T>(
  neuralResult: NeuralResult<T>,
  symbolicResult: SymbolicResult,
  strategy: BlendStrategy = 'confidence_weighted',
): BlendedResult<T> {
  const blender = new ResultBlender<T>();
  return blender.blend(neuralResult, symbolicResult, { strategy });
}
