/**
 * @nahisaho/musubix-expert-delegation
 * Semantic Router
 *
 * DES-TRG-001
 * Traces to: REQ-TRG-001
 */

import type {
  Expert,
  ExpertType,
  TriggerPattern,
  IntentResult,
} from '../types/index.js';
import { DelegationError } from '../types/errors.js';
import { ExpertManager } from '../experts/expert-manager.js';

/**
 * 言語検出結果
 */
type DetectedLanguage = 'en' | 'ja' | 'unknown';

/**
 * Semantic Router
 *
 * ユーザーメッセージから意図を検出し、適切なエキスパートにルーティングする。
 */
export class SemanticRouter {
  private customTriggers: Map<string, TriggerPattern & { expertType: ExpertType }> =
    new Map();

  constructor(private readonly expertManager: ExpertManager) {}

  /**
   * メッセージから意図を検出
   */
  detectIntent(message: string): IntentResult {
    const language = this.detectLanguage(message);
    const matches = this.expertManager.getAllMatchingExperts(message);

    if (matches.length === 0) {
      return {
        detected: false,
        expert: null,
        confidence: 0,
        language,
      };
    }

    // 最高優先度のマッチを取得
    const bestMatch = matches[0];

    // 信頼度を計算（優先度を0-1にスケール）
    const confidence = bestMatch.priority / 100;

    // 曖昧性チェック（複数のエキスパートが同等の優先度でマッチした場合）
    const topPriority = bestMatch.priority;
    const ambiguousMatches = matches.filter(
      (m) =>
        m.priority >= topPriority - 10 &&
        m.expert.type !== bestMatch.expert.type
    );

    if (ambiguousMatches.length > 0 && confidence < 0.8) {
      // 曖昧な場合は検出成功だがconfidenceを下げる
      return {
        detected: true,
        expert: bestMatch.expert.type,
        confidence: confidence * 0.7,
        matchedPattern: bestMatch.pattern,
        language,
      };
    }

    return {
      detected: true,
      expert: bestMatch.expert.type,
      confidence,
      matchedPattern: bestMatch.pattern,
      language,
    };
  }

  /**
   * 意図検出結果からエキスパートにルーティング
   * @throws DelegationError if intent is ambiguous or not detected
   */
  routeToExpert(intent: IntentResult): Expert {
    if (!intent.detected || !intent.expert) {
      throw DelegationError.fromCode('EXPERT_NOT_FOUND', {
        reason: 'No expert matched the message',
      });
    }

    // 信頼度が低すぎる場合は曖昧とみなす
    if (intent.confidence < 0.5) {
      throw DelegationError.fromCode('TRIGGER_AMBIGUOUS', {
        confidence: intent.confidence,
        matchedExpert: intent.expert,
      });
    }

    return this.expertManager.getExpert(intent.expert);
  }

  /**
   * カスタムトリガーを登録
   */
  registerTrigger(
    id: string,
    pattern: TriggerPattern,
    expertType: ExpertType
  ): void {
    this.customTriggers.set(id, { ...pattern, expertType });
  }

  /**
   * カスタムトリガーを削除
   */
  unregisterTrigger(id: string): boolean {
    return this.customTriggers.delete(id);
  }

  /**
   * メッセージと明示的なエキスパート指定からエキスパートを取得
   */
  resolveExpert(message: string, explicitExpert?: ExpertType): Expert {
    // 明示的な指定がある場合はそれを使用
    if (explicitExpert) {
      return this.expertManager.getExpert(explicitExpert);
    }

    // 意図を検出
    const intent = this.detectIntent(message);
    return this.routeToExpert(intent);
  }

  /**
   * 言語を検出
   */
  private detectLanguage(message: string): DetectedLanguage {
    // 日本語文字のパターン
    const japanesePattern = /[\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FFF]/;

    if (japanesePattern.test(message)) {
      return 'ja';
    }

    // 英語と判定（デフォルト）
    const englishPattern = /[a-zA-Z]/;
    if (englishPattern.test(message)) {
      return 'en';
    }

    return 'unknown';
  }

  /**
   * すべてのマッチングエキスパートを取得（デバッグ用）
   */
  debugMatches(
    message: string
  ): Array<{ expert: ExpertType; priority: number; pattern: string }> {
    return this.expertManager
      .getAllMatchingExperts(message)
      .map((m) => ({
        expert: m.expert.type,
        priority: m.priority,
        pattern: m.pattern,
      }));
  }
}

/**
 * SemanticRouterのファクトリ関数
 */
export function createSemanticRouter(
  expertManager?: ExpertManager
): SemanticRouter {
  return new SemanticRouter(expertManager ?? new ExpertManager());
}
