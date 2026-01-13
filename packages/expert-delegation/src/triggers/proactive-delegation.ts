/**
 * @nahisaho/musubix-expert-delegation
 * Proactive Delegation
 *
 * DES-TRG-002
 * Traces to: REQ-TRG-002
 */

import type { ExpertType } from '../types/index.js';

/**
 * セキュリティパターン検出結果
 */
export interface SecurityPatternMatch {
  pattern: string;
  severity: 'high' | 'medium' | 'low';
  location?: string;
}

/**
 * 非EARS要件検出結果
 */
export interface NonEarsMatch {
  text: string;
  suggestedPattern: 'ubiquitous' | 'event-driven' | 'state-driven' | 'unwanted' | 'optional';
  confidence: number;
}

/**
 * Proactive Delegation
 *
 * 自動的にエキスパートへの委任を提案するコンポーネント。
 * - 連続失敗時のエスカレーション
 * - セキュリティパターンの自動検出
 * - 非EARS形式の要件検出
 */
export class ProactiveDelegation {
  private failureCount: Map<string, number> = new Map();
  private readonly escalationThreshold: number;

  constructor(options: { escalationThreshold?: number } = {}) {
    this.escalationThreshold = options.escalationThreshold ?? 3;
  }

  /**
   * エスカレーションが必要かチェック
   * @param taskId - タスクID
   * @param increment - 失敗カウントを増加させるか
   */
  checkEscalation(taskId: string, increment: boolean = true): boolean {
    const current = this.failureCount.get(taskId) ?? 0;
    const newCount = increment ? current + 1 : current;

    if (increment) {
      this.failureCount.set(taskId, newCount);
    }

    return newCount >= this.escalationThreshold;
  }

  /**
   * 失敗カウントをリセット
   */
  resetFailureCount(taskId: string): void {
    this.failureCount.delete(taskId);
  }

  /**
   * コード内のセキュリティパターンを検出
   */
  detectSecurityPattern(code: string): SecurityPatternMatch[] {
    const patterns: SecurityPatternMatch[] = [];

    // SQLインジェクションの可能性（テンプレートリテラル内のSQL）
    if (
      /\$\{.*\}.*(?:SELECT|INSERT|UPDATE|DELETE|FROM|WHERE)/i.test(code) ||
      /(?:SELECT|INSERT|UPDATE|DELETE|FROM|WHERE).*\$\{/i.test(code)
    ) {
      patterns.push({
        pattern: 'SQL Injection',
        severity: 'high',
      });
    }

    // ハードコードされた認証情報
    if (/(?:password|secret|api_key|apikey)\s*[:=]\s*['"][^'"]+['"]/i.test(code)) {
      patterns.push({
        pattern: 'Hardcoded Credentials',
        severity: 'high',
      });
    }

    // evalの使用
    if (/\beval\s*\(/.test(code)) {
      patterns.push({
        pattern: 'eval() Usage',
        severity: 'medium',
      });
    }

    // dangerouslySetInnerHTML（React）
    if (/dangerouslySetInnerHTML/i.test(code)) {
      patterns.push({
        pattern: 'XSS Risk (dangerouslySetInnerHTML)',
        severity: 'medium',
      });
    }

    // 暗号化されていない通信
    if (/http:\/\/(?!localhost|127\.0\.0\.1)/i.test(code)) {
      patterns.push({
        pattern: 'Unencrypted HTTP',
        severity: 'low',
      });
    }

    return patterns;
  }

  /**
   * 非EARS形式の要件テキストを検出
   */
  detectNonEarsRequirement(text: string): NonEarsMatch | null {
    // すでにEARS形式の場合はスキップ
    if (this.isEarsFormat(text)) {
      return null;
    }

    // 要件らしいテキストかチェック
    const requirementIndicators = [
      /must\s+/i,
      /should\s+/i,
      /shall\s+/i,
      /need\s+to/i,
      /have\s+to/i,
      /required\s+to/i,
      /必要/,
      /しなければ/,
      /べき/,
      /こと$/,
    ];

    const isRequirement = requirementIndicators.some((r) => r.test(text));
    if (!isRequirement) {
      return null;
    }

    // パターンを推測
    const suggestedPattern = this.suggestEarsPattern(text);

    return {
      text,
      suggestedPattern,
      confidence: 0.7,
    };
  }

  /**
   * EARS形式かどうかを判定
   */
  private isEarsFormat(text: string): boolean {
    const earsPatterns = [
      /^THE\s+\w+\s+SHALL\s+/i,
      /^WHEN\s+.+,\s+THE\s+\w+\s+SHALL\s+/i,
      /^WHILE\s+.+,\s+THE\s+\w+\s+SHALL\s+/i,
      /^IF\s+.+,\s+THEN\s+THE\s+\w+\s+SHALL\s+/i,
      /^THE\s+\w+\s+SHALL\s+NOT\s+/i,
    ];

    return earsPatterns.some((p) => p.test(text.trim()));
  }

  /**
   * 適切なEARSパターンを提案
   */
  private suggestEarsPattern(
    text: string
  ): 'ubiquitous' | 'event-driven' | 'state-driven' | 'unwanted' | 'optional' {
    const lowerText = text.toLowerCase();

    // イベント駆動のキーワード
    if (/when|if\s+.+\s+then|upon|after|before|trigger/.test(lowerText)) {
      return 'event-driven';
    }

    // 状態駆動のキーワード
    if (/while|during|in\s+.+\s+mode|in\s+.+\s+state/.test(lowerText)) {
      return 'state-driven';
    }

    // 禁止事項のキーワード
    if (/not\s+|never|must\s+not|should\s+not|禁止|してはいけない/.test(lowerText)) {
      return 'unwanted';
    }

    // 条件付きのキーワード
    if (/if\s+|optional|may|can|場合/.test(lowerText)) {
      return 'optional';
    }

    // デフォルトは常に適用
    return 'ubiquitous';
  }

  /**
   * プロアクティブな委任提案を生成
   */
  suggestDelegation(
    code: string,
    requirements: string[]
  ): Array<{ expert: ExpertType; reason: string; priority: number }> {
    const suggestions: Array<{
      expert: ExpertType;
      reason: string;
      priority: number;
    }> = [];

    // セキュリティパターン検出
    const securityPatterns = this.detectSecurityPattern(code);
    if (securityPatterns.length > 0) {
      const highSeverity = securityPatterns.filter((p) => p.severity === 'high');
      suggestions.push({
        expert: 'security-analyst',
        reason: `${securityPatterns.length}個のセキュリティパターンを検出（${highSeverity.length}個が高リスク）`,
        priority: highSeverity.length > 0 ? 90 : 70,
      });
    }

    // 非EARS要件検出
    const nonEarsReqs = requirements
      .map((r) => this.detectNonEarsRequirement(r))
      .filter((r): r is NonEarsMatch => r !== null);

    if (nonEarsReqs.length > 0) {
      suggestions.push({
        expert: 'ears-analyst',
        reason: `${nonEarsReqs.length}個の要件がEARS形式ではありません`,
        priority: 60,
      });
    }

    return suggestions.sort((a, b) => b.priority - a.priority);
  }

  /**
   * 現在の失敗カウントを取得
   */
  getFailureCount(taskId: string): number {
    return this.failureCount.get(taskId) ?? 0;
  }

  /**
   * すべての失敗カウントをクリア
   */
  clearAll(): void {
    this.failureCount.clear();
  }
}

/**
 * ProactiveDelegationのファクトリ関数
 */
export function createProactiveDelegation(options?: {
  escalationThreshold?: number;
}): ProactiveDelegation {
  return new ProactiveDelegation(options);
}
