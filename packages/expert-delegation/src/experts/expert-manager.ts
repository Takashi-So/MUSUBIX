/**
 * @nahisaho/musubix-expert-delegation
 * Expert Manager
 *
 * DES-EXP-001
 * Traces to: REQ-EXP-001
 */

import type { Expert, ExpertType } from '../types/index.js';
import { DelegationError } from '../types/errors.js';

// Default experts
import { architectExpert } from './architect.js';
import { securityAnalystExpert } from './security-analyst.js';
import { codeReviewerExpert } from './code-reviewer.js';
import { planReviewerExpert } from './plan-reviewer.js';
import { earsAnalystExpert } from './ears-analyst.js';
import { formalVerifierExpert } from './formal-verifier.js';
import { ontologyReasonerExpert } from './ontology-reasoner.js';

/**
 * Expert Manager
 *
 * エキスパートの登録・検索・管理を行う。
 */
export class ExpertManager {
  private experts: Map<ExpertType, Expert> = new Map();

  constructor(registerDefaults: boolean = true) {
    if (registerDefaults) {
      this.registerDefaultExperts();
    }
  }

  /**
   * デフォルトの7エキスパートを登録
   */
  private registerDefaultExperts(): void {
    this.registerExpert(architectExpert);
    this.registerExpert(securityAnalystExpert);
    this.registerExpert(codeReviewerExpert);
    this.registerExpert(planReviewerExpert);
    this.registerExpert(earsAnalystExpert);
    this.registerExpert(formalVerifierExpert);
    this.registerExpert(ontologyReasonerExpert);
  }

  /**
   * エキスパートを登録
   */
  registerExpert(expert: Expert): void {
    this.experts.set(expert.type, expert);
  }

  /**
   * エキスパートを取得
   * @throws DelegationError if expert not found
   */
  getExpert(type: ExpertType): Expert {
    const expert = this.experts.get(type);
    if (!expert) {
      throw DelegationError.fromCode('EXPERT_NOT_FOUND', { type });
    }
    return expert;
  }

  /**
   * エキスパートを安全に取得（見つからなければnull）
   */
  getExpertSafe(type: ExpertType): Expert | null {
    return this.experts.get(type) ?? null;
  }

  /**
   * 登録済みエキスパートの一覧を取得
   */
  listExperts(): Expert[] {
    return Array.from(this.experts.values());
  }

  /**
   * 登録済みエキスパートの一覧を取得（エイリアス）
   */
  getAllExperts(): Expert[] {
    return this.listExperts();
  }

  /**
   * 登録済みエキスパートタイプの一覧を取得
   */
  listExpertTypes(): ExpertType[] {
    return Array.from(this.experts.keys());
  }

  /**
   * トリガーパターンに基づいてエキスパートを検索
   *
   * @param message - 検索対象のメッセージ
   * @returns マッチしたエキスパート（優先度順）、または null
   */
  getExpertByTrigger(message: string): Expert | null {
    const lowerMessage = message.toLowerCase();
    let bestMatch: { expert: Expert; priority: number } | null = null;

    for (const expert of this.experts.values()) {
      for (const trigger of expert.triggers) {
        let matched = false;

        if (typeof trigger.pattern === 'string') {
          matched = lowerMessage.includes(trigger.pattern.toLowerCase());
        } else {
          matched = trigger.pattern.test(message);
        }

        if (matched) {
          if (!bestMatch || trigger.priority > bestMatch.priority) {
            bestMatch = { expert, priority: trigger.priority };
          }
        }
      }
    }

    return bestMatch?.expert ?? null;
  }

  /**
   * 複数のトリガーマッチを取得（曖昧性検出用）
   */
  getAllMatchingExperts(
    message: string
  ): Array<{ expert: Expert; priority: number; pattern: string }> {
    const lowerMessage = message.toLowerCase();
    const matches: Array<{
      expert: Expert;
      priority: number;
      pattern: string;
    }> = [];

    for (const expert of this.experts.values()) {
      for (const trigger of expert.triggers) {
        let matched = false;
        const patternStr =
          typeof trigger.pattern === 'string'
            ? trigger.pattern
            : trigger.pattern.source;

        if (typeof trigger.pattern === 'string') {
          matched = lowerMessage.includes(trigger.pattern.toLowerCase());
        } else {
          matched = trigger.pattern.test(message);
        }

        if (matched) {
          matches.push({
            expert,
            priority: trigger.priority,
            pattern: patternStr,
          });
        }
      }
    }

    // 優先度で降順ソート
    return matches.sort((a, b) => b.priority - a.priority);
  }

  /**
   * オントロジークラスでエキスパートを検索
   */
  getExpertByOntologyClass(ontologyClass: string): Expert | null {
    for (const expert of this.experts.values()) {
      if (expert.ontologyClass === ontologyClass) {
        return expert;
      }
    }
    return null;
  }

  /**
   * 能力（capability）でエキスパートを検索
   */
  getExpertsByCapability(
    capabilityName: string
  ): Array<{ expert: Expert; capability: Expert['capabilities'][0] }> {
    const results: Array<{
      expert: Expert;
      capability: Expert['capabilities'][0];
    }> = [];

    for (const expert of this.experts.values()) {
      const capability = expert.capabilities.find(
        (c) => c.name === capabilityName
      );
      if (capability) {
        results.push({ expert, capability });
      }
    }

    return results;
  }

  /**
   * 登録済みエキスパート数を取得
   */
  get count(): number {
    return this.experts.size;
  }
}

/**
 * デフォルトのExpertManagerインスタンスを作成
 */
export function createExpertManager(): ExpertManager {
  return new ExpertManager(true);
}
