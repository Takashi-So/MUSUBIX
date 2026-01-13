/**
 * @nahisaho/musubix-expert-delegation
 * Delegation Engine
 *
 * DES-DEL-001, DES-DEL-002, DES-DEL-003, DES-DEL-004
 * Traces to: REQ-DEL-001, REQ-DEL-002, REQ-DEL-003, REQ-DEL-004
 */

import type {
  Expert,
  ExpertType,
  DelegationTask,
  DelegationContext,
  DelegationResult,
  ConstitutionViolation,
  ExecutionMode,
} from '../types/index.js';
import type { LMProvider } from '../types/index.js';
import { ExpertManager } from '../experts/expert-manager.js';
import { SemanticRouter } from '../triggers/semantic-router.js';
import { AdvisoryMode } from './advisory-mode.js';
import { ImplementationMode } from './implementation-mode.js';
import { RetryHandler, type RetryConfig, type EscalationConfig } from './retry-handler.js';

/**
 * Delegation Engine設定
 */
export interface DelegationEngineConfig {
  /** リトライ設定 */
  retry?: Partial<RetryConfig>;
  /** エスカレーション設定 */
  escalation?: Partial<EscalationConfig>;
  /** デフォルト実行モード */
  defaultMode?: ExecutionMode;
  /** 憲法チェックを有効化 */
  enableConstitutionCheck?: boolean;
  /** トレーサビリティを強制 */
  enforceTraceability?: boolean;
}

/**
 * Delegation Engine
 *
 * エキスパート委任の中心的なオーケストレーションコンポーネント。
 */
export class DelegationEngine {
  private readonly expertManager: ExpertManager;
  private readonly semanticRouter: SemanticRouter;
  private readonly advisoryMode: AdvisoryMode;
  private readonly implementationMode: ImplementationMode;
  private readonly retryHandler: RetryHandler;
  private readonly config: Required<DelegationEngineConfig>;

  constructor(
    provider: LMProvider,
    expertManager?: ExpertManager,
    config?: DelegationEngineConfig
  ) {
    this.expertManager = expertManager ?? new ExpertManager();
    this.semanticRouter = new SemanticRouter(this.expertManager);
    this.advisoryMode = new AdvisoryMode(provider);
    this.implementationMode = new ImplementationMode(provider);
    this.retryHandler = new RetryHandler(config?.retry, config?.escalation);

    this.config = {
      retry: config?.retry ?? {},
      escalation: config?.escalation ?? {},
      defaultMode: config?.defaultMode ?? 'advisory',
      enableConstitutionCheck: config?.enableConstitutionCheck ?? true,
      enforceTraceability: config?.enforceTraceability ?? true,
    };
  }

  /**
   * タスクを委任
   */
  async delegate(task: DelegationTask): Promise<DelegationResult> {
    // 1. エキスパートを解決
    const expert = this.resolveExpert(task);

    // 2. 憲法チェック（有効な場合、implementationモードのみ）
    if (this.config.enableConstitutionCheck && task.mode === 'implementation') {
      const violations = this.checkConstitution(task);
      if (violations.length > 0) {
        return this.createViolationResult(expert, violations);
      }
    }

    // 3. トレーサビリティチェック（有効な場合、implementationモードのみ）
    if (
      this.config.enforceTraceability &&
      task.mode === 'implementation' &&
      !this.hasTraceability(task)
    ) {
      return this.createMissingTraceabilityResult(expert);
    }

    // 4. リトライ付きで委任を実行
    return this.retryHandler.executeWithRetry(
      () => this.executeDelegate(expert, task),
      task.id
    );
  }

  /**
   * 簡易委任（メッセージのみ）
   */
  async delegateSimple(
    message: string,
    options?: {
      expertType?: ExpertType;
      mode?: ExecutionMode;
      relatedRequirements?: string[];
      relatedDesigns?: string[];
      traceLinks?: string[];
    }
  ): Promise<DelegationResult> {
    // Convert string trace links to TraceLink objects
    const traceLinks = options?.traceLinks?.map((link) => {
      const parts = link.split('->').map((p) => p.trim());
      return {
        sourceId: parts[0] || '',
        targetId: parts[1] || '',
        type: 'traces-to' as const,
      };
    });

    const task: DelegationTask = {
      id: `task-${Date.now()}`,
      context: {
        userMessage: message,
        mode: options?.mode ?? this.config.defaultMode,
        relatedRequirements: options?.relatedRequirements,
        relatedDesigns: options?.relatedDesigns,
        traceLinks,
      },
      expertType: options?.expertType,
      mode: options?.mode ?? this.config.defaultMode,
      createdAt: new Date(),
    };

    return this.delegate(task);
  }

  /**
   * Advisory分析のみを実行
   */
  async analyze(
    message: string,
    expertType?: ExpertType
  ): Promise<DelegationResult> {
    return this.delegateSimple(message, {
      expertType,
      mode: 'advisory',
    });
  }

  /**
   * Implementation生成を実行
   */
  async generate(
    message: string,
    expertType?: ExpertType
  ): Promise<DelegationResult> {
    return this.delegateSimple(message, {
      expertType,
      mode: 'implementation',
    });
  }

  /**
   * リトライを実行
   */
  async retry(
    taskId: string,
    previousResult: DelegationResult,
    feedback?: string
  ): Promise<DelegationResult> {
    // 元のコンテキストに失敗フィードバックを追加
    const enhancedContext: DelegationContext = {
      userMessage: feedback
        ? `Previous attempt failed. Feedback: ${feedback}\n\nOriginal request: ${previousResult.content}`
        : `Previous attempt failed. Please try again with improved approach.\n\nOriginal content: ${previousResult.content}`,
      mode: previousResult.mode,
    };

    const task: DelegationTask = {
      id: taskId,
      context: enhancedContext,
      expertType: previousResult.expertType,
      mode: previousResult.mode,
      createdAt: new Date(),
    };

    return this.delegate(task);
  }

  /**
   * エスカレーションをトリガー
   */
  async escalate(
    taskId: string,
    currentExpert: ExpertType,
    context: DelegationContext
  ): Promise<DelegationResult> {
    const escalation = this.retryHandler.getEscalationTarget(currentExpert);

    if (!escalation.shouldEscalate || !escalation.targetExpert) {
      return {
        success: false,
        expertType: currentExpert,
        mode: context.mode ?? 'advisory',
        content: escalation.reason ?? 'Cannot escalate further',
        confidence: 0,
        metadata: {
          escalationFailed: true,
        },
      };
    }

    // エスカレーション先で再実行
    const task: DelegationTask = {
      id: taskId,
      context: {
        ...context,
        userMessage: `[ESCALATED from ${currentExpert}]\n\n${context.userMessage}`,
      },
      expertType: escalation.targetExpert,
      mode: context.mode,
      createdAt: new Date(),
    };

    return this.delegate(task);
  }

  /**
   * エキスパートマネージャーを取得
   */
  getExpertManager(): ExpertManager {
    return this.expertManager;
  }

  /**
   * セマンティックルーターを取得
   */
  getSemanticRouter(): SemanticRouter {
    return this.semanticRouter;
  }

  private resolveExpert(task: DelegationTask): Expert {
    // 明示的なエキスパート指定がある場合
    if (task.expertType) {
      return this.expertManager.getExpert(task.expertType);
    }

    // セマンティックルーティング
    return this.semanticRouter.resolveExpert(task.context.userMessage);
  }

  private async executeDelegate(
    expert: Expert,
    task: DelegationTask
  ): Promise<DelegationResult> {
    const mode = task.mode ?? this.config.defaultMode;

    if (mode === 'advisory') {
      return this.advisoryMode.analyze(expert, task.context);
    } else {
      return this.implementationMode.generate(expert, task.context);
    }
  }

  private checkConstitution(task: DelegationTask): ConstitutionViolation[] {
    const violations: ConstitutionViolation[] = [];

    // Article X: Implementation Prerequisites
    if (
      task.mode === 'implementation' &&
      !task.context.relatedRequirements?.length &&
      !task.context.relatedDesigns?.length
    ) {
      violations.push({
        article: 'X',
        name: 'Implementation Prerequisites',
        description:
          'Implementation requires approved requirements and design documents',
        severity: 'critical',
      });
    }

    // Article IV: EARS Format
    if (task.context.relatedRequirements) {
      const nonEarsReqs = task.context.relatedRequirements.filter(
        (r) => !this.isEarsFormat(r)
      );
      if (nonEarsReqs.length > 0) {
        violations.push({
          article: 'IV',
          name: 'EARS Format',
          description: `${nonEarsReqs.length} requirements are not in EARS format`,
          severity: 'warning',
        });
      }
    }

    // Article V: Traceability
    if (
      this.config.enforceTraceability &&
      !task.context.traceLinks?.length
    ) {
      violations.push({
        article: 'V',
        name: 'Traceability',
        description: 'No traceability links provided',
        severity: 'warning',
      });
    }

    return violations;
  }

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

  private hasTraceability(task: DelegationTask): boolean {
    return (
      (task.context.traceLinks?.length ?? 0) > 0 ||
      (task.context.relatedRequirements?.length ?? 0) > 0
    );
  }

  private createViolationResult(
    expert: Expert,
    violations: ConstitutionViolation[]
  ): DelegationResult {
    const critical = violations.filter((v) => v.severity === 'critical');

    return {
      success: false,
      expertType: expert.type,
      mode: 'advisory',
      content: `Constitution violations detected:\n${violations
        .map((v) => `- [${v.article}] ${v.name}: ${v.description}`)
        .join('\n')}`,
      confidence: 0,
      metadata: {
        constitutionViolations: violations,
        blockedByCritical: critical.length > 0,
      },
    };
  }

  private createMissingTraceabilityResult(expert: Expert): DelegationResult {
    return {
      success: false,
      expertType: expert.type,
      mode: 'advisory',
      content:
        'Traceability required: Please provide related requirements or trace links',
      confidence: 0,
      metadata: {
        missingTraceability: true,
      },
    };
  }
}

/**
 * DelegationEngineのファクトリ関数
 */
export function createDelegationEngine(
  provider: LMProvider,
  expertManager?: ExpertManager,
  config?: DelegationEngineConfig
): DelegationEngine {
  return new DelegationEngine(provider, expertManager, config);
}
