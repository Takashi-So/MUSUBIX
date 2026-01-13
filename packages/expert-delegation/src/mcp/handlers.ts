/**
 * @nahisaho/musubix-expert-delegation
 * MCP Tool Handlers
 *
 * DES-MCP-002
 * Traces to: REQ-INT-001
 */

import type { ExpertType, ExecutionMode, DelegationResult } from '../types/index.js';
import type { LMProvider } from '../types/index.js';
import { DelegationEngine } from '../delegation/delegation-engine.js';
import { SemanticRouter } from '../triggers/semantic-router.js';
import { ExpertManager } from '../experts/expert-manager.js';
import { ModelSelector } from '../providers/model-selector.js';

/**
 * MCP Tool Response
 */
export interface MCPToolResponse {
  content: Array<{
    type: 'text';
    text: string;
  }>;
  isError?: boolean;
}

/**
 * MCP Tool Handlers
 *
 * MCPツールのリクエストを処理するハンドラクラス。
 */
export class MCPToolHandlers {
  private readonly engine: DelegationEngine;
  private readonly router: SemanticRouter;
  private readonly modelSelector: ModelSelector;
  private pendingTasks: Map<string, DelegationResult> = new Map();

  constructor(
    provider: LMProvider,
    expertManager?: ExpertManager
  ) {
    const manager = expertManager ?? new ExpertManager();
    this.engine = new DelegationEngine(provider, manager);
    this.router = this.engine.getSemanticRouter();
    this.modelSelector = new ModelSelector(provider);
  }

  /**
   * expert_delegate ハンドラ
   */
  async handleExpertDelegate(args: {
    message: string;
    expert?: ExpertType;
    mode?: ExecutionMode;
    context?: Record<string, unknown>;
    relatedRequirements?: string[];
    relatedDesigns?: string[];
    traceLinks?: string[];
  }): Promise<MCPToolResponse> {
    try {
      const result = await this.engine.delegateSimple(args.message, {
        expertType: args.expert,
        mode: args.mode ?? 'advisory',
        relatedRequirements: args.relatedRequirements,
        relatedDesigns: args.relatedDesigns,
        traceLinks: args.traceLinks,
      });

      return this.formatResult(result);
    } catch (error) {
      return this.formatError(error);
    }
  }

  /**
   * expert_architect ハンドラ
   */
  async handleExpertArchitect(args: {
    message: string;
    mode?: ExecutionMode;
    constraints?: string[];
  }): Promise<MCPToolResponse> {
    try {
      const contextMessage = args.constraints
        ? `${args.message}\n\nConstraints:\n${args.constraints.map((c) => `- ${c}`).join('\n')}`
        : args.message;

      const result = await this.engine.delegateSimple(contextMessage, {
        expertType: 'architect',
        mode: args.mode ?? 'advisory',
      });

      return this.formatResult(result);
    } catch (error) {
      return this.formatError(error);
    }
  }

  /**
   * expert_security ハンドラ
   */
  async handleExpertSecurity(args: {
    code: string;
    context?: string;
    threatModel?: boolean;
  }): Promise<MCPToolResponse> {
    try {
      const message = args.threatModel
        ? `Analyze the following code for security vulnerabilities and create a threat model:\n\n\`\`\`\n${args.code}\n\`\`\`${args.context ? `\n\nContext: ${args.context}` : ''}`
        : `Analyze the following code for security vulnerabilities:\n\n\`\`\`\n${args.code}\n\`\`\`${args.context ? `\n\nContext: ${args.context}` : ''}`;

      const result = await this.engine.delegateSimple(message, {
        expertType: 'security-analyst',
        mode: 'advisory',
      });

      return this.formatResult(result);
    } catch (error) {
      return this.formatError(error);
    }
  }

  /**
   * expert_review ハンドラ
   */
  async handleExpertReview(args: {
    code: string;
    language?: string;
    focus?: string[];
  }): Promise<MCPToolResponse> {
    try {
      let message = `Review the following ${args.language ?? ''} code:\n\n\`\`\`${args.language ?? ''}\n${args.code}\n\`\`\``;

      if (args.focus && args.focus.length > 0) {
        message += `\n\nFocus areas: ${args.focus.join(', ')}`;
      }

      const result = await this.engine.delegateSimple(message, {
        expertType: 'code-reviewer',
        mode: 'advisory',
      });

      return this.formatResult(result);
    } catch (error) {
      return this.formatError(error);
    }
  }

  /**
   * expert_plan ハンドラ
   */
  async handleExpertPlan(args: {
    plan: string;
    checkConstitution?: boolean;
    validateTraceability?: boolean;
  }): Promise<MCPToolResponse> {
    try {
      let message = `Review the following plan:\n\n${args.plan}`;

      const checks: string[] = [];
      if (args.checkConstitution !== false) {
        checks.push('MUSUBIX 10 constitutional articles');
      }
      if (args.validateTraceability !== false) {
        checks.push('traceability links');
      }

      if (checks.length > 0) {
        message += `\n\nValidate against: ${checks.join(', ')}`;
      }

      const result = await this.engine.delegateSimple(message, {
        expertType: 'plan-reviewer',
        mode: 'advisory',
      });

      return this.formatResult(result);
    } catch (error) {
      return this.formatError(error);
    }
  }

  /**
   * expert_ears ハンドラ
   */
  async handleExpertEars(args: {
    requirements: string;
    suggestedPattern?: string;
    generateIds?: boolean;
  }): Promise<MCPToolResponse> {
    try {
      let message = `Convert the following requirements to EARS format:\n\n${args.requirements}`;

      if (args.suggestedPattern) {
        message += `\n\nSuggested pattern: ${args.suggestedPattern}`;
      }

      if (args.generateIds !== false) {
        message += '\n\nGenerate unique requirement IDs (REQ-XXX-NNN format).';
      }

      const result = await this.engine.delegateSimple(message, {
        expertType: 'ears-analyst',
        mode: 'advisory',
      });

      return this.formatResult(result);
    } catch (error) {
      return this.formatError(error);
    }
  }

  /**
   * expert_formal ハンドラ
   */
  async handleExpertFormal(args: {
    code: string;
    specification?: string;
    outputFormat?: 'z3' | 'lean4' | 'hoare';
  }): Promise<MCPToolResponse> {
    try {
      const format = args.outputFormat ?? 'z3';
      let message = `Formally verify the following code:\n\n\`\`\`\n${args.code}\n\`\`\``;

      if (args.specification) {
        message += `\n\nSpecification:\n${args.specification}`;
      }

      message += `\n\nOutput format: ${format}`;

      const result = await this.engine.delegateSimple(message, {
        expertType: 'formal-verifier',
        mode: 'advisory',
      });

      return this.formatResult(result);
    } catch (error) {
      return this.formatError(error);
    }
  }

  /**
   * expert_ontology ハンドラ
   */
  async handleExpertOntology(args: {
    query: string;
    triples?: Array<{ s: string; p: string; o: string }>;
    checkConsistency?: boolean;
  }): Promise<MCPToolResponse> {
    try {
      let message = `Ontology reasoning query:\n\n${args.query}`;

      if (args.triples && args.triples.length > 0) {
        message += `\n\nContext knowledge:\n${args.triples
          .map((t) => `${t.s} ${t.p} ${t.o} .`)
          .join('\n')}`;
      }

      if (args.checkConsistency) {
        message += '\n\nAlso check knowledge graph consistency.';
      }

      const result = await this.engine.delegateSimple(message, {
        expertType: 'ontology-reasoner',
        mode: 'advisory',
      });

      return this.formatResult(result);
    } catch (error) {
      return this.formatError(error);
    }
  }

  /**
   * trigger_detect ハンドラ
   */
  async handleTriggerDetect(args: {
    message: string;
  }): Promise<MCPToolResponse> {
    try {
      const intent = this.router.detectIntent(args.message);

      return {
        content: [
          {
            type: 'text',
            text: JSON.stringify(
              {
                detected: intent.detected,
                expert: intent.expert,
                confidence: intent.confidence,
                matchedPattern: intent.matchedPattern,
                language: intent.language,
              },
              null,
              2
            ),
          },
        ],
      };
    } catch (error) {
      return this.formatError(error);
    }
  }

  /**
   * delegation_retry ハンドラ
   */
  async handleDelegationRetry(args: {
    taskId: string;
    feedback?: string;
  }): Promise<MCPToolResponse> {
    try {
      const previousResult = this.pendingTasks.get(args.taskId);

      if (!previousResult) {
        return {
          content: [
            {
              type: 'text',
              text: `Task not found: ${args.taskId}`,
            },
          ],
          isError: true,
        };
      }

      const result = await this.engine.retry(
        args.taskId,
        previousResult,
        args.feedback
      );

      // 結果を更新
      this.pendingTasks.set(args.taskId, result);

      return this.formatResult(result);
    } catch (error) {
      return this.formatError(error);
    }
  }

  /**
   * provider_select ハンドラ
   */
  async handleProviderSelect(args: {
    criteria?: {
      family?: string;
      version?: string;
    };
    temperature?: number;
  }): Promise<MCPToolResponse> {
    try {
      const models = await this.modelSelector.selectModel(args.criteria);

      return {
        content: [
          {
            type: 'text',
            text: JSON.stringify(
              {
                selectedModel: models,
                temperature: args.temperature ?? 0.3,
                status: 'ready',
              },
              null,
              2
            ),
          },
        ],
      };
    } catch (error) {
      return this.formatError(error);
    }
  }

  /**
   * タスク結果を保存（リトライ用）
   */
  saveTaskResult(taskId: string, result: DelegationResult): void {
    this.pendingTasks.set(taskId, result);
  }

  /**
   * タスク結果をクリア
   */
  clearTaskResult(taskId: string): void {
    this.pendingTasks.delete(taskId);
  }

  private formatResult(result: DelegationResult): MCPToolResponse {
    return {
      content: [
        {
          type: 'text',
          text: result.content,
        },
      ],
      isError: !result.success,
    };
  }

  private formatError(error: unknown): MCPToolResponse {
    const message =
      error instanceof Error ? error.message : 'Unknown error occurred';

    return {
      content: [
        {
          type: 'text',
          text: `Error: ${message}`,
        },
      ],
      isError: true,
    };
  }
}

/**
 * MCPToolHandlersのファクトリ関数
 */
export function createMCPToolHandlers(
  provider: LMProvider,
  expertManager?: ExpertManager
): MCPToolHandlers {
  return new MCPToolHandlers(provider, expertManager);
}
