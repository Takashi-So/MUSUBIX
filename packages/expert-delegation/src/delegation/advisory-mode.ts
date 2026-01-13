/**
 * @nahisaho/musubix-expert-delegation
 * Advisory Mode
 *
 * DES-DEL-002
 * Traces to: REQ-DEL-002
 */

import type {
  Expert,
  DelegationContext,
  DelegationResult,
} from '../types/index.js';
import type { LMProvider } from '../types/index.js';
import { PromptBuilder } from './prompt-builder.js';

/**
 * Advisory Mode Handler
 *
 * 読み取り専用の分析・推奨モード。
 * コードを直接生成せず、分析結果と推奨事項を提供する。
 */
export class AdvisoryMode {
  private readonly promptBuilder: PromptBuilder;

  constructor(private readonly provider: LMProvider) {
    this.promptBuilder = new PromptBuilder();
  }

  /**
   * Advisory分析を実行
   */
  async analyze(
    expert: Expert,
    context: DelegationContext
  ): Promise<DelegationResult> {
    // コンテキストにadvisoryモードを設定
    const advisoryContext: DelegationContext = {
      ...context,
      mode: 'advisory',
    };

    // プロンプト構築
    const prompt = this.promptBuilder.build(expert, advisoryContext);

    // Advisory用のシステムプロンプト追加
    const systemPrompt = this.buildAdvisorySystemPrompt(expert);

    // LLM実行
    const response = await this.provider.sendRequest({
      messages: [
        { role: 'system', content: systemPrompt },
        { role: 'user', content: prompt },
      ],
      temperature: 0.3, // 低温度で一貫性を重視
    });

    // 結果をパース
    return this.parseAdvisoryResponse(expert, response.content);
  }

  /**
   * セキュリティ分析に特化したAdvisory
   */
  async analyzeSecurityOnly(
    code: string,
    expert: Expert
  ): Promise<DelegationResult> {
    const context: DelegationContext = {
      userMessage: `Analyze the following code for security vulnerabilities:\n\n\`\`\`\n${code}\n\`\`\``,
      mode: 'advisory',
      activeFiles: [{ path: 'input', content: code }],
    };

    return this.analyze(expert, context);
  }

  /**
   * EARS要件分析に特化したAdvisory
   */
  async analyzeRequirements(
    requirementText: string,
    expert: Expert
  ): Promise<DelegationResult> {
    const prompt = this.promptBuilder.buildEarsAnalysisPrompt(requirementText);

    const systemPrompt = this.buildAdvisorySystemPrompt(expert);

    const response = await this.provider.sendRequest({
      messages: [
        { role: 'system', content: systemPrompt },
        { role: 'user', content: prompt },
      ],
      temperature: 0.2,
    });

    return this.parseAdvisoryResponse(expert, response.content);
  }

  /**
   * オントロジー推論に特化したAdvisory
   */
  async analyzeOntology(
    query: string,
    expert: Expert,
    contextTriples?: Array<{ s: string; p: string; o: string }>
  ): Promise<DelegationResult> {
    const prompt = this.promptBuilder.buildOntologyReasoningPrompt(
      query,
      contextTriples
    );

    const systemPrompt = this.buildAdvisorySystemPrompt(expert);

    const response = await this.provider.sendRequest({
      messages: [
        { role: 'system', content: systemPrompt },
        { role: 'user', content: prompt },
      ],
      temperature: 0.2,
    });

    return this.parseAdvisoryResponse(expert, response.content);
  }

  private buildAdvisorySystemPrompt(expert: Expert): string {
    return `${expert.systemPrompt}

## Mode: Advisory (Read-Only)

IMPORTANT CONSTRAINTS:
1. Do NOT generate implementation code
2. Focus on analysis, recommendations, and explanations
3. Provide actionable insights
4. Highlight risks and trade-offs
5. Reference relevant best practices and patterns

Output Format:
1. Summary - Brief overview of findings
2. Analysis - Detailed examination
3. Recommendations - Prioritized action items
4. Risks - Potential issues to consider
5. References - Related patterns, standards, or resources`;
  }

  private parseAdvisoryResponse(
    expert: Expert,
    content: string
  ): DelegationResult {
    // 信頼度を抽出（あれば）
    const confidenceMatch = content.match(/confidence[:\s]+(\d+(?:\.\d+)?)/i);
    const confidence = confidenceMatch
      ? parseFloat(confidenceMatch[1])
      : 0.8;

    // セクションを抽出
    const summaryMatch = content.match(
      /(?:^|\n)##?\s*summary\s*\n([\s\S]*?)(?=\n##?\s|\n---|\n\*\*|$)/i
    );
    const recommendationsMatch = content.match(
      /(?:^|\n)##?\s*recommendations?\s*\n([\s\S]*?)(?=\n##?\s|\n---|\n\*\*|$)/i
    );

    return {
      success: true,
      expertType: expert.type,
      mode: 'advisory',
      content,
      confidence: Math.min(1, Math.max(0, confidence)),
      metadata: {
        hasSummary: !!summaryMatch,
        hasRecommendations: !!recommendationsMatch,
        contentLength: content.length,
      },
    };
  }
}

/**
 * AdvisoryModeのファクトリ関数
 */
export function createAdvisoryMode(provider: LMProvider): AdvisoryMode {
  return new AdvisoryMode(provider);
}
