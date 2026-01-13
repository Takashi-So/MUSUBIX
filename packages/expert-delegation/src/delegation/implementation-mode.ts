/**
 * @nahisaho/musubix-expert-delegation
 * Implementation Mode
 *
 * DES-DEL-003
 * Traces to: REQ-DEL-002
 */

import type {
  Expert,
  DelegationContext,
  DelegationResult,
  TraceLink,
} from '../types/index.js';
import type { LMProvider } from '../types/index.js';
import { PromptBuilder } from './prompt-builder.js';

/**
 * 生成されたコードブロック
 */
interface CodeBlock {
  language: string;
  filename?: string;
  content: string;
  traceLinks: TraceLink[];
}

/**
 * Implementation Mode Handler
 *
 * コード生成を行う実装モード。
 * トレーサビリティコメントを自動挿入する。
 */
export class ImplementationMode {
  private readonly promptBuilder: PromptBuilder;

  constructor(private readonly provider: LMProvider) {
    this.promptBuilder = new PromptBuilder();
  }

  /**
   * Implementation生成を実行
   */
  async generate(
    expert: Expert,
    context: DelegationContext
  ): Promise<DelegationResult> {
    // コンテキストにimplementationモードを設定
    const implContext: DelegationContext = {
      ...context,
      mode: 'implementation',
    };

    // プロンプト構築
    const prompt = this.promptBuilder.build(expert, implContext);

    // Implementation用のシステムプロンプト追加
    const systemPrompt = this.buildImplementationSystemPrompt(expert, context);

    // LLM実行
    const response = await this.provider.sendRequest({
      messages: [
        { role: 'system', content: systemPrompt },
        { role: 'user', content: prompt },
      ],
      temperature: 0.4, // コード生成は中程度の温度
    });

    // 結果をパース
    return this.parseImplementationResponse(expert, response.content, context);
  }

  /**
   * 形式検証付きコード生成
   */
  async generateWithVerification(
    expert: Expert,
    context: DelegationContext,
    specification: string
  ): Promise<DelegationResult> {
    // まず通常のコード生成
    const result = await this.generate(expert, context);

    if (!result.success) {
      return result;
    }

    // 形式検証プロンプトを追加
    const verificationPrompt =
      this.promptBuilder.buildFormalVerificationPrompt(
        result.content,
        specification
      );

    const verificationResponse = await this.provider.sendRequest({
      messages: [
        {
          role: 'system',
          content:
            'You are a formal verification expert. Verify the generated code.',
        },
        { role: 'user', content: verificationPrompt },
      ],
      temperature: 0.2,
    });

    // 検証結果をメタデータに追加
    return {
      ...result,
      metadata: {
        ...result.metadata,
        verification: verificationResponse.content,
        verified: verificationResponse.content.includes('PASS'),
      },
    };
  }

  /**
   * コードブロックを抽出
   */
  extractCodeBlocks(content: string): CodeBlock[] {
    const blocks: CodeBlock[] = [];
    const codeBlockRegex =
      /```(\w+)?(?:\s+(\S+))?\n([\s\S]*?)```/g;

    let match: RegExpExecArray | null;
    while ((match = codeBlockRegex.exec(content)) !== null) {
      const language = match[1] ?? 'text';
      const filename = match[2];
      const code = match[3];

      // トレースリンクを抽出
      const traceLinks = this.extractTraceLinks(code);

      blocks.push({
        language,
        filename,
        content: code,
        traceLinks,
      });
    }

    return blocks;
  }

  /**
   * トレーサビリティコメントを挿入
   */
  injectTraceability(
    code: string,
    language: string,
    requirementId: string
  ): string {
    const commentStyle = this.getCommentStyle(language);

    // ファイルヘッダーにトレースコメントを追加
    const header = `${commentStyle.start} Traces to: ${requirementId} ${commentStyle.end}\n`;

    // すでにトレースコメントがある場合は追加しない
    if (code.includes(`Traces to: ${requirementId}`)) {
      return code;
    }

    return header + code;
  }

  private buildImplementationSystemPrompt(
    expert: Expert,
    context: DelegationContext
  ): string {
    const traceIds = context.traceLinks
      ?.map((l) => l.sourceId)
      .join(', ') ?? 'N/A';

    return `${expert.systemPrompt}

## Mode: Implementation (Code Generation)

IMPORTANT REQUIREMENTS:
1. Generate production-ready code
2. Include traceability comments: // Traces to: [ID]
3. Follow project coding standards
4. Add comprehensive inline documentation
5. Ensure type safety and error handling

Traceability IDs: ${traceIds}

Code Quality Requirements:
- Use TypeScript strict mode compatible code
- Include JSDoc comments for public APIs
- Follow SOLID principles
- Implement proper error handling
- Add validation for inputs

Output Format:
Provide code blocks with language specification and optional filename:
\`\`\`typescript filename.ts
// Traces to: REQ-XXX
// code here
\`\`\``;
  }

  private parseImplementationResponse(
    expert: Expert,
    content: string,
    _context: DelegationContext
  ): DelegationResult {
    // コードブロックを抽出
    const codeBlocks = this.extractCodeBlocks(content);

    // 信頼度を計算
    const hasTraceability = codeBlocks.some((b) => b.traceLinks.length > 0);
    const hasProperTypes = content.includes(': string') ||
      content.includes(': number') ||
      content.includes('interface ') ||
      content.includes('type ');
    const hasErrorHandling = content.includes('try') ||
      content.includes('catch') ||
      content.includes('throw') ||
      content.includes('Result<');

    let confidence = 0.6;
    if (hasTraceability) confidence += 0.15;
    if (hasProperTypes) confidence += 0.15;
    if (hasErrorHandling) confidence += 0.1;

    return {
      success: true,
      expertType: expert.type,
      mode: 'implementation',
      content,
      confidence: Math.min(1, confidence),
      metadata: {
        codeBlockCount: codeBlocks.length,
        hasTraceability,
        hasProperTypes,
        hasErrorHandling,
        extractedFiles: codeBlocks
          .filter((b) => b.filename)
          .map((b) => b.filename),
      },
    };
  }

  private extractTraceLinks(code: string): TraceLink[] {
    const links: TraceLink[] = [];
    const traceRegex = /Traces?\s+to:\s*([\w-]+)/gi;

    let match: RegExpExecArray | null;
    while ((match = traceRegex.exec(code)) !== null) {
      links.push({
        sourceId: match[1],
        targetId: 'generated-code',
        type: 'traces-to',
      });
    }

    return links;
  }

  private getCommentStyle(language: string): {
    start: string;
    end: string;
  } {
    switch (language.toLowerCase()) {
      case 'typescript':
      case 'javascript':
      case 'java':
      case 'c':
      case 'cpp':
      case 'rust':
      case 'go':
        return { start: '//', end: '' };
      case 'python':
      case 'ruby':
      case 'yaml':
      case 'bash':
      case 'sh':
        return { start: '#', end: '' };
      case 'html':
      case 'xml':
        return { start: '<!--', end: '-->' };
      case 'css':
        return { start: '/*', end: '*/' };
      default:
        return { start: '//', end: '' };
    }
  }
}

/**
 * ImplementationModeのファクトリ関数
 */
export function createImplementationMode(
  provider: LMProvider
): ImplementationMode {
  return new ImplementationMode(provider);
}
