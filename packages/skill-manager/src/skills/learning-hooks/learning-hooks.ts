/**
 * Learning Hooks Implementation
 *
 * REQ-LH-001: Continuous Learning Evaluation
 * REQ-LH-002: Learned Skills Storage
 * REQ-LH-003: Pattern Ignore List
 *
 * @packageDocumentation
 */

import * as path from 'path';
import * as os from 'os';
import {
  type ConversationMessage,
  DEFAULT_EXTRACTION_CONFIG,
  DEFAULT_IGNORE_PATTERNS,
  type ErrorResolutionFlow,
  type ExtractionConfig,
  type ExtractionResult,
  type ExtractedPattern,
  type IgnorePattern,
  type LearningHooksManager,
  type LearningReport,
  type PatternAnalysisResult,
  type PatternCandidate,
  type PatternType,
  type UserCorrectionFlow,
} from './types.js';

/**
 * パターンIDを生成
 */
function generatePatternId(type: PatternType, description: string): string {
  const slug = description
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '')
    .slice(0, 30);
  const timestamp = Date.now().toString(36).slice(-4);
  return `${type}-${slug}-${timestamp}`;
}

/**
 * パターン名を生成
 */
function generatePatternName(type: PatternType, problem: string): string {
  const shortProblem = problem
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '')
    .slice(0, 40);
  return `${type}-${shortProblem}`;
}

/**
 * エラーパターンを検出
 */
function detectErrorPatterns(content: string): boolean {
  const errorPatterns = [
    /error/i,
    /Error:/,
    /TypeError/,
    /SyntaxError/,
    /ReferenceError/,
    /failed/i,
    /exception/i,
    /TS\d{4,5}/,
    /✖|✗|❌/,
  ];
  return errorPatterns.some((p) => p.test(content));
}

/**
 * 修正指示パターンを検出
 */
function detectCorrectionPatterns(content: string): boolean {
  const correctionPatterns = [
    /修正/,
    /変更/,
    /直して/,
    /instead/i,
    /should be/i,
    /change.*to/i,
    /fix/i,
    /correct/i,
    /ではなく/,
    /じゃなくて/,
  ];
  return correctionPatterns.some((p) => p.test(content));
}

/**
 * コードブロックを検出
 */
function detectCodeBlock(content: string): boolean {
  return /```[\s\S]*?```/.test(content) || /`[^`]+`/.test(content);
}

/**
 * 会話メッセージを分析
 */
function analyzeMessages(
  messages: ConversationMessage[]
): PatternAnalysisResult {
  const errorResolutionFlows: ErrorResolutionFlow[] = [];
  const userCorrectionFlows: UserCorrectionFlow[] = [];
  const debuggingTechniques: string[] = [];
  const projectSpecificCandidates: string[] = [];

  // エラー解決フローの検出
  for (let i = 0; i < messages.length - 1; i++) {
    const msg = messages[i];
    if (msg.containsError) {
      // エラー後に修正があるか探索
      for (let j = i + 1; j < Math.min(i + 5, messages.length); j++) {
        const nextMsg = messages[j];
        if (nextMsg.role === 'assistant' && nextMsg.containsCode) {
          // 修正後にエラーが消えたか確認
          const hasResolution =
            j + 1 < messages.length &&
            !messages[j + 1].containsError &&
            (messages[j + 1].content.includes('成功') ||
              messages[j + 1].content.includes('OK') ||
              messages[j + 1].content.includes('passed') ||
              messages[j + 1].content.includes('✅'));

          errorResolutionFlows.push({
            errorMessageIndex: i,
            fixActionIndex: j,
            resolutionIndex: hasResolution ? j + 1 : undefined,
            errorContent: msg.content.slice(0, 500),
            fixContent: nextMsg.content.slice(0, 500),
          });
          break;
        }
      }
    }
  }

  // ユーザー修正フローの検出
  for (let i = 0; i < messages.length - 1; i++) {
    const msg = messages[i];
    if (msg.role === 'assistant' && msg.containsCode) {
      // 次のユーザーメッセージが修正指示か
      const nextUserMsg = messages.find(
        (m, idx) => idx > i && m.role === 'user'
      );
      if (nextUserMsg?.containsCorrection) {
        const nextUserIdx = messages.indexOf(nextUserMsg);
        // 修正後に承認があるか
        const approvalMsg = messages.find(
          (m, idx) =>
            idx > nextUserIdx &&
            m.role === 'user' &&
            (m.content.includes('承認') ||
              m.content.includes('OK') ||
              m.content.includes('LGTM'))
        );

        userCorrectionFlows.push({
          aiProposalIndex: i,
          userCorrectionIndex: nextUserIdx,
          approvalIndex: approvalMsg ? messages.indexOf(approvalMsg) : undefined,
          originalProposal: msg.content.slice(0, 500),
          correctionContent: nextUserMsg.content.slice(0, 500),
        });
      }
    }
  }

  // デバッグ技法の検出
  const debugPatterns = [
    /console\.log|console\.debug/,
    /debugger/,
    /breakpoint/,
    /step.*through/i,
    /inspect.*variable/i,
    /trace/i,
  ];
  for (const msg of messages) {
    if (msg.role === 'assistant') {
      for (const pattern of debugPatterns) {
        if (pattern.test(msg.content)) {
          debuggingTechniques.push(msg.content.slice(0, 200));
          break;
        }
      }
    }
  }

  // プロジェクト固有パターンの検出（命名規則、アーキテクチャ言及）
  const projectPatterns = [
    /REQ-|DES-|TSK-/,
    /EARS/,
    /憲法|constitution/i,
    /steering\//,
    /packages\//,
  ];
  for (const msg of messages) {
    for (const pattern of projectPatterns) {
      if (pattern.test(msg.content)) {
        projectSpecificCandidates.push(msg.content.slice(0, 200));
        break;
      }
    }
  }

  return {
    errorResolutionFlows,
    userCorrectionFlows,
    debuggingTechniques,
    projectSpecificCandidates,
  };
}

/**
 * 信頼度を計算
 */
function calculateConfidence(candidate: PatternCandidate): number {
  let confidence = 0.5; // ベース信頼度

  // メッセージ数による加算
  if (candidate.messageIndices.length >= 3) {
    confidence += 0.1;
  }
  if (candidate.messageIndices.length >= 5) {
    confidence += 0.1;
  }

  // コード例がある場合
  if (candidate.codeExample) {
    confidence += 0.15;
  }

  // 解決策の具体性
  if (candidate.solution.length > 100) {
    confidence += 0.1;
  }

  // 問題の明確性
  if (candidate.problem.length > 50) {
    confidence += 0.05;
  }

  return Math.min(confidence, 1.0);
}

/**
 * パターン候補を生成
 */
function generateCandidates(
  analysis: PatternAnalysisResult
): PatternCandidate[] {
  const candidates: PatternCandidate[] = [];

  // エラー解決パターン
  for (const flow of analysis.errorResolutionFlows) {
    const candidate: PatternCandidate = {
      type: 'error_resolution',
      problem: flow.errorContent,
      solution: flow.fixContent,
      messageIndices: [
        flow.errorMessageIndex,
        flow.fixActionIndex,
        ...(flow.resolutionIndex !== undefined ? [flow.resolutionIndex] : []),
      ],
      tentativeConfidence: flow.resolutionIndex !== undefined ? 0.8 : 0.6,
      codeExample: extractCodeBlock(flow.fixContent),
    };
    candidates.push(candidate);
  }

  // ユーザー修正パターン
  for (const flow of analysis.userCorrectionFlows) {
    const candidate: PatternCandidate = {
      type: 'user_corrections',
      problem: `AI proposed: ${flow.originalProposal.slice(0, 100)}`,
      solution: flow.correctionContent,
      messageIndices: [
        flow.aiProposalIndex,
        flow.userCorrectionIndex,
        ...(flow.approvalIndex !== undefined ? [flow.approvalIndex] : []),
      ],
      tentativeConfidence: flow.approvalIndex !== undefined ? 0.85 : 0.65,
    };
    candidates.push(candidate);
  }

  return candidates;
}

/**
 * コードブロックを抽出
 */
function extractCodeBlock(content: string): string | undefined {
  const match = content.match(/```(?:\w+)?\s*([\s\S]*?)```/);
  return match ? match[1].trim() : undefined;
}

/**
 * セッション時間を人間可読形式に変換
 */
function formatDuration(minutes: number): string {
  if (minutes < 60) {
    return `${minutes}分`;
  }
  const hours = Math.floor(minutes / 60);
  const mins = minutes % 60;
  return mins > 0 ? `${hours}時間${mins}分` : `${hours}時間`;
}

/**
 * スキルファイルを生成
 */
function generateSkillFileContent(pattern: ExtractedPattern): string {
  const codeSection = pattern.codeExample
    ? `
## Example

\`\`\`typescript
${pattern.codeExample}
\`\`\`
`
    : '';

  const relatedSection =
    pattern.relatedPatterns.length > 0
      ? `
## Related Patterns

${pattern.relatedPatterns.map((p) => `- ${p}`).join('\n')}
`
      : '';

  return `---
name: ${pattern.name}
description: |
  ${pattern.description}
extracted: ${pattern.extractedAt.toISOString().split('T')[0]}
confidence: ${pattern.confidence.toFixed(2)}
type: ${pattern.type}
source_session: ${pattern.sourceSessionId}
---

# ${pattern.name.replace(/-/g, ' ').replace(/\b\w/g, (c) => c.toUpperCase())}

**Extracted:** ${pattern.extractedAt.toISOString().split('T')[0]}
**Confidence:** ${pattern.confidence.toFixed(2)}
**Context:** ${pattern.type.replace(/_/g, ' ')}

## Problem

${pattern.problem}

## Solution

${pattern.solution}
${codeSection}
## When to Use

${pattern.whenToUse.map((w) => `- ${w}`).join('\n')}
${relatedSection}`;
}

/**
 * Learning Hooks Manager を作成
 * REQ-LH-001〜003: 継続的学習の全機能を提供
 */
export function createLearningHooksManager(
  config: Partial<ExtractionConfig> = {}
): LearningHooksManager {
  const mergedConfig: ExtractionConfig = {
    ...DEFAULT_EXTRACTION_CONFIG,
    ...config,
  };

  const ignorePatterns: IgnorePattern[] = [...DEFAULT_IGNORE_PATTERNS];

  return {
    shouldExtract(messageCount: number, sessionMinutes: number): boolean {
      if (!mergedConfig.enableAutoExtraction) {
        return false;
      }
      return (
        messageCount >= mergedConfig.minMessages &&
        sessionMinutes >= mergedConfig.minSessionMinutes
      );
    },

    extractPatterns(
      messages: ConversationMessage[],
      sessionId: string
    ): ExtractionResult {
      const startTime = messages[0]?.timestamp ?? new Date();
      const endTime = messages[messages.length - 1]?.timestamp ?? new Date();
      const sessionMinutes = Math.floor(
        (endTime.getTime() - startTime.getTime()) / 60000
      );

      // メッセージにメタデータを追加
      const enrichedMessages = messages.map((msg) => ({
        ...msg,
        containsError: detectErrorPatterns(msg.content),
        containsCorrection: detectCorrectionPatterns(msg.content),
        containsCode: detectCodeBlock(msg.content),
      }));

      // 分析実行
      const analysis = analyzeMessages(enrichedMessages);

      // パターン候補生成
      const candidates = generateCandidates(analysis);

      // 信頼度計算と除外チェック
      const extractedPatterns: ExtractedPattern[] = [];
      const skippedPatterns: Array<{
        candidate: PatternCandidate;
        reason: string;
      }> = [];

      for (const candidate of candidates) {
        const ignoreResult = this.shouldIgnore(candidate);
        if (ignoreResult.ignore) {
          skippedPatterns.push({ candidate, reason: ignoreResult.reason! });
          continue;
        }

        const confidence = calculateConfidence(candidate);
        if (confidence < mergedConfig.confidenceThreshold) {
          skippedPatterns.push({
            candidate,
            reason: `信頼度が閾値未満: ${confidence.toFixed(2)} < ${mergedConfig.confidenceThreshold}`,
          });
          continue;
        }

        if (extractedPatterns.length >= mergedConfig.maxPatternsPerSession) {
          skippedPatterns.push({
            candidate,
            reason: `最大パターン数に達した: ${mergedConfig.maxPatternsPerSession}`,
          });
          continue;
        }

        const patternName = generatePatternName(candidate.type, candidate.problem);
        const pattern: ExtractedPattern = {
          id: generatePatternId(candidate.type, candidate.problem),
          name: patternName,
          description: `${candidate.type.replace(/_/g, ' ')} pattern extracted from session`,
          type: candidate.type,
          confidence,
          problem: candidate.problem,
          solution: candidate.solution,
          codeExample: candidate.codeExample,
          whenToUse: [`When encountering similar ${candidate.type.replace(/_/g, ' ')} issues`],
          relatedPatterns: [],
          sourceSessionId: sessionId,
          extractedAt: new Date(),
        };

        extractedPatterns.push(pattern);
      }

      return {
        sessionId,
        extractedPatterns,
        skippedPatterns,
        messageCount: messages.length,
        sessionMinutes,
        extractedAt: new Date(),
      };
    },

    shouldIgnore(
      candidate: PatternCandidate
    ): { ignore: boolean; reason?: string } {
      const combinedContent = `${candidate.problem} ${candidate.solution}`;

      for (const ignorePattern of ignorePatterns) {
        if (ignorePattern.pattern.test(combinedContent)) {
          return {
            ignore: true,
            reason: `${ignorePattern.category}: ${ignorePattern.reason}`,
          };
        }
      }

      return { ignore: false };
    },

    saveAsSkill(pattern: ExtractedPattern): string {
      const skillDir = path.join(
        os.homedir(),
        '.musubix',
        'skills',
        'learned',
        pattern.name
      );
      const skillPath = path.join(skillDir, 'SKILL.md');
      const content = generateSkillFileContent(pattern);

      // 実際のファイル書き込みは呼び出し側で実行
      // ここではパスと内容を返す
      return `${skillPath}\n---\n${content}`;
    },

    generateReport(result: ExtractionResult): LearningReport {
      const skippedCounts: Record<string, number> = {};
      for (const { reason } of result.skippedPatterns) {
        const category = reason.split(':')[0] ?? 'other';
        skippedCounts[category] = (skippedCounts[category] ?? 0) + 1;
      }

      return {
        sessionId: result.sessionId,
        messageCount: result.messageCount,
        sessionDuration: formatDuration(result.sessionMinutes),
        extractedPatterns: result.extractedPatterns.map((p) => ({
          name: p.name,
          type: p.type,
          confidence: p.confidence,
          summary: p.description,
        })),
        skippedCounts,
        generatedAt: new Date(),
      };
    },

    formatReportAsMarkdown(report: LearningReport): string {
      const patternsSection =
        report.extractedPatterns.length > 0
          ? `## 抽出されたパターン

${report.extractedPatterns
  .map(
    (p, i) => `${i + 1}. **${p.name}** (信頼度: ${p.confidence.toFixed(2)})
   - ${p.summary}`
  )
  .join('\n\n')}`
          : '## 抽出されたパターン\n\nなし';

      const skippedSection =
        Object.keys(report.skippedCounts).length > 0
          ? `## スキップされたパターン

${Object.entries(report.skippedCounts)
  .map(([category, count]) => `- ${category}: ${count}件`)
  .join('\n')}`
          : '';

      return `📊 **学習レポート**

**セッション**: ${report.sessionId}
**メッセージ数**: ${report.messageCount}
**セッション時間**: ${report.sessionDuration}

${patternsSection}
${skippedSection}

保存を続行しますか？`;
    },

    getConfig(): ExtractionConfig {
      return { ...mergedConfig };
    },

    getIgnorePatterns(): readonly IgnorePattern[] {
      return [...ignorePatterns];
    },

    addIgnorePattern(pattern: IgnorePattern): void {
      ignorePatterns.push(pattern);
    },
  };
}

/**
 * 会話メッセージを作成するヘルパー
 */
export function createConversationMessage(
  index: number,
  role: 'user' | 'assistant',
  content: string,
  timestamp: Date = new Date()
): ConversationMessage {
  return {
    index,
    role,
    content,
    timestamp,
    containsError: detectErrorPatterns(content),
    containsCorrection: detectCorrectionPatterns(content),
    containsCode: detectCodeBlock(content),
  };
}

/**
 * 学習レポートをフォーマット（外部利用用）
 */
export function formatLearningReport(report: LearningReport): string {
  const manager = createLearningHooksManager();
  return manager.formatReportAsMarkdown(report);
}
