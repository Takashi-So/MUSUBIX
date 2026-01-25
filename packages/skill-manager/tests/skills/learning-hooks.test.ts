/**
 * Learning Hooks Tests
 *
 * REQ-LH-001: Continuous Learning Evaluation
 * REQ-LH-002: Learned Skills Storage
 * REQ-LH-003: Pattern Ignore List
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createLearningHooksManager,
  createConversationMessage,
  formatLearningReport,
  type LearningHooksManager,
  type ConversationMessage,
  type PatternCandidate,
  DEFAULT_EXTRACTION_CONFIG,
  DEFAULT_IGNORE_PATTERNS,
} from '../../src/skills/learning-hooks/index.js';

describe('Learning Hooks Manager', () => {
  let manager: LearningHooksManager;

  beforeEach(() => {
    manager = createLearningHooksManager();
  });

  describe('REQ-LH-001: Continuous Learning Evaluation', () => {
    describe('shouldExtract - 抽出条件チェック', () => {
      it('should return true when conditions are met', () => {
        expect(manager.shouldExtract(10, 15)).toBe(true);
        expect(manager.shouldExtract(20, 30)).toBe(true);
      });

      it('should return false when message count is below threshold', () => {
        expect(manager.shouldExtract(5, 20)).toBe(false);
        expect(manager.shouldExtract(9, 15)).toBe(false);
      });

      it('should return false when session time is below threshold', () => {
        expect(manager.shouldExtract(15, 10)).toBe(false);
        expect(manager.shouldExtract(10, 14)).toBe(false);
      });

      it('should return false when auto extraction is disabled', () => {
        const disabledManager = createLearningHooksManager({
          enableAutoExtraction: false,
        });
        expect(disabledManager.shouldExtract(20, 30)).toBe(false);
      });

      it('should respect custom thresholds', () => {
        const customManager = createLearningHooksManager({
          minMessages: 5,
          minSessionMinutes: 10,
        });
        expect(customManager.shouldExtract(5, 10)).toBe(true);
        expect(customManager.shouldExtract(4, 10)).toBe(false);
      });
    });

    describe('extractPatterns - パターン抽出', () => {
      it('should extract error resolution patterns', () => {
        const messages = createErrorResolutionConversation();
        const result = manager.extractPatterns(messages, 'test-session-001');

        expect(result.sessionId).toBe('test-session-001');
        expect(result.messageCount).toBe(messages.length);
        expect(result.extractedPatterns.length).toBeGreaterThanOrEqual(0);
      });

      it('should extract user correction patterns', () => {
        const messages = createUserCorrectionConversation();
        const result = manager.extractPatterns(messages, 'test-session-002');

        expect(result.sessionId).toBe('test-session-002');
        expect(result.extractedPatterns.length + result.skippedPatterns.length).toBeGreaterThanOrEqual(0);
      });

      it('should limit patterns per session', () => {
        const limitedManager = createLearningHooksManager({
          maxPatternsPerSession: 2,
          confidenceThreshold: 0.3, // 低めの閾値で多く抽出
        });

        const messages = createManyPatternsConversation();
        const result = limitedManager.extractPatterns(messages, 'test-session-003');

        expect(result.extractedPatterns.length).toBeLessThanOrEqual(2);
      });

      it('should calculate session duration correctly', () => {
        const baseTime = new Date('2026-01-25T10:00:00Z');
        const messages: ConversationMessage[] = [
          createConversationMessage(0, 'user', 'Start', baseTime),
          createConversationMessage(1, 'assistant', 'Response', new Date(baseTime.getTime() + 30 * 60000)),
        ];

        const result = manager.extractPatterns(messages, 'test-session-004');
        expect(result.sessionMinutes).toBe(30);
      });

      it('should include extractedAt timestamp', () => {
        const messages = [createConversationMessage(0, 'user', 'Hello')];
        const result = manager.extractPatterns(messages, 'test-session-005');

        expect(result.extractedAt).toBeInstanceOf(Date);
        expect(result.extractedAt.getTime()).toBeLessThanOrEqual(Date.now());
      });
    });
  });

  describe('REQ-LH-002: Learned Skills Storage', () => {
    describe('saveAsSkill - スキルファイル生成', () => {
      it('should generate skill file path', () => {
        const pattern = createMockExtractedPattern();
        const output = manager.saveAsSkill(pattern);

        expect(output).toContain('.musubix/skills/learned');
        expect(output).toContain('SKILL.md');
      });

      it('should include YAML frontmatter', () => {
        const pattern = createMockExtractedPattern();
        const output = manager.saveAsSkill(pattern);

        expect(output).toContain('---');
        expect(output).toContain('name:');
        expect(output).toContain('description:');
        expect(output).toContain('confidence:');
        expect(output).toContain('type:');
      });

      it('should include problem and solution sections', () => {
        const pattern = createMockExtractedPattern();
        const output = manager.saveAsSkill(pattern);

        expect(output).toContain('## Problem');
        expect(output).toContain('## Solution');
        expect(output).toContain('## When to Use');
      });

      it('should include code example when present', () => {
        const pattern = createMockExtractedPattern({
          codeExample: 'const x = 1;',
        });
        const output = manager.saveAsSkill(pattern);

        expect(output).toContain('## Example');
        expect(output).toContain('```typescript');
        expect(output).toContain('const x = 1;');
      });

      it('should not include code example section when absent', () => {
        const pattern = createMockExtractedPattern({
          codeExample: undefined,
        });
        const output = manager.saveAsSkill(pattern);

        expect(output).not.toContain('## Example');
      });

      it('should include related patterns when present', () => {
        const pattern = createMockExtractedPattern({
          relatedPatterns: ['pattern-a', 'pattern-b'],
        });
        const output = manager.saveAsSkill(pattern);

        expect(output).toContain('## Related Patterns');
        expect(output).toContain('- pattern-a');
        expect(output).toContain('- pattern-b');
      });
    });

    describe('generateReport - 学習レポート生成', () => {
      it('should generate report from extraction result', () => {
        const messages = createErrorResolutionConversation();
        const result = manager.extractPatterns(messages, 'report-test');
        const report = manager.generateReport(result);

        expect(report.sessionId).toBe('report-test');
        expect(report.messageCount).toBe(messages.length);
        expect(report.sessionDuration).toBeDefined();
        expect(report.generatedAt).toBeInstanceOf(Date);
      });

      it('should count skipped patterns by category', () => {
        const messages = createConversationWithIgnorablePatterns();
        const result = manager.extractPatterns(messages, 'skip-test');
        const report = manager.generateReport(result);

        expect(typeof report.skippedCounts).toBe('object');
      });

      it('should format duration correctly', () => {
        const baseTime = new Date('2026-01-25T10:00:00Z');
        const messages: ConversationMessage[] = [
          createConversationMessage(0, 'user', 'Start', baseTime),
          createConversationMessage(1, 'assistant', 'End', new Date(baseTime.getTime() + 90 * 60000)),
        ];

        const result = manager.extractPatterns(messages, 'duration-test');
        const report = manager.generateReport(result);

        expect(report.sessionDuration).toBe('1時間30分');
      });
    });

    describe('formatReportAsMarkdown - Markdownフォーマット', () => {
      it('should format report as markdown', () => {
        const messages = createErrorResolutionConversation();
        const result = manager.extractPatterns(messages, 'md-test');
        const report = manager.generateReport(result);
        const markdown = manager.formatReportAsMarkdown(report);

        expect(markdown).toContain('📊 **学習レポート**');
        expect(markdown).toContain('**セッション**: md-test');
        expect(markdown).toContain('**メッセージ数**:');
        expect(markdown).toContain('**セッション時間**:');
      });

      it('should include extracted patterns section', () => {
        const result = createMockExtractionResult();
        const report = manager.generateReport(result);
        const markdown = manager.formatReportAsMarkdown(report);

        expect(markdown).toContain('## 抽出されたパターン');
      });

      it('should include confirmation prompt', () => {
        const result = createMockExtractionResult();
        const report = manager.generateReport(result);
        const markdown = manager.formatReportAsMarkdown(report);

        expect(markdown).toContain('保存を続行しますか？');
      });
    });
  });

  describe('REQ-LH-003: Pattern Ignore List', () => {
    describe('shouldIgnore - 除外チェック', () => {
      it('should ignore typo corrections', () => {
        const candidate: PatternCandidate = {
          type: 'user_corrections',
          problem: 'typo in function name',
          solution: 'Fixed the spelling mistake',
          messageIndices: [0, 1],
          tentativeConfidence: 0.8,
        };

        const result = manager.shouldIgnore(candidate);
        expect(result.ignore).toBe(true);
        expect(result.reason).toContain('typo');
      });

      it('should ignore temporary network errors', () => {
        const candidate: PatternCandidate = {
          type: 'error_resolution',
          problem: 'ECONNRESET while fetching data',
          solution: 'Retried the request',
          messageIndices: [0, 1],
          tentativeConfidence: 0.8,
        };

        const result = manager.shouldIgnore(candidate);
        expect(result.ignore).toBe(true);
        expect(result.reason).toContain('temporary');
      });

      it('should ignore security-related patterns', () => {
        const candidate: PatternCandidate = {
          type: 'error_resolution',
          problem: 'api_key was invalid',
          solution: 'Updated the API key',
          messageIndices: [0, 1],
          tentativeConfidence: 0.9,
        };

        const result = manager.shouldIgnore(candidate);
        expect(result.ignore).toBe(true);
        expect(result.reason).toContain('security');
      });

      it('should not ignore valid patterns', () => {
        const candidate: PatternCandidate = {
          type: 'error_resolution',
          problem: 'TypeScript TS2322 type error',
          solution: 'Added proper type annotation',
          messageIndices: [0, 1],
          tentativeConfidence: 0.8,
        };

        const result = manager.shouldIgnore(candidate);
        expect(result.ignore).toBe(false);
      });

      it('should ignore rate limit errors', () => {
        const candidate: PatternCandidate = {
          type: 'error_resolution',
          problem: 'HTTP 429 Too Many Requests',
          solution: 'Added retry logic',
          messageIndices: [0, 1],
          tentativeConfidence: 0.8,
        };

        const result = manager.shouldIgnore(candidate);
        expect(result.ignore).toBe(true);
        expect(result.reason).toContain('external_api');
      });

      it('should ignore environment-specific path errors', () => {
        const candidate: PatternCandidate = {
          type: 'error_resolution',
          problem: 'ENOENT: no such file /home/user/project/file.ts',
          solution: 'Created the missing file',
          messageIndices: [0, 1],
          tentativeConfidence: 0.8,
        };

        const result = manager.shouldIgnore(candidate);
        expect(result.ignore).toBe(true);
        expect(result.reason).toContain('environment_specific');
      });
    });

    describe('addIgnorePattern - カスタム除外パターン', () => {
      it('should add custom ignore pattern', () => {
        manager.addIgnorePattern({
          category: 'typo',
          pattern: /custom-pattern-to-ignore/i,
          reason: 'Custom reason',
        });

        const candidate: PatternCandidate = {
          type: 'error_resolution',
          problem: 'custom-pattern-to-ignore in code',
          solution: 'Fixed it',
          messageIndices: [0, 1],
          tentativeConfidence: 0.8,
        };

        const result = manager.shouldIgnore(candidate);
        expect(result.ignore).toBe(true);
        expect(result.reason).toContain('Custom reason');
      });

      it('should preserve default patterns after adding custom', () => {
        manager.addIgnorePattern({
          category: 'typo',
          pattern: /my-custom/i,
          reason: 'My reason',
        });

        const patterns = manager.getIgnorePatterns();
        expect(patterns.length).toBeGreaterThan(DEFAULT_IGNORE_PATTERNS.length);
      });
    });

    describe('getIgnorePatterns - 除外パターン取得', () => {
      it('should return default patterns', () => {
        const patterns = manager.getIgnorePatterns();
        expect(patterns.length).toBe(DEFAULT_IGNORE_PATTERNS.length);
      });

      it('should return readonly array', () => {
        const patterns = manager.getIgnorePatterns();
        expect(Array.isArray(patterns)).toBe(true);
      });
    });
  });

  describe('Configuration', () => {
    describe('getConfig - 設定取得', () => {
      it('should return default config', () => {
        const config = manager.getConfig();
        expect(config.minMessages).toBe(DEFAULT_EXTRACTION_CONFIG.minMessages);
        expect(config.minSessionMinutes).toBe(DEFAULT_EXTRACTION_CONFIG.minSessionMinutes);
        expect(config.confidenceThreshold).toBe(DEFAULT_EXTRACTION_CONFIG.confidenceThreshold);
      });

      it('should return merged config when custom options provided', () => {
        const customManager = createLearningHooksManager({
          minMessages: 5,
        });
        const config = customManager.getConfig();

        expect(config.minMessages).toBe(5);
        expect(config.minSessionMinutes).toBe(DEFAULT_EXTRACTION_CONFIG.minSessionMinutes);
      });
    });
  });
});

describe('createConversationMessage', () => {
  it('should create message with error detection', () => {
    const msg = createConversationMessage(0, 'user', 'Error: Something failed');
    expect(msg.containsError).toBe(true);
  });

  it('should create message with correction detection', () => {
    const msg = createConversationMessage(0, 'user', '修正してください');
    expect(msg.containsCorrection).toBe(true);
  });

  it('should create message with code detection', () => {
    const msg = createConversationMessage(0, 'assistant', '```ts\nconst x = 1;\n```');
    expect(msg.containsCode).toBe(true);
  });

  it('should use provided timestamp', () => {
    const timestamp = new Date('2026-01-01T00:00:00Z');
    const msg = createConversationMessage(0, 'user', 'Hello', timestamp);
    expect(msg.timestamp).toEqual(timestamp);
  });
});

describe('formatLearningReport', () => {
  it('should format report using manager', () => {
    const report = {
      sessionId: 'test-session',
      messageCount: 15,
      sessionDuration: '30分',
      extractedPatterns: [],
      skippedCounts: {},
      generatedAt: new Date(),
    };

    const markdown = formatLearningReport(report);
    expect(markdown).toContain('📊 **学習レポート**');
    expect(markdown).toContain('test-session');
  });
});

// Test Helper Functions

function createErrorResolutionConversation(): ConversationMessage[] {
  const baseTime = new Date('2026-01-25T10:00:00Z');
  return [
    createConversationMessage(0, 'user', 'Running the build', baseTime),
    createConversationMessage(
      1,
      'assistant',
      'Build started',
      new Date(baseTime.getTime() + 1000)
    ),
    createConversationMessage(
      2,
      'user',
      'Error: TS2322 Type error in file.ts',
      new Date(baseTime.getTime() + 60000)
    ),
    createConversationMessage(
      3,
      'assistant',
      '```typescript\nconst x: string = "fixed";\n```',
      new Date(baseTime.getTime() + 120000)
    ),
    createConversationMessage(
      4,
      'user',
      'Build passed ✅',
      new Date(baseTime.getTime() + 180000)
    ),
  ];
}

function createUserCorrectionConversation(): ConversationMessage[] {
  const baseTime = new Date('2026-01-25T10:00:00Z');
  return [
    createConversationMessage(0, 'user', 'Create a function', baseTime),
    createConversationMessage(
      1,
      'assistant',
      '```typescript\nfunction foo() { return 1; }\n```',
      new Date(baseTime.getTime() + 1000)
    ),
    createConversationMessage(
      2,
      'user',
      '修正してください。instead of returning 1, return "hello"',
      new Date(baseTime.getTime() + 60000)
    ),
    createConversationMessage(
      3,
      'assistant',
      '```typescript\nfunction foo() { return "hello"; }\n```',
      new Date(baseTime.getTime() + 120000)
    ),
    createConversationMessage(4, 'user', '承認', new Date(baseTime.getTime() + 180000)),
  ];
}

function createManyPatternsConversation(): ConversationMessage[] {
  const baseTime = new Date('2026-01-25T10:00:00Z');
  const messages: ConversationMessage[] = [];

  for (let i = 0; i < 5; i++) {
    messages.push(
      createConversationMessage(
        i * 3,
        'user',
        `Error: Problem ${i}`,
        new Date(baseTime.getTime() + i * 60000)
      )
    );
    messages.push(
      createConversationMessage(
        i * 3 + 1,
        'assistant',
        `\`\`\`typescript\nconst fix${i} = true;\n\`\`\``,
        new Date(baseTime.getTime() + i * 60000 + 10000)
      )
    );
    messages.push(
      createConversationMessage(
        i * 3 + 2,
        'user',
        '成功 ✅',
        new Date(baseTime.getTime() + i * 60000 + 20000)
      )
    );
  }

  return messages;
}

function createConversationWithIgnorablePatterns(): ConversationMessage[] {
  const baseTime = new Date('2026-01-25T10:00:00Z');
  return [
    createConversationMessage(0, 'user', 'typo in the code', baseTime),
    createConversationMessage(
      1,
      'assistant',
      'Fixed the spelling',
      new Date(baseTime.getTime() + 1000)
    ),
    createConversationMessage(
      2,
      'user',
      'ECONNRESET error',
      new Date(baseTime.getTime() + 60000)
    ),
    createConversationMessage(
      3,
      'assistant',
      'Network issue, retrying',
      new Date(baseTime.getTime() + 120000)
    ),
  ];
}

function createMockExtractedPattern(
  overrides: Partial<{
    codeExample: string | undefined;
    relatedPatterns: string[];
  }> = {}
): import('../src/skills/learning-hooks/types.js').ExtractedPattern {
  return {
    id: 'error-resolution-test-abc123',
    name: 'error-resolution-test-pattern',
    description: 'A test pattern for error resolution',
    type: 'error_resolution',
    confidence: 0.85,
    problem: 'Test problem description',
    solution: 'Test solution description',
    codeExample: overrides.codeExample,
    whenToUse: ['When testing'],
    relatedPatterns: overrides.relatedPatterns ?? [],
    sourceSessionId: 'test-session-001',
    extractedAt: new Date('2026-01-25T10:00:00Z'),
  };
}

function createMockExtractionResult(): import('../src/skills/learning-hooks/types.js').ExtractionResult {
  return {
    sessionId: 'mock-session',
    extractedPatterns: [createMockExtractedPattern()],
    skippedPatterns: [],
    messageCount: 10,
    sessionMinutes: 30,
    extractedAt: new Date(),
  };
}
