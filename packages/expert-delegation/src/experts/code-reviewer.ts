/**
 * @nahisaho/musubix-expert-delegation
 * Code Reviewer Expert
 *
 * DES-EXP-001
 * Traces to: REQ-EXP-001
 */

import type { Expert } from '../types/index.js';

/**
 * Code Reviewer Expert
 *
 * コードレビュー・品質分析を行うエキスパート。
 */
export const codeReviewerExpert: Expert = {
  type: 'code-reviewer',
  name: 'Code Reviewer Expert',
  description:
    'コードレビュー、品質分析、リファクタリング提案を行います。クリーンコード、テスタビリティ、保守性に注目します。',

  systemPrompt: `You are a senior code reviewer with deep expertise in:
- Clean code principles
- Code smells and refactoring
- Design patterns application
- Testing best practices
- Performance optimization
- Documentation standards
- Language-specific idioms

When reviewing code:
1. Check for correctness and edge cases
2. Evaluate readability and maintainability
3. Identify code smells and anti-patterns
4. Suggest specific improvements with examples
5. Consider testability and debugging

Provide feedback in this format:
[Category] Issue description
  Location: file:line
  Suggestion: specific improvement
  Example: code snippet if helpful

Categories: BUG, SECURITY, PERFORMANCE, STYLE, MAINTAINABILITY, DOCS`,

  triggers: [
    { pattern: 'review this code', language: 'en', priority: 85 },
    { pattern: 'find issues', language: 'en', priority: 70 },
    { pattern: 'code quality', language: 'en', priority: 75 },
    { pattern: 'refactor', language: 'en', priority: 70 },
    { pattern: 'improve this', language: 'en', priority: 60 },
    { pattern: 'レビュー', language: 'ja', priority: 80 },
    { pattern: 'コードチェック', language: 'ja', priority: 75 },
    { pattern: 'リファクタ', language: 'ja', priority: 70 },
    { pattern: '改善', language: 'ja', priority: 50 },
  ],

  ontologyClass: 'sdd:CodeReviewer',

  capabilities: [
    {
      name: 'review',
      mode: 'advisory',
      description: 'コードレビュー・問題点指摘',
    },
    {
      name: 'analyze',
      mode: 'advisory',
      description: 'コード品質分析',
    },
    {
      name: 'refactor',
      mode: 'implementation',
      description: 'リファクタリングコード生成',
    },
  ],
};
