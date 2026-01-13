/**
 * @nahisaho/musubix-expert-delegation
 * Architect Expert
 *
 * DES-EXP-001
 * Traces to: REQ-EXP-001
 */

import type { Expert } from '../types/index.js';

/**
 * Architect Expert
 *
 * ソフトウェアアーキテクチャの設計・分析を行うエキスパート。
 * claude-delegator互換のシステムプロンプトを使用。
 */
export const architectExpert: Expert = {
  type: 'architect',
  name: 'Architect Expert',
  description:
    'ソフトウェアアーキテクチャの設計、レビュー、改善提案を行います。C4モデル、設計パターン、SOLID原則に精通しています。',

  systemPrompt: `You are a senior software architect with deep expertise in:
- System design and architecture patterns
- C4 model (Context, Container, Component, Code)
- Design patterns (GoF, Enterprise, Domain-Driven Design)
- SOLID principles and clean architecture
- Scalability, performance, and reliability
- Technology selection and trade-off analysis

When analyzing architecture:
1. Understand the business context and requirements
2. Identify key quality attributes (scalability, security, maintainability)
3. Propose appropriate patterns and technologies
4. Consider trade-offs and risks
5. Provide clear diagrams when helpful (Mermaid format)

Always explain your reasoning and provide actionable recommendations.`,

  triggers: [
    { pattern: 'how should I structure', language: 'en', priority: 80 },
    { pattern: 'architecture', language: 'en', priority: 70 },
    { pattern: 'design pattern', language: 'en', priority: 70 },
    { pattern: 'system design', language: 'en', priority: 75 },
    { pattern: 'アーキテクチャ', language: 'ja', priority: 80 },
    { pattern: '設計', language: 'ja', priority: 60 },
    { pattern: 'システム構成', language: 'ja', priority: 70 },
    { pattern: '構造', language: 'ja', priority: 50 },
  ],

  ontologyClass: 'sdd:Architect',

  capabilities: [
    {
      name: 'analyze',
      mode: 'advisory',
      description: 'アーキテクチャの分析・評価',
    },
    {
      name: 'design',
      mode: 'advisory',
      description: 'アーキテクチャの設計提案',
    },
    {
      name: 'review',
      mode: 'advisory',
      description: '既存設計のレビュー',
    },
    {
      name: 'generate',
      mode: 'implementation',
      description: 'C4ダイアグラムの生成',
    },
  ],
};
