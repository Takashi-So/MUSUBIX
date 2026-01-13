/**
 * @nahisaho/musubix-expert-delegation
 * Trigger Patterns
 *
 * DES-TRG-001
 * Traces to: REQ-TRG-001
 */

import type { ExpertType, TriggerPattern } from '../types/index.js';

/**
 * エキスパートごとのトリガーパターン定義
 */
export const triggerPatterns: Record<ExpertType, TriggerPattern[]> = {
  architect: [
    { pattern: 'how should I structure', language: 'en', priority: 80 },
    { pattern: 'architecture', language: 'en', priority: 70 },
    { pattern: 'design pattern', language: 'en', priority: 70 },
    { pattern: 'system design', language: 'en', priority: 75 },
    { pattern: 'アーキテクチャ', language: 'ja', priority: 80 },
    { pattern: '設計', language: 'ja', priority: 60 },
    { pattern: 'システム構成', language: 'ja', priority: 70 },
  ],

  'security-analyst': [
    { pattern: 'is this secure', language: 'en', priority: 80 },
    { pattern: 'security', language: 'en', priority: 70 },
    { pattern: 'vulnerability', language: 'en', priority: 85 },
    { pattern: 'exploit', language: 'en', priority: 85 },
    { pattern: 'injection', language: 'en', priority: 80 },
    { pattern: 'セキュリティ', language: 'ja', priority: 80 },
    { pattern: '脆弱性', language: 'ja', priority: 85 },
    { pattern: '安全', language: 'ja', priority: 50 },
  ],

  'code-reviewer': [
    { pattern: 'review this code', language: 'en', priority: 85 },
    { pattern: 'find issues', language: 'en', priority: 70 },
    { pattern: 'code quality', language: 'en', priority: 75 },
    { pattern: 'refactor', language: 'en', priority: 70 },
    { pattern: 'レビュー', language: 'ja', priority: 80 },
    { pattern: 'コードチェック', language: 'ja', priority: 75 },
    { pattern: 'リファクタ', language: 'ja', priority: 70 },
  ],

  'plan-reviewer': [
    { pattern: 'review this plan', language: 'en', priority: 80 },
    { pattern: 'validate design', language: 'en', priority: 75 },
    { pattern: 'check requirements', language: 'en', priority: 70 },
    { pattern: 'is this feasible', language: 'en', priority: 65 },
    { pattern: '計画レビュー', language: 'ja', priority: 80 },
    { pattern: '検証', language: 'ja', priority: 60 },
    { pattern: '設計チェック', language: 'ja', priority: 75 },
  ],

  'ears-analyst': [
    { pattern: 'define requirements', language: 'en', priority: 75 },
    { pattern: 'EARS', language: 'any', priority: 90 },
    { pattern: 'requirements analysis', language: 'en', priority: 70 },
    { pattern: 'convert to EARS', language: 'en', priority: 85 },
    { pattern: '要件定義', language: 'ja', priority: 80 },
    { pattern: 'EARS形式', language: 'ja', priority: 90 },
    { pattern: '要件分析', language: 'ja', priority: 70 },
  ],

  'formal-verifier': [
    { pattern: 'formal verification', language: 'en', priority: 90 },
    { pattern: 'prove', language: 'en', priority: 70 },
    { pattern: 'verify correctness', language: 'en', priority: 80 },
    { pattern: 'Z3', language: 'any', priority: 85 },
    { pattern: 'Lean', language: 'any', priority: 85 },
    { pattern: '形式検証', language: 'ja', priority: 90 },
    { pattern: '証明', language: 'ja', priority: 70 },
  ],

  'ontology-reasoner': [
    { pattern: 'infer', language: 'en', priority: 75 },
    { pattern: 'reasoning', language: 'en', priority: 80 },
    { pattern: 'ontology', language: 'en', priority: 85 },
    { pattern: 'knowledge graph', language: 'en', priority: 80 },
    { pattern: 'RDF', language: 'any', priority: 75 },
    { pattern: '推論', language: 'ja', priority: 80 },
    { pattern: 'オントロジー', language: 'ja', priority: 85 },
    { pattern: '知識グラフ', language: 'ja', priority: 80 },
  ],
};

/**
 * すべてのトリガーパターンを取得
 */
export function getAllTriggerPatterns(): TriggerPattern[] {
  return Object.values(triggerPatterns).flat();
}

/**
 * エキスパートのトリガーパターンを取得
 */
export function getTriggerPatterns(type: ExpertType): TriggerPattern[] {
  return triggerPatterns[type] ?? [];
}
