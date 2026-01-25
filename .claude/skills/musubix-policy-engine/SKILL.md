# MUSUBIX Policy Engine スキル

> 10憲法条項の自動検証エンジン

## WHEN/DO トリガー

| WHEN | DO |
|------|-----|
| プロジェクト全体の検証 | `engine.validateProject('.')` |
| 特定ポリシーのみ検証 | `engine.validate(ctx, ['CONST-001'])` |
| 単一ファイル検証 | `engine.validateFile(path)` |
| カスタムルール追加 | `engine.registerPolicy(policy)` |

## クイック使用法

```typescript
import { createPolicyEngine } from '@musubix/policy';

const engine = createPolicyEngine();

// プロジェクト検証
const report = await engine.validateProject('.');

if (report.passed) {
  console.log('✅ すべての憲法条項に準拠');
} else {
  for (const v of report.violations) {
    console.log(`❌ [${v.policyId}] ${v.message}`);
  }
}

// ポリシー一覧
const policies = engine.listPolicies('constitution');
```

## 10憲法条項

| ID | 条項 | 検証内容 | 重要度 |
|----|------|----------|--------|
| CONST-001 | コンテキスト最優先 | steering/の参照 | error |
| CONST-002 | ナレッジ駆動 | 既存知識の活用 | error |
| CONST-003 | 仕様駆動(SDD) | 要件→設計→実装 | error |
| CONST-004 | トレーサビリティ | ADR記録 | error |
| CONST-005 | 段階的詳細化 | 抽象→具体 | warning |
| CONST-006 | 自律学習 | Wake-Sleep活用 | warning |
| CONST-007 | 形式検証 | Lean4証明 | warning |
| CONST-008 | パターン適用 | ベストプラクティス | warning |
| CONST-009 | 明示的コミュニケーション | 不明点確認 | error |
| CONST-010 | 品質最優先 | テスト・検証 | error |

## 必要なプロジェクト構造

```
project/
├── packages/           # Library-First
├── bin/                # CLI Interface
├── __tests__/          # Test-First
├── storage/
│   ├── specs/          # EARS Format
│   ├── traceability/   # Traceability
│   └── design/         # Design Patterns
├── steering/           # Project Memory
├── docs/decisions/     # Decision Records
└── vitest.config.ts    # Quality Gates
```

## 出力フォーマット

```
┌─────────────────────────────────────────┐
│ Policy Validation Report                │
├─────────────────────────────────────────┤
│ ✅ CONST-001: Context First             │
│ ✅ CONST-002: Knowledge Driven          │
│ ❌ CONST-003: SDD Workflow              │
│    → Missing specs directory            │
├─────────────────────────────────────────┤
│ Passed: 8/10 | Violations: 2            │
└─────────────────────────────────────────┘
```
