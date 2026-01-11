# MUSUBIX Policy Engine スキル

このスキルを使用して、`@musubix/policy` パッケージによる9憲法条項の自動検証を行います。

## 概要

MUSUBIX Policy Engineは、プロジェクトが9憲法条項に準拠しているかを自動的に検証します。

## 基本的な使い方

### ポリシーエンジンの初期化

```typescript
import { createPolicyEngine } from '@musubix/policy';

const engine = createPolicyEngine();
```

### プロジェクトの検証

```typescript
const report = await engine.validateProject('.');

console.log('合格:', report.passed);
console.log('違反数:', report.violations.length);

for (const v of report.violations) {
  console.log(`[${v.severity}] ${v.policyId}: ${v.message}`);
}
```

### 特定ポリシーの検証

```typescript
// CONST-001（Library-First）のみ検証
const report = await engine.validate(
  { projectPath: '.' },
  ['CONST-001']
);
```

### ファイル単位の検証

```typescript
// 要件ファイルがEARS形式か確認
const report = await engine.validateFile('storage/specs/REQ-001.md');
```

## 9憲法条項

| ID | 条項 | 検証内容 | 重要度 |
|----|------|----------|--------|
| CONST-001 | Library-First | `packages/` ディレクトリの存在 | error |
| CONST-002 | CLI Interface | `bin/` または package.json の bin フィールド | error |
| CONST-003 | Test-First | テストファイルの存在 | error |
| CONST-004 | EARS Format | 要件ファイルのEARS形式 | error |
| CONST-005 | Traceability | `storage/traceability/` の存在 | error |
| CONST-006 | Project Memory | `steering/` ディレクトリの存在 | warning |
| CONST-007 | Design Patterns | `storage/design/` の存在 | warning |
| CONST-008 | Decision Records | `docs/decisions/` の存在 | warning |
| CONST-009 | Quality Gates | CI設定またはテスト設定の存在 | error |

## ポリシー一覧の取得

```typescript
// 全ポリシー
const all = engine.listPolicies();

// 憲法条項のみ
const constitution = engine.listPolicies('constitution');

for (const p of constitution) {
  console.log(`${p.id}: ${p.name}`);
}
```

## カスタムポリシーの登録

```typescript
engine.registerPolicy({
  id: 'CUSTOM-001',
  name: 'No Console Logs',
  description: 'Production code must not contain console.log',
  severity: 'warning',
  category: 'quality',
  async validate(ctx) {
    if (ctx.content?.includes('console.log')) {
      return {
        passed: false,
        violations: [{
          policyId: 'CUSTOM-001',
          message: 'console.log found in production code',
          severity: 'warning',
        }],
      };
    }
    return { passed: true, violations: [] };
  },
});
```

## 検証レポートの活用

```typescript
const report = await engine.validateProject('.');

if (report.passed) {
  console.log('✅ すべての憲法条項に準拠しています');
} else {
  console.log(`❌ ${report.failedPolicies} 件の違反:`);
  
  for (const v of report.violations) {
    const icon = v.severity === 'error' ? '🚫' : '⚠️';
    console.log(`${icon} [${v.policyId}] ${v.message}`);
  }
}
```

## 必要なプロジェクト構造

```
project/
├── packages/           # CONST-001: Library-First
├── bin/                # CONST-002: CLI Interface
├── __tests__/          # CONST-003: Test-First
├── storage/
│   ├── specs/          # CONST-004: EARS Format
│   ├── traceability/   # CONST-005: Traceability
│   └── design/         # CONST-007: Design Patterns
├── steering/           # CONST-006: Project Memory
├── docs/decisions/     # CONST-008: Decision Records
└── vitest.config.ts    # CONST-009: Quality Gates
```

## 参照

- [ユーザーガイド](docs/MUSUBIX-v3.0-User-Guide.md)
- [9憲法条項](steering/rules/constitution.md)
