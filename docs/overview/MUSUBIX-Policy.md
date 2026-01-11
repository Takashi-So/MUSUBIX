# MUSUBIX Policy パッケージ

**パッケージ名**: `@musubix/policy`  
**バージョン**: 3.0.1  
**最終更新**: 2026-01-12

---

## 1. 概要

`@musubix/policy` は、MUSUBIX v3.0で導入されたポリシー検証エンジンです。MUSUBIX 9憲法条項に基づいてプロジェクトの構造・品質を自動検証し、開発プロセスの一貫性を保証します。

### 1.1 特徴

| 特徴 | 説明 |
|------|------|
| **9憲法条項検証** | MUSUBIX開発ルールへの準拠を自動チェック |
| **CI/CD統合** | GitHub Actions等への組み込みが容易 |
| **カスタムポリシー** | プロジェクト固有のルールを追加可能 |
| **詳細レポート** | 違反箇所と修正方法を明示 |
| **型安全** | TypeScriptによる完全な型定義 |

### 1.2 9憲法条項

| 条項 | ID | 名称 | 概要 |
|------|-----|------|------|
| I | CONST-001 | Library-First | 機能は独立ライブラリとして開始 |
| II | CONST-002 | CLI Interface | すべてのライブラリはCLI公開必須 |
| III | CONST-003 | Test-First | Red-Green-Blueサイクルでテスト先行 |
| IV | CONST-004 | EARS Format | 要件はEARS形式で記述 |
| V | CONST-005 | Traceability | 要件↔設計↔コード↔テストの100%追跡 |
| VI | CONST-006 | Project Memory | steering/を参照してから決定 |
| VII | CONST-007 | Design Patterns | 設計パターン適用の文書化 |
| VIII | CONST-008 | Decision Records | すべての決定をADRで記録 |
| IX | CONST-009 | Quality Gates | フェーズ移行前の品質検証 |

---

## 2. インストール

```bash
# 単体インストール
npm install @musubix/policy

# または musubix パッケージ経由
npm install musubix
```

---

## 3. 基本的な使い方

### 3.1 ポリシーエンジンの初期化

```typescript
import { createPolicyEngine } from '@musubix/policy';

const engine = createPolicyEngine();
```

### 3.2 プロジェクト全体の検証

```typescript
const report = await engine.validateProject('.');

console.log('合格:', report.passed);
console.log('違反数:', report.violations.length);
console.log('警告数:', report.warnings.length);

// 違反の詳細
for (const v of report.violations) {
  console.log(`[${v.severity}] ${v.policyId}: ${v.message}`);
  if (v.suggestion) {
    console.log(`  修正案: ${v.suggestion}`);
  }
}
```

### 3.3 特定ポリシーのみ検証

```typescript
// CONST-001（Library-First）とCONST-003（Test-First）のみ
const report = await engine.validate(
  { projectPath: '.' },
  ['CONST-001', 'CONST-003']
);
```

### 3.4 ファイル単位の検証

```typescript
// 要件ファイルがEARS形式か確認
const report = await engine.validateFile('storage/specs/REQ-001.md');

if (!report.passed) {
  console.log('EARS形式に準拠していません');
  for (const v of report.violations) {
    console.log(`  - ${v.message}`);
  }
}
```

---

## 4. ポリシー詳細

### 4.1 CONST-001: Library-First

**検証内容**: `packages/` ディレクトリの存在を確認

```typescript
// 違反例
project/
├── src/           # packages/ がない → 違反
└── package.json

// 準拠例
project/
├── packages/
│   ├── core/
│   └── utils/
└── package.json
```

### 4.2 CONST-002: CLI Interface

**検証内容**: `bin/` ディレクトリまたは package.json の `bin` フィールドを確認

```json
// 準拠例: package.json
{
  "name": "my-package",
  "bin": {
    "my-cli": "./bin/cli.js"
  }
}
```

### 4.3 CONST-003: Test-First

**検証内容**: テストファイル（`*.test.ts`, `*.spec.ts`）の存在を確認

```typescript
// 検証対象パターン
**/*.test.ts
**/*.spec.ts
**/__tests__/*.ts
```

### 4.4 CONST-004: EARS Format

**検証内容**: 要件ファイルがEARS形式（5パターン）で記述されているか確認

```markdown
<!-- 5つのEARSパターン -->
1. Ubiquitous:   THE [system] SHALL [requirement]
2. Event-driven: WHEN [event], THE [system] SHALL [response]
3. State-driven: WHILE [state], THE [system] SHALL [response]
4. Unwanted:     THE [system] SHALL NOT [behavior]
5. Optional:     IF [condition], THEN THE [system] SHALL [response]
```

### 4.5 CONST-005: Traceability

**検証内容**: `storage/traceability/` ディレクトリの存在を確認

```
project/
└── storage/
    └── traceability/
        ├── matrix.json
        └── links.json
```

### 4.6 CONST-006: Project Memory

**検証内容**: `steering/` ディレクトリの存在を確認

```
project/
└── steering/
    ├── structure.ja.md
    ├── tech.ja.md
    ├── product.ja.md
    └── rules/
        └── constitution.md
```

### 4.7 CONST-007: Design Patterns

**検証内容**: `storage/design/` ディレクトリの存在を確認

```
project/
└── storage/
    └── design/
        ├── patterns.md
        └── decisions/
```

### 4.8 CONST-008: Decision Records

**検証内容**: `docs/decisions/` または `docs/adr/` ディレクトリの存在を確認

```
project/
└── docs/
    └── decisions/
        ├── ADR-0001.md
        └── ADR-0002.md
```

### 4.9 CONST-009: Quality Gates

**検証内容**: CI設定（`.github/workflows/`）またはテスト設定（`vitest.config.ts`等）の存在を確認

```
project/
├── .github/
│   └── workflows/
│       └── ci.yml
└── vitest.config.ts
```

---

## 5. ポリシー一覧の取得

```typescript
// 全ポリシー
const all = engine.listPolicies();

// 憲法条項のみ
const constitution = engine.listPolicies('constitution');

// カスタムポリシーのみ
const custom = engine.listPolicies('custom');

for (const p of constitution) {
  console.log(`${p.id}: ${p.name} (${p.severity})`);
}
```

---

## 6. カスタムポリシーの登録

### 6.1 カスタムポリシーの作成

```typescript
engine.registerPolicy({
  id: 'CUSTOM-001',
  name: 'No Console Log',
  description: 'プロダクションコードでconsole.logを禁止',
  category: 'custom',
  severity: 'warning',
  
  async validate(context) {
    const violations = [];
    
    // srcディレクトリのTSファイルを検査
    const files = await context.glob('src/**/*.ts');
    
    for (const file of files) {
      const content = await context.readFile(file);
      const lines = content.split('\n');
      
      lines.forEach((line, index) => {
        if (line.includes('console.log')) {
          violations.push({
            file,
            line: index + 1,
            message: `console.log found at line ${index + 1}`,
            suggestion: 'Use a proper logger instead',
          });
        }
      });
    }
    
    return {
      passed: violations.length === 0,
      violations,
    };
  },
});
```

### 6.2 カスタムポリシーの実行

```typescript
// カスタムポリシーを含めて検証
const report = await engine.validate(
  { projectPath: '.' },
  ['CONST-001', 'CUSTOM-001']  // 憲法条項 + カスタム
);
```

---

## 7. CI/CD統合

### 7.1 GitHub Actions

```yaml
# .github/workflows/policy-check.yml
name: Policy Check

on: [push, pull_request]

jobs:
  policy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: '20'
      
      - run: npm install
      
      - name: Run Policy Check
        run: |
          npx ts-node -e "
            import { createPolicyEngine } from '@musubix/policy';
            
            async function main() {
              const engine = createPolicyEngine();
              const report = await engine.validateProject('.');
              
              if (!report.passed) {
                console.error('Policy violations found:');
                for (const v of report.violations) {
                  console.error(\`  [\${v.severity}] \${v.policyId}: \${v.message}\`);
                }
                process.exit(1);
              }
              
              console.log('All policies passed!');
            }
            
            main();
          "
```

### 7.2 pre-commit フック

```bash
# .husky/pre-commit
#!/bin/sh
npx ts-node scripts/policy-check.ts
```

---

## 8. API リファレンス

### 8.1 PolicyEngine インターフェース

```typescript
interface PolicyEngine {
  // 検証
  validateProject(projectPath: string): Promise<PolicyReport>;
  validate(context: ValidationContext, policyIds?: string[]): Promise<PolicyReport>;
  validateFile(filePath: string): Promise<PolicyReport>;
  
  // ポリシー管理
  listPolicies(category?: 'constitution' | 'custom'): Policy[];
  getPolicy(id: string): Policy | null;
  registerPolicy(policy: CustomPolicy): void;
  unregisterPolicy(id: string): boolean;
}
```

### 8.2 PolicyReport インターフェース

```typescript
interface PolicyReport {
  passed: boolean;           // 全ポリシー合格か
  violations: Violation[];   // 違反リスト（error）
  warnings: Violation[];     // 警告リスト（warning）
  checkedPolicies: string[]; // チェックしたポリシーID
  timestamp: string;         // 検証日時
}
```

### 8.3 Violation インターフェース

```typescript
interface Violation {
  policyId: string;      // 例: 'CONST-001'
  severity: 'error' | 'warning';
  message: string;       // 違反メッセージ
  file?: string;         // 違反ファイルパス
  line?: number;         // 違反行番号
  suggestion?: string;   // 修正提案
}
```

---

## 9. ユースケース

### 9.1 新規プロジェクトのセットアップ検証

```typescript
import { createPolicyEngine } from '@musubix/policy';

async function validateNewProject(projectPath: string) {
  const engine = createPolicyEngine();
  
  // 必須の憲法条項のみチェック
  const criticalPolicies = [
    'CONST-001', // Library-First
    'CONST-003', // Test-First
    'CONST-005', // Traceability
    'CONST-006', // Project Memory
  ];
  
  const report = await engine.validate(
    { projectPath },
    criticalPolicies
  );
  
  if (!report.passed) {
    console.log('プロジェクト構造を修正してください:');
    for (const v of report.violations) {
      console.log(`  - ${v.message}`);
      if (v.suggestion) {
        console.log(`    修正: ${v.suggestion}`);
      }
    }
  }
  
  return report;
}
```

### 9.2 PRマージ前の品質ゲート

```typescript
async function prQualityGate() {
  const engine = createPolicyEngine();
  const report = await engine.validateProject('.');
  
  // エラーがあればマージ拒否
  if (report.violations.length > 0) {
    console.error('❌ Quality gate failed');
    process.exit(1);
  }
  
  // 警告は許容するが表示
  if (report.warnings.length > 0) {
    console.warn(`⚠️ ${report.warnings.length} warnings found`);
  }
  
  console.log('✅ Quality gate passed');
}
```

---

## 10. 関連パッケージ

| パッケージ | 説明 |
|------------|------|
| `@musubix/knowledge` | Git-Native知識グラフシステム |
| `@musubix/decisions` | Architecture Decision Records管理 |
| `musubix` | 3パッケージを含むメインパッケージ |

---

## 11. 参照

- [MUSUBIX v3.0 User Guide](../MUSUBIX-v3.0-User-Guide.md)
- [9憲法条項](../../steering/rules/constitution.md)
- [GitHub Repository](https://github.com/nahisaho/MUSUBIX)
- [npm Package](https://www.npmjs.com/package/@musubix/policy)
