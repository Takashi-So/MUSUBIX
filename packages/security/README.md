# @nahisaho/musubix-security

MUSUBIX Security Package - セキュリティ分析と脆弱性検出

## 概要

MUSUBIXシステムにセキュリティ特化機能を提供するパッケージです。

### 主な機能

- **脆弱性スキャン**: OWASP Top 10、CWE Top 25対応
- **テイント分析**: データフロー追跡による汚染検出
- **自動修正**: LLM（VS Code LM API）+ Z3形式検証による安全な修正
- **シークレット検出**: APIキー、トークン、パスワードの検出
- **依存関係監査**: npm依存関係の脆弱性チェック

## インストール

```bash
npm install @nahisaho/musubix-security
```

## 使用方法

### CLI

```bash
# 脆弱性スキャン
npx musubix-security scan ./src

# 自動修正
npx musubix-security fix VULN-2026-001

# 依存関係監査
npx musubix-security audit-deps

# シークレット検出
npx musubix-security detect-secrets ./src

# コンプライアンスチェック
npx musubix-security compliance --standard asvs
```

### Library API

```typescript
import { 
  VulnerabilityScanner, 
  TaintAnalyzer,
  FixPipeline,
  SecretsDetector,
  DependencyAuditor
} from '@nahisaho/musubix-security';

// 脆弱性スキャン
const scanner = new VulnerabilityScanner();
const result = await scanner.scan(['./src/**/*.ts']);

// テイント分析
const taintAnalyzer = new TaintAnalyzer();
const taintResult = await taintAnalyzer.analyze(code, 'file.ts');

// 自動修正
const fixPipeline = new FixPipeline();
const fixes = await fixPipeline.generateFix(vulnerability);
const verified = await fixPipeline.verifyFix(fixes[0]);
```

## 設定

プロジェクトルートに `.musubix-security.yaml` を作成:

```yaml
version: "1.0"

scan:
  rulesets:
    - owasp-top-10
    - cwe-top-25
  severity:
    - critical
    - high
  exclude:
    - "**/node_modules/**"
    - "**/*.test.ts"

fix:
  llm:
    enabled: true
    model: "copilot"
  autoApply: false

secrets:
  entropyThreshold: 4.5
```

## トレーサビリティ

- **要件定義**: REQ-SEC-001
- **設計書**: DES-SEC-001
- **テスト**: TST-SEC-*

## ライセンス

MIT
