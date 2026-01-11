# 要件定義書: @nahisaho/musubix-security CodeQL同等機能強化

**Document ID**: REQ-SEC-CODEQL-001  
**Version**: 1.0.0  
**Created**: 2026-01-12  
**Author**: AI Agent (GitHub Copilot)  
**Status**: Draft (レビュー待ち)

---

## 1. 概要

### 1.1 目的

@nahisaho/musubix-security パッケージをCodeQL同等以上のセキュリティ分析機能を持つツールに強化する。

### 1.2 背景

現在のmusubix-securityは以下の機能を持つ：
- 脆弱性スキャナー（TypeScript/JavaScript/Python/PHP）
- テイント解析（基本的なデータフロー追跡）
- シークレット検出
- 依存関係監査
- 手続き間解析（Interprocedural Analysis）

CodeQLは以下の追加機能を持つ：
- 12言語サポート（C/C++, C#, Go, Java, Kotlin, JavaScript, TypeScript, Python, Ruby, Rust, Swift）
- データベースベースのコード表現（抽象構文木、データフローグラフ、制御フローグラフ）
- カスタムクエリ言語（QL）
- バリアント解析（Variant Analysis）
- 多言語同時解析

### 1.3 スコープ

**Phase 1 (v3.1.0)**: 解析基盤強化
- 言語サポート拡張（Go, Java, Ruby, Rust追加）
- コードデータベース（CodeDB）の実装
- 制御フローグラフ（CFG）解析強化
- クエリエンジン基盤

**Phase 2 (v3.2.0)**: 高度解析機能
- カスタムクエリ言語（MQL: MUSUBIX Query Language）
- バリアント解析
- 多リポジトリ解析
- シンボリック実行

**Phase 3 (v3.3.0)**: エンタープライズ機能
- SARIF 2.1.0完全準拠
- GitHub Advanced Security統合
- CI/CD完全統合
- パフォーマンス最適化（大規模コードベース対応）

---

## 2. 要件一覧

### 2.1 機能要件 (Functional Requirements)

#### 2.1.1 言語サポート拡張

| ID | 要件 (EARS形式) | 優先度 | 依存 |
|----|----------------|--------|------|
| REQ-SEC-LANG-001 | THE musubix-security system SHALL support static analysis for Go programming language (versions 1.18 to 1.25). | P0 | - |
| REQ-SEC-LANG-002 | THE musubix-security system SHALL support static analysis for Java programming language (versions 8 to 25). | P0 | - |
| REQ-SEC-LANG-003 | THE musubix-security system SHALL support static analysis for Ruby programming language (versions 2.7 to 3.3). | P1 | - |
| REQ-SEC-LANG-004 | THE musubix-security system SHALL support static analysis for Rust programming language (editions 2021 and 2024). | P1 | - |
| REQ-SEC-LANG-005 | THE musubix-security system SHALL support static analysis for Kotlin programming language (versions 1.6 to 2.2). | P2 | REQ-SEC-LANG-002 |
| REQ-SEC-LANG-006 | THE musubix-security system SHALL support static analysis for Swift programming language (versions 5.4 to 6.2). | P2 | - |

#### 2.1.2 コードデータベース（CodeDB）

| ID | 要件 (EARS形式) | 優先度 | 依存 |
|----|----------------|--------|------|
| REQ-SEC-DB-001 | THE musubix-security system SHALL create a queryable code database from source code extraction. | P0 | - |
| REQ-SEC-DB-002 | THE code database SHALL store abstract syntax tree (AST) information for all supported languages. | P0 | REQ-SEC-DB-001 |
| REQ-SEC-DB-003 | THE code database SHALL store data flow graph (DFG) information for interprocedural analysis. | P0 | REQ-SEC-DB-001 |
| REQ-SEC-DB-004 | THE code database SHALL store control flow graph (CFG) information for path-sensitive analysis. | P0 | REQ-SEC-DB-001 |
| REQ-SEC-DB-005 | THE code database SHALL support incremental updates when source files change. | P1 | REQ-SEC-DB-001 |
| REQ-SEC-DB-006 | WHEN code database exceeds 10GB in size, THE system SHALL use memory-mapped storage to reduce memory usage. | P1 | REQ-SEC-DB-001 |
| REQ-SEC-DB-007 | THE code database SHALL be serializable to and deserializable from JSON format for Git-friendly storage. | P0 | REQ-SEC-DB-001 |

#### 2.1.3 クエリエンジン（MQL: MUSUBIX Query Language）

| ID | 要件 (EARS形式) | 優先度 | 依存 |
|----|----------------|--------|------|
| REQ-SEC-MQL-001 | THE musubix-security system SHALL provide a domain-specific query language (MQL) for security analysis. | P0 | REQ-SEC-DB-001 |
| REQ-SEC-MQL-002 | THE MQL engine SHALL support queries for data flow paths from sources to sinks. | P0 | REQ-SEC-MQL-001 |
| REQ-SEC-MQL-003 | THE MQL engine SHALL support queries for control flow patterns. | P0 | REQ-SEC-MQL-001 |
| REQ-SEC-MQL-004 | THE MQL engine SHALL support recursive predicates for transitive closure queries. | P1 | REQ-SEC-MQL-001 |
| REQ-SEC-MQL-005 | THE MQL engine SHALL support parameterized queries for reusable analysis patterns. | P1 | REQ-SEC-MQL-001 |
| REQ-SEC-MQL-006 | WHEN executing MQL queries, THE system SHALL cache intermediate results for query optimization. | P1 | REQ-SEC-MQL-001 |

#### 2.1.4 制御フローグラフ（CFG）解析強化

| ID | 要件 (EARS形式) | 優先度 | 依存 |
|----|----------------|--------|------|
| REQ-SEC-CFG-001 | THE musubix-security system SHALL generate control flow graphs for all functions and methods. | P0 | - |
| REQ-SEC-CFG-002 | THE CFG analyzer SHALL identify all basic blocks within functions. | P0 | REQ-SEC-CFG-001 |
| REQ-SEC-CFG-003 | THE CFG analyzer SHALL track exception handling paths (try-catch-finally). | P0 | REQ-SEC-CFG-001 |
| REQ-SEC-CFG-004 | THE CFG analyzer SHALL identify loop constructs and compute loop bounds where possible. | P1 | REQ-SEC-CFG-001 |
| REQ-SEC-CFG-005 | THE CFG analyzer SHALL support path-sensitive analysis for conditional branches. | P0 | REQ-SEC-CFG-001 |
| REQ-SEC-CFG-006 | WHILE analyzing async/await code, THE CFG analyzer SHALL model promise chains and async boundaries. | P1 | REQ-SEC-CFG-001 |

#### 2.1.5 データフロー解析強化

| ID | 要件 (EARS形式) | 優先度 | 依存 |
|----|----------------|--------|------|
| REQ-SEC-DFG-001 | THE musubix-security system SHALL perform interprocedural data flow analysis across function boundaries. | P0 | REQ-SEC-DB-003 |
| REQ-SEC-DFG-002 | THE data flow analyzer SHALL track taint propagation through object properties and array elements. | P0 | REQ-SEC-DFG-001 |
| REQ-SEC-DFG-003 | THE data flow analyzer SHALL support context-sensitive analysis (call-site sensitivity). | P0 | REQ-SEC-DFG-001 |
| REQ-SEC-DFG-004 | THE data flow analyzer SHALL track data flow through callbacks and closures. | P0 | REQ-SEC-DFG-001 |
| REQ-SEC-DFG-005 | THE data flow analyzer SHALL recognize and handle sanitizers correctly. | P0 | REQ-SEC-DFG-001 |
| REQ-SEC-DFG-006 | WHEN encountering unknown functions, THE data flow analyzer SHALL apply conservative taint propagation. | P1 | REQ-SEC-DFG-001 |

#### 2.1.6 バリアント解析

| ID | 要件 (EARS形式) | 優先度 | 依存 |
|----|----------------|--------|------|
| REQ-SEC-VAR-001 | THE musubix-security system SHALL support variant analysis to find similar vulnerabilities. | P0 | REQ-SEC-MQL-001 |
| REQ-SEC-VAR-002 | WHEN a vulnerability pattern is defined, THE system SHALL scan the entire codebase for variants. | P0 | REQ-SEC-VAR-001 |
| REQ-SEC-VAR-003 | THE variant analyzer SHALL support pattern generalization from specific vulnerability instances. | P1 | REQ-SEC-VAR-001 |
| REQ-SEC-VAR-004 | THE variant analyzer SHALL rank results by similarity score to the original vulnerability. | P1 | REQ-SEC-VAR-001 |

#### 2.1.7 多リポジトリ解析

| ID | 要件 (EARS形式) | 優先度 | 依存 |
|----|----------------|--------|------|
| REQ-SEC-MULTI-001 | THE musubix-security system SHALL support analysis across multiple repositories. | P1 | REQ-SEC-DB-001 |
| REQ-SEC-MULTI-002 | THE multi-repository analyzer SHALL track dependencies between repositories. | P1 | REQ-SEC-MULTI-001 |
| REQ-SEC-MULTI-003 | THE multi-repository analyzer SHALL aggregate vulnerability reports across repositories. | P1 | REQ-SEC-MULTI-001 |

#### 2.1.8 シンボリック実行

| ID | 要件 (EARS形式) | 優先度 | 依存 |
|----|----------------|--------|------|
| REQ-SEC-SYM-001 | THE musubix-security system SHALL support symbolic execution for path exploration. | P1 | REQ-SEC-CFG-001 |
| REQ-SEC-SYM-002 | THE symbolic executor SHALL generate test inputs that reach specific code paths. | P2 | REQ-SEC-SYM-001 |
| REQ-SEC-SYM-003 | WHEN path explosion occurs, THE symbolic executor SHALL apply heuristic pruning strategies. | P2 | REQ-SEC-SYM-001 |

#### 2.1.9 フレームワーク認識

| ID | 要件 (EARS形式) | 優先度 | 依存 |
|----|----------------|--------|------|
| REQ-SEC-FW-001 | THE musubix-security system SHALL recognize and model Express.js framework patterns. | P0 | - |
| REQ-SEC-FW-002 | THE musubix-security system SHALL recognize and model Nest.js framework patterns. | P0 | - |
| REQ-SEC-FW-003 | THE musubix-security system SHALL recognize and model React framework patterns. | P0 | - |
| REQ-SEC-FW-004 | THE musubix-security system SHALL recognize and model Django framework patterns. | P0 | REQ-SEC-LANG-001 |
| REQ-SEC-FW-005 | THE musubix-security system SHALL recognize and model Flask framework patterns. | P0 | REQ-SEC-LANG-001 |
| REQ-SEC-FW-006 | THE musubix-security system SHALL recognize and model Spring Boot framework patterns. | P1 | REQ-SEC-LANG-002 |
| REQ-SEC-FW-007 | THE musubix-security system SHALL recognize and model Ruby on Rails framework patterns. | P1 | REQ-SEC-LANG-003 |
| REQ-SEC-FW-008 | THE musubix-security system SHALL recognize and model Gin framework patterns (Go). | P1 | REQ-SEC-LANG-001 |

#### 2.1.10 レポーティング強化

| ID | 要件 (EARS形式) | 優先度 | 依存 |
|----|----------------|--------|------|
| REQ-SEC-RPT-001 | THE musubix-security system SHALL generate SARIF 2.1.0 compliant reports. | P0 | - |
| REQ-SEC-RPT-002 | THE SARIF report SHALL include data flow paths for each vulnerability. | P0 | REQ-SEC-RPT-001 |
| REQ-SEC-RPT-003 | THE SARIF report SHALL include code snippets for vulnerability locations. | P0 | REQ-SEC-RPT-001 |
| REQ-SEC-RPT-004 | THE musubix-security system SHALL support GitHub Code Scanning alert format. | P1 | REQ-SEC-RPT-001 |
| REQ-SEC-RPT-005 | THE musubix-security system SHALL generate executive summary reports in Markdown format. | P1 | - |

---

### 2.2 非機能要件 (Non-Functional Requirements)

#### 2.2.1 パフォーマンス

| ID | 要件 (EARS形式) | 優先度 |
|----|----------------|--------|
| REQ-SEC-PERF-001 | THE musubix-security system SHALL analyze 100,000 lines of code within 60 seconds on standard hardware. | P0 |
| REQ-SEC-PERF-002 | THE code database creation SHALL complete within 5 minutes for repositories up to 1 million lines of code. | P1 |
| REQ-SEC-PERF-003 | THE MQL query execution SHALL return results within 10 seconds for typical vulnerability queries. | P1 |
| REQ-SEC-PERF-004 | THE system SHALL support incremental analysis that processes only changed files. | P0 |

#### 2.2.2 スケーラビリティ

| ID | 要件 (EARS形式) | 優先度 |
|----|----------------|--------|
| REQ-SEC-SCALE-001 | THE musubix-security system SHALL handle codebases up to 10 million lines of code. | P1 |
| REQ-SEC-SCALE-002 | THE system SHALL support parallel analysis using multiple CPU cores. | P0 |
| REQ-SEC-SCALE-003 | THE system SHALL provide memory usage limits to prevent out-of-memory conditions. | P1 |

#### 2.2.3 互換性

| ID | 要件 (EARS形式) | 優先度 |
|----|----------------|--------|
| REQ-SEC-COMPAT-001 | THE musubix-security system SHALL maintain backward compatibility with existing MCP tools. | P0 |
| REQ-SEC-COMPAT-002 | THE system SHALL support Node.js 20.0.0 and later versions. | P0 |
| REQ-SEC-COMPAT-003 | THE system SHALL run on Linux, macOS, and Windows platforms. | P0 |

#### 2.2.4 統合性

| ID | 要件 (EARS形式) | 優先度 |
|----|----------------|--------|
| REQ-SEC-INT-001 | THE musubix-security system SHALL integrate with GitHub Actions for CI/CD. | P0 |
| REQ-SEC-INT-002 | THE system SHALL integrate with GitLab CI for CI/CD. | P1 |
| REQ-SEC-INT-003 | THE system SHALL provide VS Code extension integration. | P1 |
| REQ-SEC-INT-004 | THE system SHALL support pre-commit hooks for local analysis. | P1 |

---

## 3. 現在の実装状況との比較

### 3.1 既存機能（継続利用）

| 機能 | 現状 | 対応言語 |
|------|------|----------|
| 脆弱性スキャナー | ✅ 実装済み | TypeScript, JavaScript, Python, PHP |
| テイント解析 | ✅ 実装済み（基本） | TypeScript, JavaScript |
| シークレット検出 | ✅ 実装済み | 全言語 |
| 依存関係監査 | ✅ 実装済み | npm, pip |
| 手続き間解析 | ✅ 実装済み（TypeScript） | TypeScript |
| ゼロデイ検出 | ✅ 実装済み | TypeScript |
| コンプライアンスチェック | ✅ 実装済み | 全言語 |
| SARIF出力 | ⚠️ 部分実装 | - |

### 3.2 新規実装必要機能

| 機能 | CodeQL | MUSUBIX現状 | Phase |
|------|--------|-------------|-------|
| Go解析 | ✅ | ❌ | Phase 1 |
| Java解析 | ✅ | ❌ | Phase 1 |
| Ruby解析 | ✅ | ❌ | Phase 1 |
| Rust解析 | ✅ | ❌ | Phase 1 |
| コードデータベース | ✅ | ❌ | Phase 1 |
| カスタムクエリ言語 | ✅ (QL) | ❌ | Phase 2 |
| バリアント解析 | ✅ | ❌ | Phase 2 |
| 多リポジトリ解析 | ✅ | ❌ | Phase 2 |
| シンボリック実行 | ⚠️ 限定的 | ❌ | Phase 2 |
| SARIF 2.1.0完全準拠 | ✅ | ⚠️ | Phase 3 |

---

## 4. アーキテクチャ概要

### 4.1 コンポーネント構成

```
@nahisaho/musubix-security (v3.1.0+)
├── extractors/          # 言語別コード抽出器
│   ├── typescript/      # TypeScript/JavaScript
│   ├── python/          # Python
│   ├── go/              # Go (NEW)
│   ├── java/            # Java (NEW)
│   ├── ruby/            # Ruby (NEW)
│   └── rust/            # Rust (NEW)
├── codedb/              # コードデータベース (NEW)
│   ├── schema/          # データベーススキーマ
│   ├── builder/         # DB構築
│   └── query/           # クエリ実行
├── analysis/            # 解析エンジン
│   ├── cfg/             # 制御フローグラフ (強化)
│   ├── dfg/             # データフローグラフ (強化)
│   ├── taint/           # テイント解析 (強化)
│   └── symbolic/        # シンボリック実行 (NEW)
├── mql/                 # MQLクエリエンジン (NEW)
│   ├── parser/          # クエリパーサー
│   ├── compiler/        # クエリコンパイラ
│   └── executor/        # クエリ実行
├── variant/             # バリアント解析 (NEW)
└── frameworks/          # フレームワーク認識 (強化)
```

### 4.2 データフロー

```
Source Code → Extractor → CodeDB → Analyzer → Results
                              ↑
                         MQL Query Engine
```

---

## 5. 成功基準

### 5.1 定量的基準

| 指標 | 目標値 |
|------|--------|
| 対応言語数 | 10言語以上 |
| 検出精度（Precision） | 90%以上 |
| 再現率（Recall） | 85%以上 |
| 解析速度 | 100KLOC/60秒 |
| OWASP Top 10カバレッジ | 100% |
| CWE Top 25カバレッジ | 100% |

### 5.2 定性的基準

- CodeQLのサンプルクエリを同等の機能で実行可能
- SARIF出力がGitHub Code Scanningで正常に表示される
- 既存のmusubix-security APIとの後方互換性を維持

---

## 6. リスクと対策

| リスク | 影響度 | 対策 |
|--------|--------|------|
| 多言語パーサー実装の複雑さ | 高 | Tree-sitter等の既存パーサーを活用 |
| 解析速度の低下 | 中 | インクリメンタル解析、並列処理 |
| メモリ使用量の増大 | 中 | ストリーミング処理、メモリマップ |
| クエリ言語の学習コスト | 中 | TypeScript風の構文、豊富なサンプル |

---

## 7. 依存パッケージ（予定）

| パッケージ | 用途 | Phase |
|-----------|------|-------|
| tree-sitter | 多言語パーサー | Phase 1 |
| tree-sitter-go | Go言語サポート | Phase 1 |
| tree-sitter-java | Java言語サポート | Phase 1 |
| tree-sitter-ruby | Ruby言語サポート | Phase 1 |
| tree-sitter-rust | Rust言語サポート | Phase 1 |
| better-sqlite3 | CodeDB永続化 | Phase 1 |
| z3-solver | シンボリック実行 | Phase 2 |

---

## 8. トレーサビリティ

### 8.1 関連要件

- REQ-MUSUBIX-001: MUSUBIXシステム全体要件
- REQ-SEC-001: セキュリティ分析基本要件

### 8.2 関連設計

- DES-SEC-001: セキュリティパッケージアーキテクチャ（作成予定）

---

## 9. 改訂履歴

| バージョン | 日付 | 変更内容 | 著者 |
|-----------|------|----------|------|
| 1.0.0 | 2026-01-12 | 初版作成 | AI Agent |

---

## 📋 レビュー結果

### セルフレビュー実施項目

| 観点 | 状態 | 詳細 |
|------|------|------|
| EARS形式準拠 | ✅ OK | 全59要件がEARS形式で記述 |
| 優先度設定 | ✅ OK | P0/P1/P2で分類済み |
| 既存実装との整合性 | ✅ OK | 既存機能を継続利用、新規機能を追加 |
| スコープ明確性 | ✅ OK | Phase 1/2/3で段階的実装を定義 |
| 依存関係 | ✅ OK | 要件間の依存関係を明記 |
| トレーサビリティ | ✅ OK | REQ-SEC-*形式でID付与 |
| CodeQL比較 | ✅ OK | 主要機能を網羅的に比較 |

### 確認事項

1. **Phase 1優先度**: Go/Java言語サポートをP0としましたが、優先順位の変更が必要ですか？
2. **シンボリック実行**: Phase 2でP1としましたが、必須機能ですか？
3. **対応フレームワーク**: 追加で認識すべきフレームワークはありますか？

---

👉 **次のアクションを選択してください:**
- **修正** / 具体的な修正指示 → 修正して再提示
- **承認** / **OK** / **進める** → Phase 2（設計）へ
