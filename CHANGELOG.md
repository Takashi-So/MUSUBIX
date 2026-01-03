# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.0.11] - 2026-01-03

### Added
- **自己学習機能** (REQ-LEARN-001〜006): プロジェクト開発を通じた能動的学習
  - `FeedbackCollector`: ユーザーフィードバック収集・永続化
  - `PatternExtractor`: 繰り返しパターンの自動抽出
  - `LearningEngine`: 適応的推論の統合エンジン
- **CLI learn コマンド**: 自己学習システムの管理
  - `musubix learn status` - 学習状態ダッシュボード
  - `musubix learn feedback <id>` - フィードバック記録
  - `musubix learn patterns` - パターン一覧表示
  - `musubix learn add-pattern <name>` - パターン手動登録
  - `musubix learn remove-pattern <id>` - パターン削除
  - `musubix learn recommend` - コンテキストベースの推奨
  - `musubix learn decay` - 未使用パターンの減衰
  - `musubix learn export` - 学習データエクスポート
  - `musubix learn import <file>` - 学習データインポート
- **プライバシー保護**: 機密情報の自動フィルタリング（REQ-LEARN-006）
- **パターン信頼度**: 使用頻度に基づく動的信頼度計算
- **パターン減衰**: 未使用パターンの自動減衰・アーカイブ

### Tests
- 自己学習モジュール: 23テスト追加
- 全285テスト合格

---

## [1.0.10] - 2026-01-03

### Added
- **EARS検証器**: "shall not" パターンのサポート（unwanted behavior）
- **ArtifactStatus拡張**: `approved`, `implemented`, `verified` ステータス追加
- **トレーサビリティ**: 全体カバレッジ（weighted average）の計算

### Changed
- **EARS検証器**: パターン順序を最適化（特定パターンを汎用パターンより先に評価）
- **信頼度計算**: パターン固有のボーナス値を追加
  - event-driven/state-driven: +0.25
  - unwanted/optional: +0.20
  - complex: +0.30
  - ubiquitous: +0.00
- **パフォーマンス最適化**:
  - EARS検証器: 早期終了（高信頼度≥0.85でマッチ時に即座に返却）
  - EARS検証器: "shall"キーワードの事前チェック
  - トレーサビリティ: リンクインデックス（O(1)検索）

### Fixed
- EARS検証器: すべてのパターンが"ubiquitous"として検出される問題
- トレーサビリティ: `coverage.overall`が`undefined`になる問題
- CLIテスト: requirementsサブコマンド数の期待値を4から5に修正

### Tests
- EARS検証器テスト: 正しいパターン検出を期待するように更新
- 全262テスト合格

---

## [1.0.1] - 2026-01-03

### Added

#### CLI コマンド完全実装（Sprint 6）

すべてのCLIコマンドが実装され、AGENTS.mdおよびドキュメントの記載と完全に一致。

**requirements コマンド**
- `musubix requirements analyze <file>` - 自然言語からEARS要件への変換
- `musubix requirements validate <file>` - EARS構文検証
- `musubix requirements map <file>` - オントロジーマッピング
- `musubix requirements search <query>` - 関連要件検索

**design コマンド**
- `musubix design generate <file>` - 要件から設計生成
- `musubix design patterns <context>` - デザインパターン検出
- `musubix design validate <file>` - SOLID準拠検証
- `musubix design c4 <file>` - C4ダイアグラム生成（Mermaid/PlantUML）
- `musubix design adr <decision>` - ADRドキュメント生成

**codegen コマンド**
- `musubix codegen generate <file>` - 設計からコード生成
- `musubix codegen analyze <file>` - 静的コード解析
- `musubix codegen security <path>` - セキュリティスキャン（CWE対応）

**test コマンド**
- `musubix test generate <file>` - テスト生成（vitest/jest/mocha/pytest対応）
- `musubix test coverage <dir>` - カバレッジ測定・HTMLレポート

**trace コマンド**
- `musubix trace matrix` - トレーサビリティマトリクス生成（HTML/CSV/Markdown）
- `musubix trace impact <id>` - 変更影響分析
- `musubix trace validate` - トレーサビリティリンク検証

**explain コマンド**
- `musubix explain why <id>` - 決定理由の説明生成
- `musubix explain graph <id>` - 推論グラフ生成（Mermaid）

### Changed
- TSK-MUSUBIX-001.md Sprint 6 成果物を完了ステータスに更新

### Fixed
- TypeScript型エラー修正（未使用インポート、プロパティ名修正）

---

## [1.0.0] - 2026-01-02

### 🎉 Initial Release

MUSUBIXの最初の安定版リリース。全56タスク完了、ビルド・テスト通過。

### Added

#### npm/npx インストール対応

```bash
# グローバルインストール
npm install -g musubix

# npx で直接実行
npx musubix init
npx @nahisaho/musubix-mcp-server

# スコープ付きパッケージとして
npm install @nahisaho/musubix-core @nahisaho/musubix-mcp-server @nahisaho/musubix-yata-client
```

#### CLI コマンド
- `musubix` - メインCLI
- `musubix-mcp` - MCPサーバー起動

#### Core Package (@nahisaho/musubix-core)
- **認証・認可** (`auth/`)
  - AuthManager - JWT/OAuth認証管理
  
- **CLIインターフェース** (`cli/`)
  - CLI基盤 - コマンドライン引数解析・ヘルプ表示
  
- **コード生成・解析** (`codegen/`)
  - CodeGenerator - テンプレートベースコード生成
  - StaticAnalyzer - 静的コード解析
  - SecurityScanner - 脆弱性検出
  - PatternConformanceChecker - パターン準拠チェック
  - DependencyAnalyzer - 依存関係分析
  - UnitTestGenerator - ユニットテスト生成
  - IntegrationTestGenerator - 統合テスト生成
  - CoverageReporter - カバレッジレポート
  
- **設計** (`design/`)
  - PatternDetector - デザインパターン検出
  - SOLIDValidator - SOLID原則検証
  - FrameworkOptimizer - フレームワーク最適化
  - C4ModelGenerator - C4モデル生成
  - ADRGenerator - ADR生成
  
- **エラーハンドリング** (`error/`)
  - ErrorHandler - 統一エラーハンドリング
  - GracefulDegradation - グレースフルデグラデーション
  - DataPersistence - データ永続化
  
- **説明生成** (`explanation/`)
  - ReasoningChainRecorder - 推論チェーン記録
  - ExplanationGenerator - 説明生成
  - VisualExplanationGenerator - 視覚的説明生成
  
- **要件分析** (`requirements/`)
  - RequirementsDecomposer - 要件分解
  - RelatedRequirementsFinder - 関連要件検索
  
- **トレーサビリティ** (`traceability/`)
  - TraceabilityManager - トレーサビリティ管理
  - ImpactAnalyzer - 影響分析
  
- **型定義** (`types/`)
  - 共通型定義（common.ts, ears.ts, errors.ts）
  
- **ユーティリティ** (`utils/`)
  - Logger - 構造化ログ
  - DataProtector - データ保護
  - PerformanceProfiler - パフォーマンスプロファイリング
  - ScalabilityOptimizer - スケーラビリティ最適化
  - I18nManager - 国際化対応
  
- **バリデーター** (`validators/`)
  - EARSValidator - EARS形式検証
  - QualityMetricsCalculator - 品質メトリクス計算
  - CodingStandardsChecker - コーディング規約チェック

#### MCP Server Package (@nahisaho/musubix-mcp-server)
- MCPServer基盤（stdio/SSE対応）
- 34個のMCPツール定義
- 3個のMCPプロンプト定義
- MCPリソース定義
- PlatformAdapter（GitHub Copilot/Cursor対応）

#### YATA Client Package (@nahisaho/musubix-yata-client)
- YATAClient基盤
- GraphQueryInterface
- OntologyMapper
- NeuroSymbolicIntegrator
- ConfidenceEvaluator
- ContradictionDetector
- VersionCompatibility

#### テスト
- E2E統合テスト（16テストケース）
- Vitestテストフレームワーク対応

#### ドキュメント
- 要件定義書 (REQ-MUSUBIX-001.md)
- 設計書 (DES-MUSUBIX-001.md)
- タスク定義書 (TSK-MUSUBIX-001.md)
- APIリファレンス (API-REFERENCE.md)
- GitHub Copilot用プロンプト（一問一答形式対応）

### Technical Details

- **言語**: TypeScript 5.3+
- **ランタイム**: Node.js 20+
- **パッケージ管理**: npm workspaces
- **ビルド**: tsc
- **テスト**: Vitest
- **カバレッジ目標**: 
  - ライン: 80%
  - ブランチ: 75%
  - 関数: 90%

### Constitutional Compliance

9条の憲法に完全準拠:
1. Specification First (Article I)
2. Design Before Code (Article II)
3. Single Source of Truth (Article III)
4. Traceability (Article IV)
5. Incremental Progress (Article V)
6. Decision Documentation (Article VI)
7. Quality Gates (Article VII)
8. User-Centric (Article VIII)
9. Continuous Learning (Article IX)

---

## [0.1.0] - 2026-01-01

### Added
- プロジェクト初期化
- 要件定義書ドラフト
- 設計書ドラフト
- 基本プロジェクト構造

---

**文書ID**: CHANGELOG  
**バージョン**: 1.0.0  
**最終更新**: 2026-01-02
