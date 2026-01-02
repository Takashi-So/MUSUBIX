# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
npx @musubix/mcp-server

# スコープ付きパッケージとして
npm install @musubix/core @musubix/mcp-server @musubix/yata-client
```

#### CLI コマンド
- `musubix` - メインCLI
- `musubix-mcp` - MCPサーバー起動

#### Core Package (@musubix/core)
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

#### MCP Server Package (@musubix/mcp-server)
- MCPServer基盤（stdio/SSE対応）
- 34個のMCPツール定義
- 3個のMCPプロンプト定義
- MCPリソース定義
- PlatformAdapter（GitHub Copilot/Cursor対応）

#### YATA Client Package (@musubix/yata-client)
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
