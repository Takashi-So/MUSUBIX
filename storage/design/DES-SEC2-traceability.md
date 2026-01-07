# MUSUBIX Security v2.0 トレーサビリティマトリクス

**プロジェクト**: MUSUBIX Security Subsystem
**バージョン**: 2.0.0
**ステータス**: Draft
**作成日**: 2026-01-07
**関連ドキュメント**: 
- [要件定義書](../specs/REQ-SEC-v2.0.md)
- [アーキテクチャ設計書](DES-SEC2-architecture.md)
- [コンポーネント設計書](DES-SEC2-components.md)
- [コード設計書](DES-SEC2-code.md)
- [動的設計書](DES-SEC2-sequences.md)

---

## 1. 要件→設計 トレーサビリティマトリクス

### 1.1 CLI/インターフェース要件

| 要件ID | 要件タイトル | 優先度 | 設計ID | コンポーネント | ファイル | テストID |
|--------|-------------|--------|--------|---------------|---------|---------|
| REQ-SEC2-CLI-001 | CLI標準コマンド | P0 | DES-SEC2-CLI-001 | SecurityCLI | src/cli/index.ts | TST-SEC2-CLI-001 |
| REQ-SEC2-CLI-002 | CLIヘルプ・終了コード | P0 | DES-SEC2-CLI-001 | SecurityCLI | src/cli/index.ts | TST-SEC2-CLI-002 |

### 1.2 SAST要件

| 要件ID | 要件タイトル | 優先度 | 設計ID | コンポーネント | ファイル | テストID |
|--------|-------------|--------|--------|---------------|---------|---------|
| REQ-SEC2-SAST-001 | 脆弱性パターン検出 | P0 | DES-SEC2-SAST-001 | VulnerabilityScanner | src/analyzers/sast/vulnerability-scanner.ts | TST-SEC2-SAST-001 |
| REQ-SEC2-SAST-002 | Neuro-Symbolic分析 | P0 | DES-SEC2-SAST-002 | NeuroSymbolicCore | src/intelligence/neuro-symbolic-core.ts | TST-SEC2-SAST-002 |
| REQ-SEC2-SAST-003 | ゼロデイ検出 | P1 | DES-SEC2-SAST-003 | ZeroDayDetector | src/analyzers/sast/zero-day-detector.ts | TST-SEC2-SAST-003 |
| REQ-SEC2-SAST-004 | インタープロシージャ解析 | P0 | DES-SEC2-SAST-004 | InterproceduralAnalyzer | src/analyzers/sast/interprocedural-analyzer.ts | TST-SEC2-SAST-004 |

### 1.3 テイント分析要件

| 要件ID | 要件タイトル | 優先度 | 設計ID | コンポーネント | ファイル | テストID |
|--------|-------------|--------|--------|---------------|---------|---------|
| REQ-SEC2-TAINT-001 | ソース・シンク識別 | P0 | DES-SEC2-TAINT-001 | TaintTracker | src/analyzers/taint/taint-tracker.ts | TST-SEC2-TAINT-001 |
| REQ-SEC2-TAINT-002 | フレームワーク対応 | P0 | DES-SEC2-TAINT-002 | FrameworkAdapters | src/analyzers/taint/adapters/*.ts | TST-SEC2-TAINT-002 || REQ-SEC2-TAINT-003 | サニタイザー有効性検証 | P1 | DES-SEC2-TAINT-003 | SanitizerVerifier | src/analyzers/taint/sanitizer-verifier.ts | TST-SEC2-TAINT-003 |
### 1.4 シークレット検出要件

| 要件ID | 要件タイトル | 優先度 | 設計ID | コンポーネント | ファイル | テストID |
|--------|-------------|--------|--------|---------------|---------|---------|
| REQ-SEC2-SECRET-001 | シークレットパターン検出 | P0 | DES-SEC2-SECRET-001 | SecretDetector | src/analyzers/secrets/secret-detector.ts | TST-SEC2-SECRET-001 |
| REQ-SEC2-SECRET-002 | シークレット分類と優先度付け | P0 | DES-SEC2-SECRET-002 | SecretClassifier | src/analyzers/secrets/secret-classifier.ts | TST-SEC2-SECRET-002 |
| REQ-SEC2-SECRET-003 | リアルタイムシークレット防止 | P1 | DES-SEC2-SECRET-003 | PreCommitHook | src/analyzers/secrets/pre-commit-hook.ts | TST-SEC2-SECRET-003 |

### 1.5 依存関係監査要件

| 要件ID | 要件タイトル | 優先度 | 設計ID | コンポーネント | ファイル | テストID |
|--------|-------------|--------|--------|---------------|---------|---------|
| REQ-SEC2-DEP-001 | CVEデータベース照合 | P0 | DES-SEC2-DEP-001 | DependencyAuditor | src/analyzers/dependency/dependency-auditor.ts | TST-SEC2-DEP-001 |
| REQ-SEC2-DEP-002 | サプライチェーン分析 | P0 | DES-SEC2-DEP-002 | SupplyChainAnalyzer | src/analyzers/dependency/supply-chain-analyzer.ts | TST-SEC2-DEP-002 |
| REQ-SEC2-DEP-003 | SBOM生成 | P0 | DES-SEC2-DEP-003 | SBOMGenerator | src/analyzers/dependency/sbom-generator.ts | TST-SEC2-DEP-003 |

### 1.6 自動修正要件

| 要件ID | 要件タイトル | 優先度 | 設計ID | コンポーネント | ファイル | テストID |
|--------|-------------|--------|--------|---------------|---------|---------|
| REQ-SEC2-FIX-001 | LLM修正生成 | P0 | DES-SEC2-FIX-001 | FixGenerator | src/fix/fix-generator.ts | TST-SEC2-FIX-001 |
| REQ-SEC2-FIX-002 | Z3形式検証 | P0 | DES-SEC2-FIX-002 | Z3Verifier | src/fix/z3-verifier.ts | TST-SEC2-FIX-002 |
| REQ-SEC2-FIX-003 | テスト生成 | P0 | DES-SEC2-FIX-003 | TestGenerator | src/fix/test-generator.ts | TST-SEC2-FIX-003 |

### 1.7 コンテナ・IaC要件

| 要件ID | 要件タイトル | 優先度 | 設計ID | コンポーネント | ファイル | テストID |
|--------|-------------|--------|--------|---------------|---------|---------|
| REQ-SEC2-CONTAINER-001 | イメージスキャン | P0 | DES-SEC2-CONTAINER-001 | ImageScanner | src/analyzers/container/image-scanner.ts | TST-SEC2-CONTAINER-001 |
| REQ-SEC2-CONTAINER-002 | Dockerfile分析 | P0 | DES-SEC2-CONTAINER-002 | DockerfileAnalyzer | src/analyzers/container/dockerfile-analyzer.ts | TST-SEC2-CONTAINER-002 |
| REQ-SEC2-IAC-001 | Terraform/K8s分析 | P0 | DES-SEC2-IAC-001 | IaCChecker | src/analyzers/iac/iac-checker.ts | TST-SEC2-IAC-001 |
| REQ-SEC2-IAC-002 | ベンチマーク準拠 | P0 | DES-SEC2-IAC-002 | IaCChecker | src/analyzers/iac/iac-checker.ts | TST-SEC2-IAC-002 |

### 1.8 AI/ML要件

| 要件ID | 要件タイトル | 優先度 | 設計ID | コンポーネント | ファイル | テストID |
|--------|-------------|--------|--------|---------------|---------|---------|
| REQ-SEC2-AI-001 | プロンプトインジェクション検出 | P0 | DES-SEC2-AI-001 | PromptInjectionDetector | src/analyzers/ai/prompt-injection-detector.ts | TST-SEC2-AI-001 |
| REQ-SEC2-AI-002 | LLM出力検証 | P0 | DES-SEC2-AI-002 | PromptInjectionDetector | src/analyzers/ai/prompt-injection-detector.ts | TST-SEC2-AI-002 |

### 1.9 コンプライアンス要件

| 要件ID | 要件タイトル | 優先度 | 設計ID | コンポーネント | ファイル | テストID |
|--------|-------------|--------|--------|---------------|---------|---------|
| REQ-SEC2-COMPLIANCE-001 | セキュリティ標準マッピング | P1 | DES-SEC2-COMPLIANCE-001 | ComplianceValidator | src/compliance/compliance-validator.ts | TST-SEC2-COMPLIANCE-001 |
| REQ-SEC2-COMPLIANCE-002 | コンプライアンスレポート | P1 | DES-SEC2-COMPLIANCE-002 | ComplianceValidator | src/compliance/compliance-validator.ts | TST-SEC2-COMPLIANCE-002 |

### 1.10 レポート要件

| 要件ID | 要件タイトル | 優先度 | 設計ID | コンポーネント | ファイル | テストID |
|--------|-------------|--------|--------|---------------|---------|---------|
| REQ-SEC2-REPORT-001 | 複数形式出力 | P0 | DES-SEC2-REPORT-001 | ReportGenerator | src/report/report-generator.ts | TST-SEC2-REPORT-001 |
| REQ-SEC2-REPORT-002 | SARIF出力 | P0 | DES-SEC2-REPORT-002 | SARIFTemplate | src/report/templates/sarif.ts | TST-SEC2-REPORT-002 |

### 1.11 統合要件

| 要件ID | 要件タイトル | 優先度 | 設計ID | コンポーネント | ファイル | テストID |
|--------|-------------|--------|--------|---------------|---------|---------|
| REQ-SEC2-INT-001 | VS Code LSP統合 | P0 | DES-SEC2-INT-001 | SecurityLSPServer | src/lsp/index.ts | TST-SEC2-INT-001 |
| REQ-SEC2-INT-002 | CI/CD統合 | P0 | DES-SEC2-INT-002 | CLI | src/cli/index.ts | TST-SEC2-INT-002 |
| REQ-SEC2-INT-003 | MCP統合 | P0 | DES-SEC2-INT-003 | SecurityMCPServer | src/mcp/index.ts | TST-SEC2-INT-003 |

### 1.12 ロギング・エラーハンドリング要件

| 要件ID | 要件タイトル | 優先度 | 設計ID | コンポーネント | ファイル | テストID |
|--------|-------------|--------|--------|---------------|---------|---------|
| REQ-SEC2-LOG-001 | 監査ログ記録 | P0 | DES-SEC2-LOG-001 | AuditLogger | src/infrastructure/audit-logger.ts | TST-SEC2-LOG-001 |
| REQ-SEC2-LOG-002 | ログ出力形式 | P0 | DES-SEC2-LOG-002 | AuditLogger | src/infrastructure/audit-logger.ts | TST-SEC2-LOG-002 |
| REQ-SEC2-ERR-001 | エラーリカバリー | P0 | DES-SEC2-ERR-001 | ErrorHandler | src/infrastructure/error-handler.ts | TST-SEC2-ERR-001 |
| REQ-SEC2-CFG-001 | 設定ファイル | P0 | DES-SEC2-CFG-001 | ConfigManager | src/infrastructure/config-manager.ts | TST-SEC2-CFG-001 |

### 1.13 非機能要件

| 要件ID | 要件タイトル | 優先度 | 設計ID | コンポーネント | ファイル | テストID |
|--------|-------------|--------|--------|---------------|---------|---------|
| REQ-SEC2-PERF-001 | スキャン性能 | P0 | DES-SEC2-ORCH-002 | PipelineManager | src/core/pipeline-manager.ts | TST-SEC2-PERF-001 |
| REQ-SEC2-PERF-002 | インクリメンタル分析 | P1 | DES-SEC2-SAST-001 | VulnerabilityScanner | src/analyzers/sast/vulnerability-scanner.ts | TST-SEC2-PERF-002 |
| REQ-SEC2-REL-001 | 偽陽性抑制 | P0 | DES-SEC2-SAST-002 | NeuroSymbolicCore | src/intelligence/neuro-symbolic-core.ts | TST-SEC2-REL-001 |
| REQ-SEC2-REL-002 | グレースフルデグレード | P0 | DES-SEC2-ERR-001 | ErrorHandler | src/infrastructure/error-handler.ts | TST-SEC2-REL-002 |
| REQ-SEC2-SEC-001 | シークレットマスキング | P0 | DES-SEC2-SECRET-001 | SecretDetector | src/analyzers/secrets/secret-detector.ts | TST-SEC2-SEC-001 |
| REQ-SEC2-SEC-002 | セキュアな通信 | P0 | DES-SEC2-INFRA-002 | YATAClient, LLMClient | src/infrastructure/*.ts | TST-SEC2-SEC-002 |
| REQ-SEC2-EXT-001 | プラグインアーキテクチャ | P0 | DES-SEC2-SAST-001 | VulnerabilityScanner | src/analyzers/sast/vulnerability-scanner.ts | TST-SEC2-EXT-001 |
| REQ-SEC2-EXT-002 | API公開 | P1 | DES-SEC2-ORCH-001 | SecurityService | src/core/security-service.ts | TST-SEC2-EXT-002 |

---

## 2. 設計→コンポーネント マッピング

### 2.1 Orchestration Layer

| 設計ID | コンポーネント | 責務 | 依存関係 |
|--------|---------------|------|---------|
| DES-SEC2-ORCH-001 | SecurityService | エントリーポイント、オーケストレーション | PipelineManager, ResultAggregator, All Analyzers |
| DES-SEC2-ORCH-002 | PipelineManager | パイプライン構築・実行 | None |
| DES-SEC2-ORCH-003 | ResultAggregator | 結果集約・重複排除・優先度付け | None |

### 2.2 Analysis Layer

| 設計ID | コンポーネント | 責務 | 依存関係 |
|--------|---------------|------|---------|
| DES-SEC2-SAST-001 | VulnerabilityScanner | 静的脆弱性検出 | ASTParser, RuleEngine |
| DES-SEC2-TAINT-001 | TaintTracker | データフロー追跡 | ASTParser, SourceIdentifier, SinkIdentifier |
| DES-SEC2-SECRET-001 | SecretDetector | シークレット検出 | EntropyCalculator |
| DES-SEC2-DEP-001 | DependencyAuditor | 依存関係監査 | CVEClient, SupplyChainAnalyzer |
| DES-SEC2-CONTAINER-001 | ImageScanner | コンテナイメージスキャン | CVEClient |
| DES-SEC2-IAC-001 | IaCChecker | IaC設定チェック | TerraformAnalyzer, KubernetesAnalyzer |
| DES-SEC2-AI-001 | PromptInjectionDetector | プロンプトインジェクション検出 | TaintTracker, LLMCallIdentifier |

### 2.3 Intelligence Layer

| 設計ID | コンポーネント | 責務 | 依存関係 |
|--------|---------------|------|---------|
| DES-SEC2-SAST-002 | NeuroSymbolicCore | LLM+知識グラフ統合推論 | LLMAnalyzer, KnowledgeQuery |
| DES-SEC2-INT-YATA | KnowledgeQuery | YATA知識グラフクエリ | YATAClient |
| DES-SEC2-INT-LLM | LLMAnalyzer | LLM分析 | LLMClient |

### 2.4 Fix Layer

| 設計ID | コンポーネント | 責務 | 依存関係 |
|--------|---------------|------|---------|
| DES-SEC2-FIX-001 | FixGenerator | LLM修正生成 | NeuroSymbolicCore, LLMClient |
| DES-SEC2-FIX-002 | Z3Verifier | 形式検証 | z3-solver |
| DES-SEC2-FIX-003 | TestGenerator | テスト生成 | None |

### 2.5 Interface Layer

| 設計ID | コンポーネント | 責務 | 依存関係 |
|--------|---------------|------|---------|
| DES-SEC2-CLI-001 | SecurityCLI | CLIインターフェース | SecurityService, ConfigManager |
| DES-SEC2-INT-003 | SecurityMCPServer | MCPプロトコル | SecurityService |
| DES-SEC2-INT-001 | SecurityLSPServer | LSPプロトコル | SecurityService |

### 2.6 Infrastructure Layer

| 設計ID | コンポーネント | 責務 | 依存関係 |
|--------|---------------|------|---------|
| DES-SEC2-INFRA-001 | ASTParser | AST解析 | ts-morph |
| DES-SEC2-INFRA-002 | YATAClient | YATA通信 | None |
| DES-SEC2-INFRA-003 | LLMClient | LLM API通信 | None |
| DES-SEC2-LOG-001 | AuditLogger | 監査ログ | None |
| DES-SEC2-CFG-001 | ConfigManager | 設定管理 | None |
| DES-SEC2-ERR-001 | ErrorHandler | エラーハンドリング | None |

---

## 3. コンポーネント→テスト マッピング

### 3.1 単体テスト

| コンポーネント | テストファイル | テストケース数 | カバレッジ目標 |
|---------------|---------------|--------------|--------------|
| SecurityService | tests/unit/core/security-service.test.ts | 15+ | 90% |
| PipelineManager | tests/unit/core/pipeline-manager.test.ts | 10+ | 90% |
| VulnerabilityScanner | tests/unit/analyzers/vulnerability-scanner.test.ts | 25+ | 95% |
| TaintTracker | tests/unit/analyzers/taint-tracker.test.ts | 20+ | 95% |
| SecretDetector | tests/unit/analyzers/secret-detector.test.ts | 15+ | 95% |
| DependencyAuditor | tests/unit/analyzers/dependency-auditor.test.ts | 15+ | 90% |
| NeuroSymbolicCore | tests/unit/intelligence/neuro-symbolic-core.test.ts | 20+ | 95% |
| FixGenerator | tests/unit/fix/fix-generator.test.ts | 15+ | 90% |
| Z3Verifier | tests/unit/fix/z3-verifier.test.ts | 10+ | 85% |
| TestGenerator | tests/unit/fix/test-generator.test.ts | 10+ | 85% |

### 3.2 統合テスト

| テストシナリオ | テストファイル | 関連要件 |
|--------------|---------------|---------|
| CLIフルスキャン | tests/integration/cli.test.ts | REQ-SEC2-CLI-001 |
| MCP統合スキャン | tests/integration/mcp-server.test.ts | REQ-SEC2-INT-003 |
| LSPリアルタイム診断 | tests/integration/lsp-server.test.ts | REQ-SEC2-INT-001 |
| End-to-Endスキャン | tests/integration/full-scan.test.ts | REQ-SEC2-SAST-001, REQ-SEC2-SAST-002 |
| 修正生成・検証フロー | tests/integration/fix-flow.test.ts | REQ-SEC2-FIX-001, REQ-SEC2-FIX-002 |

### 3.3 E2Eテスト

| テストシナリオ | テストファイル | 関連要件 |
|--------------|---------------|---------|
| 脆弱性検出→修正→検証 | tests/e2e/vulnerability-fix.test.ts | REQ-SEC2-SAST-001, REQ-SEC2-FIX-001〜003 |
| CI/CDパイプライン統合 | tests/e2e/cicd.test.ts | REQ-SEC2-INT-002 |

---

## 4. 憲法条項準拠マトリクス

| 憲法条項 | 要件ID | 準拠状況 |
|---------|--------|---------|
| I. Library-First | 全要件 | ✅ 独立パッケージとして設計 |
| II. CLI Interface | REQ-SEC2-CLI-001, REQ-SEC2-CLI-002 | ✅ CLI要件を明示的に定義 |
| III. Test-First | 全要件 | ✅ テストID列で対応テストを定義 |
| IV. EARS Format | 全要件 | ✅ 全要件がEARS形式 |
| V. Traceability | 本文書 | ✅ 100%トレーサビリティを確保 |
| VI. Project Memory | 設計全体 | ✅ steering/を参照して設計 |
| VII. Design Patterns | ADR-001〜003 | ✅ ADRで設計パターンを文書化 |
| VIII. Decision Records | ADR-001〜003 | ✅ 重要な決定をADRで記録 |
| IX. Quality Gates | TST-SEC2-* | ✅ テストによる品質ゲート |

---

## 5. カバレッジサマリー

### 5.1 要件カバレッジ

| カテゴリ | 要件数 | 設計済み | テスト定義済み | カバレッジ |
|---------|-------|---------|--------------|-----------|
| CLI | 2 | 2 | 2 | 100% |
| SAST | 4 | 4 | 4 | 100% |
| Taint | 3 | 3 | 3 | 100% |
| Secret | 3 | 3 | 3 | 100% |
| Dependency | 3 | 3 | 3 | 100% |
| Fix | 3 | 3 | 3 | 100% |
| Container | 2 | 2 | 2 | 100% |
| IaC | 2 | 2 | 2 | 100% |
| AI/ML | 2 | 2 | 2 | 100% |
| Compliance | 2 | 2 | 2 | 100% |
| Report | 2 | 2 | 2 | 100% |
| Integration | 3 | 3 | 3 | 100% |
| Logging/Error | 4 | 4 | 4 | 100% |
| Non-functional | 5 | 5 | 5 | 100% |
| **合計** | **40** | **40** | **40** | **100%** |

### 5.2 設計成果物サマリー

| 成果物 | ファイル | 状態 |
|--------|---------|------|
| アーキテクチャ設計書 | DES-SEC2-architecture.md | ✅ 完了 |
| コンポーネント設計書 | DES-SEC2-components.md | ✅ 完了 |
| コード設計書 | DES-SEC2-code.md | ✅ 完了 |
| 動的設計書 | DES-SEC2-sequences.md | ✅ 完了 |
| トレーサビリティマトリクス | DES-SEC2-traceability.md | ✅ 完了 |

---

## 6. 次フェーズへの引き継ぎ

### 6.1 実装優先順位

1. **Phase 1: Core Infrastructure** (Week 1-2)
   - SecurityService, PipelineManager, ResultAggregator
   - ConfigManager, ErrorHandler, AuditLogger
   - CLI基本コマンド

2. **Phase 2: Basic Analyzers** (Week 3-4)
   - VulnerabilityScanner（基本検出器）
   - TaintTracker（Express対応）
   - SecretDetector

3. **Phase 3: Neuro-Symbolic Integration** (Week 5-6)
   - NeuroSymbolicCore
   - KnowledgeQuery
   - LLMAnalyzer

4. **Phase 4: Fix Generation** (Week 7-8)
   - FixGenerator
   - Z3Verifier
   - TestGenerator

5. **Phase 5: Advanced Features** (Week 9-10)
   - DependencyAuditor（サプライチェーン分析含む）
   - ImageScanner
   - IaCChecker
   - PromptInjectionDetector

6. **Phase 6: Integration** (Week 11-12)
   - MCP Server
   - LSP Server
   - CI/CD統合
   - E2Eテスト

### 6.2 リスクと軽減策

| リスク | 影響度 | 軽減策 |
|--------|-------|--------|
| Z3学習曲線 | 高 | 早期プロトタイピング、形式検証の専門家レビュー |
| LLM API品質 | 中 | 複数プロバイダー対応、フォールバック戦略 |
| YATA統合複雑性 | 中 | 既存yata-clientパッケージ活用 |
| パフォーマンス目標 | 中 | 並列処理、キャッシュ戦略の早期実装 |

---

## 7. 改訂履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 0.1.0 | 2026-01-07 | 初版作成（全マトリクス） | AI Agent |
| 0.2.0 | 2026-01-07 | レビュー指摘対応: SAST-003/004要件タイトル修正、TAINT-003/SECRET-003追加、カバレッジサマリー更新 | AI Agent |

