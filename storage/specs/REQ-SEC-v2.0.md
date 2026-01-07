# MUSUBIX Security Subsystem v2.0 要件定義

**プロジェクト**: MUSUBIX Security
**バージョン**: 2.0.0
**ステータス**: Draft
**作成日**: 2026-01-07
**最終更新**: 2026-01-07
**作成者**: AI Agent (Claude)

---

## 1. エグゼクティブサマリー

### 1.1 目的

MUSUBIX Security v2.0は、GitHub Advanced Security (GHAS)の機能を包括的に上回る、Neuro-Symbolic AIベースのセキュリティ分析プラットフォームを提供します。

### 1.2 GitHub Advanced Securityとの比較

| 機能領域 | GitHub GHAS | MUSUBIX Security v2.0 |
|---------|-------------|----------------------|
| コードスキャン | CodeQL (パターンベース) | **Neuro-Symbolic** (LLM + 知識グラフ + 形式検証) |
| シークレット検出 | 正規表現ベース | **エントロピー + コンテキスト + ML分類** |
| 依存関係監査 | Dependabot (CVEデータベース) | **リアルタイムCVE + サプライチェーン分析 + 推移的脆弱性** |
| 自動修正 | Dependabotプルリクエスト | **LLM生成 + Z3形式検証 + 回帰テスト自動生成** |
| テイント分析 | 限定的 | **インタープロシージャ + フレームワーク対応** |
| コンテナセキュリティ | なし | **SBOM生成 + イメージスキャン + ランタイム分析** |
| IaCセキュリティ | なし | **Terraform/Bicep/CloudFormation分析** |
| コンプライアンス | なし | **ASVS/PCI-DSS/HIPAA/SOC2自動マッピング** |
| AI/MLセキュリティ | なし | **プロンプトインジェクション + モデル攻撃検出** |
| リアルタイム分析 | CI/CDのみ | **IDE統合 + CI/CD + ランタイム** |

### 1.3 差別化ポイント

1. **Neuro-Symbolic統合**: LLMの創造性 + 知識グラフの精度 + 形式検証の確実性
2. **自己学習**: セキュリティパターンの継続的学習と適応
3. **完全なトレーサビリティ**: 脆弱性→要件→修正→テストの追跡
4. **ゼロデイ検出**: 未知の脆弱性パターンの推論的検出
5. **修正検証**: Z3ベースの形式検証で修正の安全性を保証

---

## 2. スコープ

### 2.1 対象範囲

- TypeScript/JavaScript/Node.js プロジェクト（プライマリ）
- Python、Java、Go、Rust（セカンダリ）
- インフラストラクチャコード（Terraform、Bicep、CloudFormation）
- コンテナイメージ（Docker、OCI）
- 依存関係（npm、pip、Maven、Cargo）

### 2.2 対象外

- バイナリ解析（将来バージョンで検討）
- ハードウェアセキュリティ
- 物理的セキュリティ

---

## 3. 機能要件

### 3.0 CLIインターフェース（憲法Article II準拠）

#### REQ-SEC2-CLI-001: CLIインターフェース

**EARS**: THE system SHALL expose all security analysis capabilities through a command-line interface following POSIX conventions.

**優先度**: P0（必須）
**カテゴリ**: Core（憲法Article II準拠）
**トレーサビリティ**: DES-SEC2-CLI-001

**受け入れ基準**:
- `musubix-security scan <path>` - 脆弱性スキャン
- `musubix-security taint <path>` - テイント分析
- `musubix-security secrets <path>` - シークレット検出
- `musubix-security audit <path>` - 依存関係監査
- `musubix-security fix <vuln-id>` - 自動修正
- `musubix-security report <path>` - レポート生成
- `musubix-security container <image>` - コンテナスキャン
- `musubix-security iac <path>` - IaCスキャン
- `--format` オプション（json/sarif/html/pdf）
- `--config` オプション（設定ファイル指定）
- `--severity` オプション（最小重大度フィルタ）
- `--help` ヘルプ表示
- 終了コード: 0=成功（脆弱性なし）, 1=脆弱性検出, 2=エラー

---

#### REQ-SEC2-CLI-002: CLI出力フォーマット

**EARS**: WHEN the user specifies an output format, THE system SHALL generate results in the requested format (JSON, SARIF, HTML, PDF, or plain text).

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-CLI-002

**受け入れ基準**:
- JSON: 機械可読形式
- SARIF: GitHub/Azure DevOps統合用
- HTML: 人間可読レポート
- PDF: 監査用レポート
- Plain text: ターミナル出力（デフォルト）

---

### 3.1 静的解析エンジン（SAST）

#### REQ-SEC2-SAST-001: 多言語脆弱性スキャン

**EARS**: THE system SHALL detect security vulnerabilities in TypeScript, JavaScript, Python, Java, Go, and Rust source code with a detection rate of at least 95% for known vulnerability patterns as measured against the OWASP Benchmark v1.2 and Juliet Test Suite.

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-SAST-001

**受け入れ基準**:
- OWASP Top 10 (2021) 全カテゴリをカバー
- CWE Top 25 全項目をカバー
- 誤検出率 5% 未満（OWASP Benchmarkで測定）
- 処理速度 10,000行/秒以上
- ベンチマーク: OWASP Benchmark v1.2、Juliet Test Suite

---

#### REQ-SEC2-SAST-002: Neuro-Symbolic脆弱性推論

**EARS**: WHEN a potential vulnerability is detected, THE system SHALL use both neural (LLM) analysis and symbolic (knowledge graph) reasoning to determine the vulnerability's validity and severity.

**優先度**: P0（必須）
**カテゴリ**: Innovation
**トレーサビリティ**: DES-SEC2-SAST-002

**受け入れ基準**:
- LLMによるコンテキスト理解と脆弱性説明
- YATAナレッジグラフによる既知パターンマッチング
- 信頼度スコア算出（0.0-1.0）
- シンボリック検証で無効な場合はニューラル結果を棄却

---

#### REQ-SEC2-SAST-003: ゼロデイ脆弱性検出

**EARS**: THE system SHALL detect potential zero-day vulnerabilities (defined as vulnerabilities not yet registered in CVE/CWE databases AND not matching known vulnerability patterns) by analyzing code patterns that deviate from secure coding practices stored in the knowledge graph.

**優先度**: P1（重要）
**カテゴリ**: Innovation
**トレーサビリティ**: DES-SEC2-SAST-003

**定義**:
- **ゼロデイ脆弱性**: CVE/CWE未登録かつ既知パターン外の脆弱性
- **検出方法**: 知識グラフのセキュアコーディングパターンからの逸脱分析

**受け入れ基準**:
- 既知パターンに一致しないが危険と推論される箇所を検出
- LLMによる脆弱性の可能性評価（信頼度スコア付き）
- 専門家レビュー待ちとしてフラグ付け（severity: potential）
- 検出理由の説明生成（自然言語 + コード参照）
- 誤検出許容率: 20%以下（ゼロデイ特性を考慮）

---

#### REQ-SEC2-SAST-004: インタープロシージャ解析

**EARS**: THE system SHALL perform inter-procedural analysis to track data flow across function boundaries, modules, and packages.

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-SAST-004

**受け入れ基準**:
- 関数呼び出しチェーン全体の追跡
- モジュール境界を越えたデータフロー分析
- 最大深度: 20呼び出し
- 循環呼び出しの検出と処理

---

### 3.2 テイント分析

#### REQ-SEC2-TAINT-001: 高精度テイント追跡

**EARS**: THE system SHALL track tainted data from sources (user input, external APIs, files) to sinks (database queries, command execution, file operations) with path-sensitive analysis.

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-TAINT-001

**受け入れ基準**:
- 50種類以上のソース識別
- 30種類以上のシンク識別
- パス感度のある追跡（条件分岐を考慮）
- サニタイザーの認識と適切性検証

---

#### REQ-SEC2-TAINT-002: フレームワーク対応テイント

**EARS**: WHEN analyzing framework-based code, THE system SHALL recognize framework-specific data flow patterns for Express, Fastify, Koa, NestJS, Next.js, and Django.

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-TAINT-002

**受け入れ基準**:
- 各フレームワークのミドルウェアパターン理解
- リクエスト/レスポンスライフサイクルの追跡
- デコレータベースルーティングの解析
- カスタムサニタイザーの学習

---

#### REQ-SEC2-TAINT-003: サニタイザー有効性検証

**EARS**: THE system SHALL verify that applied sanitizers are appropriate for the specific sink context (e.g., HTML encoding for DOM insertion, SQL parameterization for database queries).

**優先度**: P1（重要）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-TAINT-003

**受け入れ基準**:
- サニタイザー-シンク適合性マトリクス
- 不適切なサニタイザー使用の警告
- カスタムサニタイザーの安全性評価
- 推奨サニタイザーの提案

---

### 3.3 シークレット検出

#### REQ-SEC2-SECRET-001: 高精度シークレット検出

**EARS**: THE system SHALL detect secrets (API keys, tokens, passwords, certificates) in source code, configuration files, and environment files with a false positive rate below 1%.

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-SECRET-001

**受け入れ基準**:
- 200種類以上のシークレットパターン認識
- エントロピーベース検出（閾値: 4.5）
- コンテキスト分析による誤検出削減
- Git履歴全体のスキャン

---

#### REQ-SEC2-SECRET-002: シークレット分類と優先度付け

**EARS**: WHEN a secret is detected, THE system SHALL classify its type and assign a severity based on potential impact.

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-SECRET-002

**受け入れ基準**:
- 分類: API Key, OAuth Token, Password, Private Key, Certificate, etc.
- 重大度: Critical (本番認証情報), High (外部サービスキー), Medium (開発キー), Low (テストキー)
- サービス識別（AWS, Azure, GCP, Stripe等）
- ローテーション推奨の自動生成

---

#### REQ-SEC2-SECRET-003: リアルタイムシークレット防止

**EARS**: THE system SHALL prevent secrets from being committed to version control by providing pre-commit hooks and IDE integration.

**優先度**: P1（重要）
**カテゴリ**: Prevention
**トレーサビリティ**: DES-SEC2-SECRET-003

**受け入れ基準**:
- pre-commitフック提供
- VS Code拡張でのリアルタイム警告
- コミット時の自動ブロック（設定可能）
- 安全な代替案の提案

---

### 3.4 依存関係セキュリティ

#### REQ-SEC2-DEP-001: 包括的依存関係監査

**EARS**: THE system SHALL audit all direct and transitive dependencies for known vulnerabilities using multiple CVE databases (NVD, GitHub Advisory, Snyk, OSV).

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-DEP-001

**受け入れ基準**:
- npm, pip, Maven, Cargo, Go modules対応
- 推移的依存関係の完全解析
- 複数CVEデータベースの集約
- 毎日の自動更新チェック

---

#### REQ-SEC2-DEP-002: サプライチェーン攻撃検出

**EARS**: THE system SHALL detect potential supply chain attacks including typosquatting, dependency confusion, maintainer hijacking, and malicious package injection.

**優先度**: P0（必須）
**カテゴリ**: Innovation
**トレーサビリティ**: DES-SEC2-DEP-002

**検出対象**:
| 攻撃タイプ | 説明 | 検出方法 |
|-----------|------|----------|
| Typosquatting | 類似名パッケージ | レーベンシュタイン距離 ≤ 2 |
| Dependency Confusion | 内部/外部名前空間混同 | プライベートレジストリ照合 |
| Maintainer Hijacking | メンテナー乗っ取り | npm/PyPI メンテナー変更履歴 |
| Malicious Injection | 悪意あるコード挿入 | post-installスクリプト分析 |
| Star Jacking | 偽のスター数 | GitHub API照合 |

**受け入れ基準**:
- タイポスクワッティング検出（レーベンシュタイン距離 ≤ 2）
- 依存関係混同攻撃の検出（内部/外部名前空間照合）
- パッケージ整合性検証（ハッシュ、署名、Sigstore対応）
- 新規メンテナー変更の警告（過去30日以内の変更）
- post-installスクリプトの静的分析
- 人気度異常検出（ダウンロード数/スター数の不整合）

---

#### REQ-SEC2-DEP-003: SBOM生成と管理

**EARS**: THE system SHALL generate Software Bill of Materials (SBOM) in SPDX and CycloneDX formats for compliance and audit purposes.

**優先度**: P1（重要）
**カテゴリ**: Compliance
**トレーサビリティ**: DES-SEC2-DEP-003

**受け入れ基準**:
- SPDX 2.3形式出力
- CycloneDX 1.5形式出力
- ライセンス情報の自動収集
- コンポーネント依存グラフ生成

---

### 3.5 自動修正エンジン

#### REQ-SEC2-FIX-001: LLM支援修正生成

**EARS**: WHEN a vulnerability is detected, THE system SHALL generate one or more fix candidates using LLM analysis of the vulnerable code and security best practices.

**優先度**: P0（必須）
**カテゴリ**: Innovation
**トレーサビリティ**: DES-SEC2-FIX-001

**受け入れ基準**:
- 脆弱性ごとに1-3個の修正候補
- コンテキストを考慮した修正
- コードスタイル維持
- 修正理由の説明生成

---

#### REQ-SEC2-FIX-002: Z3形式検証

**EARS**: THE system SHALL verify generated fixes using Z3 SMT solver to prove that the fix eliminates the vulnerability without introducing new security issues.

**優先度**: P0（必須）
**カテゴリ**: Innovation
**トレーサビリティ**: DES-SEC2-FIX-002

**受け入れ基準**:
- 修正前後のセキュリティプロパティ検証
- 不変条件の維持証明
- 副作用の検出
- 検証タイムアウト: 30秒

---

#### REQ-SEC2-FIX-003: 回帰テスト自動生成

**EARS**: WHEN a fix is generated, THE system SHALL automatically generate regression tests to verify the fix and prevent future regressions.

**優先度**: P1（重要）
**カテゴリ**: Innovation
**トレーサビリティ**: DES-SEC2-FIX-003

**受け入れ基準**:
- 脆弱性を再現するテストケース
- 修正後の正常動作テスト
- エッジケースのテスト生成
- 既存テストとの整合性

---

### 3.6 コンテナセキュリティ

#### REQ-SEC2-CONTAINER-001: コンテナイメージスキャン

**EARS**: THE system SHALL scan container images for vulnerabilities in base images, installed packages, and application dependencies.

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-CONTAINER-001

**受け入れ基準**:
- Docker、OCI形式対応
- ベースイメージ脆弱性検出
- レイヤーごとの分析
- 最小権限違反の検出

---

#### REQ-SEC2-CONTAINER-002: Dockerfile分析

**EARS**: THE system SHALL analyze Dockerfiles for security misconfigurations and best practice violations.

**優先度**: P1（重要）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-CONTAINER-002

**受け入れ基準**:
- ルートユーザー使用の警告
- 不要なパッケージインストールの検出
- 機密情報のハードコード検出
- マルチステージビルドの推奨

---

### 3.7 IaCセキュリティ

#### REQ-SEC2-IAC-001: インフラコード分析

**EARS**: THE system SHALL analyze Infrastructure as Code files (Terraform, Bicep, CloudFormation, Pulumi) for security misconfigurations.

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-IAC-001

**受け入れ基準**:
- 過剰な権限設定の検出
- パブリックアクセス設定の警告
- 暗号化設定の検証
- ネットワークセグメンテーション検証

---

#### REQ-SEC2-IAC-002: クラウドセキュリティベンチマーク

**EARS**: THE system SHALL validate IaC configurations against CIS benchmarks for AWS, Azure, and GCP.

**優先度**: P1（重要）
**カテゴリ**: Compliance
**トレーサビリティ**: DES-SEC2-IAC-002

**受け入れ基準**:
- CIS AWS Foundations Benchmark v2.0
- CIS Azure Foundations Benchmark v2.0
- CIS GCP Foundations Benchmark v2.0
- 準拠レポート生成

---

### 3.8 AI/MLセキュリティ

#### REQ-SEC2-AI-001: プロンプトインジェクション検出

**EARS**: THE system SHALL detect potential prompt injection vulnerabilities (both direct and indirect) in code that integrates with LLM APIs.

**優先度**: P0（必須）
**カテゴリ**: Innovation
**トレーサビリティ**: DES-SEC2-AI-001

**検出対象**:
| インジェクションタイプ | 説明 | 例 |
|---------------------|------|----|
| Direct Injection | ユーザー入力が直接プロンプトに | `prompt = user_input + instruction` |
| Indirect Injection | 外部データ経由の挿入 | RAGでの悪意あるドキュメント |
| Jailbreak Attempt | 制限回避の試み | "Ignore previous instructions..." |
| Prompt Leaking | システムプロンプト漏洩 | "Repeat your instructions" |

**受け入れ基準**:
- Direct Injection: ユーザー入力の直接プロンプト挿入検出
- Indirect Injection: 外部データソース経由の挿入検出
- テンプレートインジェクションの検出（f-string、template literal）
- Jailbreakパターンの検出（known patterns database）
- サニタイズ推奨（入力検証、出力フィルタリング）
- 安全なプロンプト構築パターンの提案（structured prompts）
- LLM API呼び出し箇所の自動識別（OpenAI, Anthropic, Azure OpenAI等）

---

#### REQ-SEC2-AI-002: モデル入出力検証

**EARS**: THE system SHALL verify that LLM/ML model outputs are properly validated before use in security-sensitive operations.

**優先度**: P1（重要）
**カテゴリ**: Innovation
**トレーサビリティ**: DES-SEC2-AI-002

**受け入れ基準**:
- モデル出力の未検証使用の検出
- 出力サニタイズの推奨
- コンテンツフィルタリングの検証
- 幻覚データの危険性警告

---

### 3.9 コンプライアンス

#### REQ-SEC2-COMP-001: ASVS準拠検証

**EARS**: THE system SHALL verify code compliance with OWASP Application Security Verification Standard (ASVS) Level 1, 2, and 3.

**優先度**: P1（重要）
**カテゴリ**: Compliance
**トレーサビリティ**: DES-SEC2-COMP-001

**受け入れ基準**:
- ASVS v4.0全項目のマッピング
- 自動検証可能項目の検出
- 準拠レポート生成
- ギャップ分析

---

#### REQ-SEC2-COMP-002: マルチスタンダード対応

**EARS**: THE system SHALL support compliance checking for PCI-DSS, HIPAA, SOC2, and GDPR requirements.

**優先度**: P1（重要）
**カテゴリ**: Compliance
**トレーサビリティ**: DES-SEC2-COMP-002

**受け入れ基準**:
- 各スタンダードの技術要件マッピング
- コード実装との対応付け
- 証跡自動収集
- 監査レポート生成

---

### 3.10 レポートと可視化

#### REQ-SEC2-REPORT-001: 包括的セキュリティレポート

**EARS**: THE system SHALL generate comprehensive security reports including vulnerability summary, risk assessment, remediation priorities, and trend analysis.

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-REPORT-001

**受け入れ基準**:
- HTML/PDF/JSON/SARIF形式出力
- エグゼクティブサマリー
- 技術詳細セクション
- 推奨アクション優先度付け

---

#### REQ-SEC2-REPORT-002: セキュリティダッシュボード

**EARS**: THE system SHALL provide a real-time security dashboard showing vulnerability counts, trends, and risk scores.

**優先度**: P1（重要）
**カテゴリ**: UX
**トレーサビリティ**: DES-SEC2-REPORT-002

**受け入れ基準**:
- リアルタイム更新
- 時系列トレンドグラフ
- リスクスコア計算
- カテゴリ別分布

---

### 3.11 統合機能

#### REQ-SEC2-INT-001: IDE統合

**EARS**: THE system SHALL integrate with VS Code to provide real-time security analysis and inline vulnerability warnings.

**優先度**: P0（必須）
**カテゴリ**: Integration
**トレーサビリティ**: DES-SEC2-INT-001

**受け入れ基準**:
- VS Code Language Server Protocol対応
- インライン診断表示
- Quick Fix提案
- CodeLensによる脆弱性インジケータ

---

#### REQ-SEC2-INT-002: CI/CD統合

**EARS**: THE system SHALL provide CI/CD pipeline integration for GitHub Actions, GitLab CI, Azure DevOps, and Jenkins.

**優先度**: P0（必須）
**カテゴリ**: Integration
**トレーサビリティ**: DES-SEC2-INT-002

**受け入れ基準**:
- 各プラットフォーム用アクション/ステップ提供
- SARIF形式出力でネイティブ統合
- 品質ゲート設定（重大度閾値）
- プルリクエストコメント自動投稿

---

#### REQ-SEC2-INT-003: MCP Server統合

**EARS**: THE system SHALL expose all security analysis capabilities through the Model Context Protocol (MCP) for AI agent integration.

**優先度**: P0（必須）
**カテゴリ**: Integration
**トレーサビリティ**: DES-SEC2-INT-003

**受け入れ基準**:
- MCP Tools: security_scan, taint_analyze, fix_generate, secret_detect
- MCP Prompts: security_review, vulnerability_explain
- MUSUBIX MCPサーバーとの統合
- ストリーミングレスポンス対応

---

## 4. 非機能要件

### 4.1 パフォーマンス

#### REQ-SEC2-PERF-001: スキャン速度

**EARS**: THE system SHALL complete a full security scan of 100,000 lines of code within 60 seconds on standard hardware (4 cores, 8GB RAM).

**優先度**: P0（必須）
**受け入れ基準**:
- 平均処理速度: 1,700行/秒以上
- インクリメンタルスキャン: 変更ファイルのみ
- 並列処理対応

---

#### REQ-SEC2-PERF-002: メモリ効率

**EARS**: THE system SHALL NOT exceed 2GB of memory usage during analysis of projects up to 1 million lines of code.

**優先度**: P0（必須）
**受け入れ基準**:
- メモリ使用量上限: 2GB
- ストリーミング処理対応
- 大規模ファイルの分割処理

---

### 4.2 信頼性

#### REQ-SEC2-REL-001: 検出精度

**EARS**: THE system SHALL achieve a precision of at least 95% and recall of at least 90% for known vulnerability patterns.

**優先度**: P0（必須）
**受け入れ基準**:
- Precision ≥ 95%
- Recall ≥ 90%
- F1スコア ≥ 92%

---

### 4.3 セキュリティ

#### REQ-SEC2-SEC-001: 自己セキュリティ

**EARS**: THE system SHALL NOT introduce security vulnerabilities in its own implementation and SHALL be validated against its own scanning capabilities.

**優先度**: P0（必須）
**受け入れ基準**:
- セルフスキャン合格
- 定期的なセキュリティ監査
- 依存関係の最小化

---

### 4.4 拡張性

#### REQ-SEC2-EXT-001: カスタムルール

**EARS**: THE system SHALL allow users to define custom security rules using a declarative YAML format.

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-EXT-001

**受け入れ基準**:
- YAMLベースルール定義
- パターンマッチングDSL（AST、正規表現、セマンティック）
- ルールテスト機能（サンプルコードでの検証）
- ルールインポート/エクスポート
- コミュニティルール共有機能

---

### 3.12 監査ログ

#### REQ-SEC2-LOG-001: セキュリティ監査ログ

**EARS**: THE system SHALL log all security analysis activities including scan executions, detected vulnerabilities, applied fixes, and configuration changes for audit purposes.

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-LOG-001

**受け入れ基準**:
- スキャン実行ログ（開始/終了時刻、対象、結果サマリー）
- 脆弱性検出ログ（ID、重大度、場所、検出ルール）
- 修正適用ログ（修正前後のコード、検証結果）
- 設定変更ログ（変更者、変更内容、タイムスタンプ）
- ログ形式: JSON Lines（構造化ログ）
- ログローテーション対応
- ログ改ざん検出（ハッシュチェーン）

---

#### REQ-SEC2-LOG-002: ログエクスポート

**EARS**: THE system SHALL support exporting audit logs to external SIEM systems (Splunk, Elasticsearch, Azure Sentinel).

**優先度**: P1（重要）
**カテゴリ**: Integration
**トレーサビリティ**: DES-SEC2-LOG-002

**受け入れ基準**:
- Syslog出力対応
- Webhook通知対応
- Splunk HEC対応
- Elasticsearch直接出力対応
- カスタムエクスポーター拡張ポイント

---

### 3.13 エラーハンドリング

#### REQ-SEC2-ERR-001: グレースフルエラーハンドリング

**EARS**: WHEN an error occurs during security analysis, THE system SHALL handle the error gracefully, log the error details, and continue processing remaining files when possible.

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-ERR-001

**受け入れ基準**:
- 単一ファイル解析失敗時も他ファイルの処理を継続
- エラー詳細のログ出力（スタックトレース、コンテキスト）
- エラーサマリーの最終レポート含有
- リトライ可能なエラーの自動リトライ（最大3回）
- タイムアウト設定（ファイル単位、全体）

---

### 3.14 設定管理

#### REQ-SEC2-CFG-001: 設定ファイル管理

**EARS**: THE system SHALL support configuration through YAML files (.musubix-security.yaml) with environment variable overrides and CLI argument precedence.

**優先度**: P0（必須）
**カテゴリ**: Core
**トレーサビリティ**: DES-SEC2-CFG-001

**受け入れ基準**:
- 設定ファイル: `.musubix-security.yaml`
- 設定優先順位: CLI引数 > 環境変数 > 設定ファイル > デフォルト
- 設定スキーマ検証（JSON Schema）
- 設定テンプレート生成コマンド
- プロジェクト継承設定（extends）

---

## 5. トレーサビリティマトリクス

### 5.1 要件 → 設計

| 要件ID | 設計ID | 実装コンポーネント |
|--------|--------|-------------------|
| REQ-SEC2-CLI-001 | DES-SEC2-CLI-001 | SecurityCLI |
| REQ-SEC2-CLI-002 | DES-SEC2-CLI-002 | OutputFormatter |
| REQ-SEC2-SAST-001 | DES-SEC2-SAST-001 | VulnerabilityScanner |
| REQ-SEC2-SAST-002 | DES-SEC2-SAST-002 | NeuroSymbolicAnalyzer |
| REQ-SEC2-SAST-003 | DES-SEC2-SAST-003 | ZeroDayDetector |
| REQ-SEC2-SAST-004 | DES-SEC2-SAST-004 | InterproceduralAnalyzer |
| REQ-SEC2-TAINT-001 | DES-SEC2-TAINT-001 | TaintTracker |
| REQ-SEC2-TAINT-002 | DES-SEC2-TAINT-002 | FrameworkAdapter |
| REQ-SEC2-TAINT-003 | DES-SEC2-TAINT-003 | SanitizerVerifier |
| REQ-SEC2-SECRET-001 | DES-SEC2-SECRET-001 | SecretDetector |
| REQ-SEC2-SECRET-002 | DES-SEC2-SECRET-002 | SecretClassifier |
| REQ-SEC2-SECRET-003 | DES-SEC2-SECRET-003 | PreCommitHook |
| REQ-SEC2-DEP-001 | DES-SEC2-DEP-001 | DependencyAuditor |
| REQ-SEC2-DEP-002 | DES-SEC2-DEP-002 | SupplyChainAnalyzer |
| REQ-SEC2-DEP-003 | DES-SEC2-DEP-003 | SBOMGenerator |
| REQ-SEC2-FIX-001 | DES-SEC2-FIX-001 | LLMFixGenerator |
| REQ-SEC2-FIX-002 | DES-SEC2-FIX-002 | Z3Verifier |
| REQ-SEC2-FIX-003 | DES-SEC2-FIX-003 | TestGenerator |
| REQ-SEC2-CONTAINER-001 | DES-SEC2-CONTAINER-001 | ImageScanner |
| REQ-SEC2-CONTAINER-002 | DES-SEC2-CONTAINER-002 | DockerfileAnalyzer |
| REQ-SEC2-IAC-001 | DES-SEC2-IAC-001 | IaCAnalyzer |
| REQ-SEC2-IAC-002 | DES-SEC2-IAC-002 | CISBenchmarkValidator |
| REQ-SEC2-AI-001 | DES-SEC2-AI-001 | PromptInjectionDetector |
| REQ-SEC2-AI-002 | DES-SEC2-AI-002 | ModelOutputValidator |
| REQ-SEC2-COMP-001 | DES-SEC2-COMP-001 | ASVSValidator |
| REQ-SEC2-COMP-002 | DES-SEC2-COMP-002 | ComplianceEngine |
| REQ-SEC2-REPORT-001 | DES-SEC2-REPORT-001 | ReportGenerator |
| REQ-SEC2-REPORT-002 | DES-SEC2-REPORT-002 | SecurityDashboard |
| REQ-SEC2-INT-001 | DES-SEC2-INT-001 | VSCodeExtension |
| REQ-SEC2-INT-002 | DES-SEC2-INT-002 | CIPipelineIntegration |
| REQ-SEC2-INT-003 | DES-SEC2-INT-003 | SecurityMCPServer |
| REQ-SEC2-LOG-001 | DES-SEC2-LOG-001 | AuditLogger |
| REQ-SEC2-LOG-002 | DES-SEC2-LOG-002 | LogExporter |
| REQ-SEC2-ERR-001 | DES-SEC2-ERR-001 | ErrorHandler |
| REQ-SEC2-CFG-001 | DES-SEC2-CFG-001 | ConfigManager | |

### 5.2 要件統計

| カテゴリ | P0（必須） | P1（重要） | P2（任意） | 合計 |
|---------|----------|----------|----------|------|
| CLI | 2 | 0 | 0 | 2 |
| SAST | 3 | 1 | 0 | 4 |
| Taint | 2 | 1 | 0 | 3 |
| Secret | 2 | 1 | 0 | 3 |
| Dependency | 2 | 1 | 0 | 3 |
| Fix | 2 | 1 | 0 | 3 |
| Container | 1 | 1 | 0 | 2 |
| IaC | 1 | 1 | 0 | 2 |
| AI/ML | 1 | 1 | 0 | 2 |
| Compliance | 0 | 2 | 0 | 2 |
| Report | 1 | 1 | 0 | 2 |
| Integration | 3 | 0 | 0 | 3 |
| Log | 1 | 1 | 0 | 2 |
| Error | 1 | 0 | 0 | 1 |
| Config | 1 | 0 | 0 | 1 |
| Performance | 2 | 0 | 0 | 2 |
| Reliability | 1 | 0 | 0 | 1 |
| Security | 1 | 0 | 0 | 1 |
| Extensibility | 1 | 0 | 0 | 1 |
| **合計** | **28** | **12** | **0** | **40** |

---

## 6. 用語集

| 用語 | 定義 |
|------|------|
| SAST | Static Application Security Testing - 静的アプリケーションセキュリティテスト |
| テイント分析 | 汚染されたデータ（ユーザー入力等）の追跡分析 |
| SBOM | Software Bill of Materials - ソフトウェア部品表 |
| ASVS | Application Security Verification Standard - OWASP認証基準 |
| CWE | Common Weakness Enumeration - 共通脆弱性タイプ |
| SARIF | Static Analysis Results Interchange Format |
| IaC | Infrastructure as Code |
| MCP | Model Context Protocol |

---

## 7. 改訂履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 0.1.0 | 2026-01-07 | 初版作成 | AI Agent |
| 0.2.0 | 2026-01-07 | レビュー指摘を反映: CLI要件追加、監査ログ要件追加、曖昧性解消、優先度見直し | AI Agent |

---

**次のステップ**:
1. ステークホルダーレビュー
2. 要件の優先度最終決定
3. C4設計ドキュメント作成
4. プロトタイプ実装計画

