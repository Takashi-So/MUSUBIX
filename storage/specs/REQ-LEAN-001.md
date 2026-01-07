# REQ-LEAN-001: musubix-lean パッケージ要件仕様書

**バージョン**: 2.0.0-alpha.1  
**作成日**: 2026-01-06  
**ステータス**: Draft  
**優先度**: P0  
**トレーサビリティ**: ROADMAP-v2.md Phase 1 Section 3.2

---

## 1. 概要

### 1.1 目的

musubix-lean パッケージは、TypeScript/JavaScriptコードに対するLean 4形式検証統合を提供する。EARS形式要件から形式仕様への変換、定理証明の自動生成、およびReProver統合による証明探索を実現する。

### 1.2 スコープ

- Lean 4証明支援系との連携
- EARS要件からLean定理への変換
- TypeScriptコードプロパティの仕様化
- 証明探索と検証フィードバック
- 既存formal-verifyパッケージとの統合

### 1.3 参考資料

| 資料 | 説明 |
|------|------|
| LeanDojo/ReProver | ベストファースト証明探索システム |
| AlphaProof | IMO銀メダル獲得の定理証明システム |
| MUSUBIX formal-verify | 既存Z3/SMTベース検証 |
| Lean 4 Documentation | Lean 4公式ドキュメント |

### 1.4 用語定義

| 用語 | 定義 |
|------|------|
| **Lean 4** | 依存型を持つ関数型プログラミング言語および証明支援系 |
| **定理（Theorem）** | 証明されるべき論理的命題 |
| **証明（Proof）** | 定理が真であることの形式的な根拠 |
| **タクティック（Tactic）** | 証明を構築するための手続き |
| **ReProver** | ニューラルネットワークベースの証明探索システム |
| **証明状態（Proof State）** | 証明構築中の中間状態 |

---

## 2. 機能要件

### 2.1 Lean 4統合 (REQ-LEAN-CORE)

#### REQ-LEAN-CORE-001: Lean 4環境検出
**優先度**: P0  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the system initializes the LeanIntegration component, THE system SHALL detect the installed Lean 4 version and validate compatibility with version 4.0.0 or higher.

**受入基準**:
- Lean 4のパスを自動検出する
- バージョン4.0.0以上を必須とする
- インストールされていない場合はLeanNotFoundErrorをスローする
- 検出結果をキャッシュして再利用する

---

#### REQ-LEAN-CORE-002: Leanプロジェクト初期化
**優先度**: P0  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the user requests Lean project initialization, THE system SHALL create a valid lakefile.lean and Lean 4 project structure in the specified directory.

**受入基準**:
- lakefile.leanを生成する
- 必要なディレクトリ構造を作成する
- MUSUBIXカスタムtacticsライブラリを含める
- lake buildで正常にビルドできる

---

#### REQ-LEAN-CORE-003: Leanファイル生成
**優先度**: P0  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the system converts specifications to Lean code, THE system SHALL generate syntactically valid Lean 4 files that can be parsed by the Lean compiler without errors.

**受入基準**:
- 生成されたLeanコードは構文エラーがない
- UTF-8エンコーディングで出力する
- 適切なimport文を自動付与する
- 生成元の要件IDをコメントで記録する

---

#### REQ-LEAN-CORE-004: Lean実行環境
**優先度**: P0  
**パターン**: Ubiquitous  
**EARS形式**:
> THE system SHALL provide a LeanRunner that can execute Lean 4 commands and capture their output including proof states, errors, and tactic suggestions.

**受入基準**:
- lean --runコマンドを実行できる
- lake buildを実行できる
- 標準出力・標準エラー出力を捕捉する
- タイムアウト設定が可能（デフォルト30秒）

---

### 2.2 EARS→Lean変換 (REQ-LEAN-CONV)

#### REQ-LEAN-CONV-001: 基本EARS変換
**優先度**: P0  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the system receives an EARS requirement in Ubiquitous pattern, THE system SHALL convert it to a Lean theorem declaration with appropriate type signature.

**受入基準**:
- Ubiquitousパターンを定理宣言に変換する
- 要件IDをtheorem名に反映する
- 自然言語の述語をLean型に変換する
- 変換不能な場合は理由を含むエラーを返す

---

#### REQ-LEAN-CONV-002: イベント駆動EARS変換
**優先度**: P0  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the system receives an EARS requirement in Event-driven pattern (WHEN...SHALL), THE system SHALL convert it to a Lean theorem with an implication structure (event → response).

**受入基準**:
- WHEN節を前提条件（仮定）に変換する
- SHALL節を結論に変換する
- 因果関係を論理的含意として表現する

---

#### REQ-LEAN-CONV-003: 状態駆動EARS変換
**優先度**: P1  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the system receives an EARS requirement in State-driven pattern (WHILE...SHALL), THE system SHALL convert it to a Lean theorem with a state predicate and invariant preservation proof obligation.

**受入基準**:
- WHILE節を状態述語に変換する
- 不変条件として表現する
- 状態遷移の整合性を検証可能にする

---

#### REQ-LEAN-CONV-004: 否定EARS変換
**優先度**: P1  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the system receives an EARS requirement in Unwanted pattern (SHALL NOT), THE system SHALL convert it to a Lean theorem proving the negation of the unwanted behavior.

**受入基準**:
- SHALL NOT節を否定命題に変換する
- ¬(unwanted_behavior)として表現する
- 反例による検証をサポートする

---

#### REQ-LEAN-CONV-005: 条件付きEARS変換
**優先度**: P1  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the system receives an EARS requirement in Optional pattern (IF...THEN...SHALL), THE system SHALL convert it to a Lean theorem with conditional logic structure.

**受入基準**:
- IF節を条件述語に変換する
- THEN SHALL節を条件付き結論に変換する
- 条件が偽の場合の動作は未定義とする

---

### 2.3 TypeScript仕様化 (REQ-LEAN-TS)

#### REQ-LEAN-TS-001: 関数シグネチャ変換
**優先度**: P0  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the system analyzes a TypeScript function, THE system SHALL extract its signature and convert it to a Lean function type declaration.

**受入基準**:
- TypeScript関数の引数型を抽出する
- 戻り値型を抽出する
- Lean互換の型に変換する（number→Nat/Int、string→String、boolean→Bool、Array→List）
- ジェネリック型パラメータをサポートする

---

#### REQ-LEAN-TS-002: 事前条件仕様化
**優先度**: P0  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the system identifies a precondition annotation or validation in TypeScript code, THE system SHALL generate a Lean hypothesis representing the precondition.

**受入基準**:
- @precondition JSDocを認識する
- 型ガードを事前条件として抽出する
- 範囲チェック（x > 0、x < 100、x >= 0 && x <= 255）を数学的制約に変換する
- 複数の事前条件をANDで結合する

---

#### REQ-LEAN-TS-003: 事後条件仕様化
**優先度**: P0  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the system identifies a postcondition annotation in TypeScript code, THE system SHALL generate a Lean goal representing the postcondition to be proven.

**受入基準**:
- @postcondition JSDocを認識する
- Result型の成功/失敗条件を抽出する
- 戻り値に対する述語を生成する

---

#### REQ-LEAN-TS-004: 不変条件仕様化
**優先度**: P1  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the system identifies a class invariant annotation in TypeScript code, THE system SHALL generate a Lean structure with an invariant field that must be preserved across all methods.

**受入基準**:
- @invariant JSDocを認識する
- クラス不変条件をLean構造体の制約として表現する
- メソッド呼び出し前後での不変条件保持を検証する

---

### 2.4 証明生成 (REQ-LEAN-PROOF)

#### REQ-LEAN-PROOF-001: 基本証明生成
**優先度**: P0  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the system generates a Lean theorem, THE system SHALL attempt to generate a proof using standard tactics (simp, rfl, decide, native_decide) with a maximum of 5 tactic applications.

**受入基準**:
- 基本tacticsを順次試行する
- 成功した場合は証明を出力する
- 失敗した場合は証明状態を返す
- タクティック適用数を制限する

---

#### REQ-LEAN-PROOF-002: 帰納法証明
**優先度**: P1  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the system encounters a theorem involving recursive data structures, THE system SHALL attempt structural induction proof strategies.

**受入基準**:
- 再帰的データ型を検出する
- inductionタクティックを適用する
- 基底ケースと帰納ケースを分離する
- 帰納仮定を適切に使用する

---

#### REQ-LEAN-PROOF-003: 証明スケッチ生成
**優先度**: P1  
**パターン**: Event-driven  
**EARS形式**:
> WHEN automatic proof generation fails, THE system SHALL generate a proof sketch with sorry markers indicating incomplete parts and provide hints for manual completion.

**受入基準**:
- sorryマーカーを挿入する
- 各sorry箇所に期待される型を記載する
- 証明完了のヒントをコメントで提供する
- 証明進捗率を計算する

---

### 2.5 ReProver統合 (REQ-LEAN-REPROVER)

#### REQ-LEAN-REPROVER-001: ReProver接続
**優先度**: P2  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the user enables ReProver integration, THE system SHALL establish a connection to the ReProver service and verify its availability.

**受入基準**:
- ReProverエンドポイントに接続する
- ヘルスチェックを実行する
- 接続失敗時はフォールバックで基本証明を使用する
- タイムアウト設定が可能

---

#### REQ-LEAN-REPROVER-002: ベストファースト探索
**優先度**: P2  
**パターン**: Event-driven  
**EARS形式**:
> WHEN ReProver is available and basic proof fails, THE system SHALL invoke ReProver's best-first proof search with configurable maximum depth and timeout.

**受入基準**:
- 証明状態をReProverに送信する
- 探索深度上限を設定可能（デフォルト10）
- タイムアウトを設定可能（デフォルト60秒）
- 探索結果を証明に変換する

---

#### REQ-LEAN-REPROVER-003: 証明フィードバック
**優先度**: P2  
**パターン**: Event-driven  
**EARS形式**:
> WHEN proof search fails, THE system SHALL provide detailed feedback including the stuck proof state, attempted tactics, and suggestions for alternative approaches.

**受入基準**:
- 失敗した証明状態を返す
- 試行したtacticsのリストを返す
- 類似の証明済み定理を提案する
- 手動証明のガイダンスを提供する

---

### 2.6 検証フィードバック (REQ-LEAN-FEEDBACK)

#### REQ-LEAN-FEEDBACK-001: 証明成功レポート
**優先度**: P0  
**パターン**: Event-driven  
**EARS形式**:
> WHEN a proof completes successfully, THE system SHALL generate a verification report including the theorem statement, proof term, and verification timestamp.

**受入基準**:
- 定理文を含める
- 証明項（proof term）を含める
- 検証タイムスタンプを記録する
- 要件IDへのトレーサビリティを含める

---

#### REQ-LEAN-FEEDBACK-002: 証明失敗診断
**優先度**: P0  
**パターン**: Event-driven  
**EARS形式**:
> WHEN proof generation fails, THE system SHALL provide a diagnostic report including the failure point, expected vs actual types, and potential fixes.

**受入基準**:
- 失敗箇所を特定する
- 型の不一致を報告する
- 自動修正候補を提案する
- エラーメッセージを人間が読みやすく整形する

---

#### REQ-LEAN-FEEDBACK-003: 反例生成
**優先度**: P1  
**パターン**: Event-driven  
**EARS形式**:
> WHEN a theorem is proven false or a counterexample is found, THE system SHALL generate a concrete counterexample demonstrating why the property does not hold.

**受入基準**:
- 具体的な反例値を生成する
- 反例がどの前提に違反するか示す
- TypeScriptコードでの再現方法を提示する

---

### 2.7 CLI/API (REQ-LEAN-API)

#### REQ-LEAN-API-001: LeanIntegration API
**優先度**: P0  
**パターン**: Ubiquitous  
**EARS形式**:
> THE system SHALL provide a LeanIntegration class with methods for initialization, theorem conversion, and proof verification.

**受入基準**:
- new LeanIntegration(options) でインスタンス化できる
- initialize()で環境セットアップする
- earsToTheorem(requirement)で変換する
- prove(theorem)で証明を試みる
- verify(proof)で証明を検証する

---

#### REQ-LEAN-API-002: CLIコマンド
**優先度**: P0  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the user invokes the CLI with lean subcommand, THE system SHALL provide commands for conversion (ears-to-lean), verification (verify), and proof search (prove).

**受入基準**:
- `musubix lean convert <requirements.md>` で変換する
- `musubix lean verify <theorem.lean>` で検証する
- `musubix lean prove <theorem.lean>` で証明探索する
- `musubix lean init` でLeanプロジェクトを初期化する

---

#### REQ-LEAN-API-003: MCPツール統合
**優先度**: P1  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the MCP server receives a lean_verify tool call, THE system SHALL execute the verification pipeline and return structured results.

**受入基準**:
- lean_convert ツールを提供する
- lean_verify ツールを提供する
- lean_prove ツールを提供する
- JSON形式で結果を返す

---

### 2.8 formal-verify統合 (REQ-LEAN-INTEG)

#### REQ-LEAN-INTEG-001: Z3との相互運用
**優先度**: P1  
**パターン**: Event-driven  
**EARS形式**:
> WHEN the user requests hybrid verification, THE system SHALL coordinate between Z3 (for decidable fragments) and Lean 4 (for complex properties).

**受入基準**:
- 検証対象を分類する（decidable/undecidable）
- decidable部分はZ3で高速検証する
- undecidable部分はLeanで証明する
- 両結果を統合したレポートを生成する

---

#### REQ-LEAN-INTEG-002: トレーサビリティ維持
**優先度**: P0  
**パターン**: Ubiquitous  
**EARS形式**:
> THE system SHALL maintain full traceability from EARS requirements through Lean theorems to verification results.

**受入基準**:
- 要件ID→Lean定理名のマッピングを保持する
- 証明結果を要件にリンクする
- トレーサビリティマトリクスを更新する

---

## 3. 非機能要件

### 3.1 性能要件

#### REQ-LEAN-PERF-001: 変換性能
**優先度**: P1  
**パターン**: Ubiquitous  
**EARS形式**:
> THE system SHALL complete EARS-to-Lean conversion within 1 second per requirement for requirements of 200 words or fewer.

**受入基準**:
- 変換時間 < 1秒/要件
- メモリ使用量 < 100MB

---

#### REQ-LEAN-PERF-002: 証明探索性能
**優先度**: P1  
**パターン**: Ubiquitous  
**EARS形式**:
> THE system SHALL provide configurable timeout for proof search with a default of 30 seconds and a maximum of 5 minutes.

**受入基準**:
- デフォルトタイムアウト: 30秒
- 最大タイムアウト: 5分
- 進捗コールバックをサポートする

---

### 3.2 エラーハンドリング

#### REQ-LEAN-ERR-001: Lean未インストール時
**優先度**: P0  
**パターン**: Event-driven  
**EARS形式**:
> WHEN Lean 4 is not installed on the system, THE system SHALL provide a clear error message with installation instructions for the user's operating system.

**受入基準**:
- OS検出（Linux/macOS/Windows）
- 適切なインストール手順を表示する
- elanインストーラへのリンクを提供する

---

#### REQ-LEAN-ERR-002: 変換エラーリカバリ
**優先度**: P1  
**パターン**: Event-driven  
**EARS形式**:
> WHEN EARS-to-Lean conversion fails for a specific requirement, THE system SHALL continue processing remaining requirements and report all failures in a consolidated error report.

**受入基準**:
- 部分的成功を許容する
- 失敗した要件のリストを返す
- 各失敗の理由を含める

---

## 4. トレーサビリティマトリクス

| 要件ID | カテゴリ | 優先度 | 設計コンポーネント |
|--------|---------|--------|-------------------|
| REQ-LEAN-CORE-001 | Lean統合 | P0 | LeanEnvironmentDetector |
| REQ-LEAN-CORE-002 | Lean統合 | P0 | LeanProjectInitializer |
| REQ-LEAN-CORE-003 | Lean統合 | P0 | LeanFileGenerator |
| REQ-LEAN-CORE-004 | Lean統合 | P0 | LeanRunner |
| REQ-LEAN-CONV-001 | 変換 | P0 | EarsToLeanConverter |
| REQ-LEAN-CONV-002 | 変換 | P0 | EarsToLeanConverter |
| REQ-LEAN-CONV-003 | 変換 | P1 | EarsToLeanConverter |
| REQ-LEAN-CONV-004 | 変換 | P1 | EarsToLeanConverter |
| REQ-LEAN-CONV-005 | 変換 | P1 | EarsToLeanConverter |
| REQ-LEAN-TS-001 | TS仕様化 | P0 | TypeScriptSpecifier |
| REQ-LEAN-TS-002 | TS仕様化 | P0 | TypeScriptSpecifier |
| REQ-LEAN-TS-003 | TS仕様化 | P0 | TypeScriptSpecifier |
| REQ-LEAN-TS-004 | TS仕様化 | P1 | TypeScriptSpecifier |
| REQ-LEAN-PROOF-001 | 証明生成 | P0 | ProofGenerator |
| REQ-LEAN-PROOF-002 | 証明生成 | P1 | ProofGenerator |
| REQ-LEAN-PROOF-003 | 証明生成 | P1 | ProofGenerator |
| REQ-LEAN-REPROVER-001 | ReProver | P2 | ReProverClient |
| REQ-LEAN-REPROVER-002 | ReProver | P2 | ReProverClient |
| REQ-LEAN-REPROVER-003 | ReProver | P2 | ReProverClient |
| REQ-LEAN-FEEDBACK-001 | フィードバック | P0 | VerificationReporter |
| REQ-LEAN-FEEDBACK-002 | フィードバック | P0 | VerificationReporter |
| REQ-LEAN-FEEDBACK-003 | フィードバック | P1 | VerificationReporter |
| REQ-LEAN-API-001 | API | P0 | LeanIntegration |
| REQ-LEAN-API-002 | CLI | P0 | LeanCLI |
| REQ-LEAN-API-003 | MCP | P1 | LeanMCPTools |
| REQ-LEAN-INTEG-001 | 統合 | P1 | HybridVerifier |
| REQ-LEAN-INTEG-002 | 統合 | P0 | TraceabilityManager |
| REQ-LEAN-PERF-001 | 性能 | P1 | - |
| REQ-LEAN-PERF-002 | 性能 | P1 | - |
| REQ-LEAN-ERR-001 | エラー | P0 | LeanEnvironmentDetector |
| REQ-LEAN-ERR-002 | エラー | P1 | EarsToLeanConverter |

---

## 5. 要件サマリー

| カテゴリ | P0 | P1 | P2 | 合計 |
|---------|----|----|----|----|
| Lean 4統合 | 4 | 0 | 0 | 4 |
| EARS→Lean変換 | 2 | 3 | 0 | 5 |
| TypeScript仕様化 | 3 | 1 | 0 | 4 |
| 証明生成 | 1 | 2 | 0 | 3 |
| ReProver統合 | 0 | 0 | 3 | 3 |
| 検証フィードバック | 2 | 1 | 0 | 3 |
| CLI/API | 2 | 1 | 0 | 3 |
| formal-verify統合 | 1 | 1 | 0 | 2 |
| 性能要件 | 0 | 2 | 0 | 2 |
| エラーハンドリング | 1 | 1 | 0 | 2 |
| **合計** | **16** | **12** | **3** | **31** |

---

## 6. 変更履歴

| バージョン | 日付 | 変更内容 | 著者 |
|-----------|------|----------|------|
| 0.1.0 | 2026-01-06 | 初版作成 | AI Agent |

