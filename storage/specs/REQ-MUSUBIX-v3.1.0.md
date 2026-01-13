# MUSUBIX v3.1.0 要件定義書
# Easy Approach to Requirements Syntax (EARS) 準拠

**文書ID**: REQ-MUSUBIX-v3.1.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-13  
**ステータス**: Draft  
**準拠規格**: EARS（Easy Approach to Requirements Syntax）  
**参照文書**: REQ-IMPROVEMENT-v3.1.0.md

---

## 1. 文書概要

### 1.1 目的

本文書は、MUSUBIX v3.1.0の機能要件をEARS形式で正式に定義する。10仮想プロジェクト開発（410+テスト、114フィードバック、26パターン学習）から得られた知見に基づく。

### 1.2 EARS パターン定義

| パターン | キーワード | 用途 | 構文 |
|----------|-----------|------|------|
| **Ubiquitous** | SHALL | システムが常に満たすべき要件 | THE \<system\> SHALL \<requirement\> |
| **Event-Driven** | WHEN...SHALL | イベント発生時の要件 | WHEN \<trigger\>, THE \<system\> SHALL \<response\> |
| **State-Driven** | WHILE...SHALL | 特定状態における要件 | WHILE \<state\>, THE \<system\> SHALL \<response\> |
| **Unwanted** | SHALL NOT | 禁止事項 | THE \<system\> SHALL NOT \<behavior\> |
| **Optional** | IF...THEN SHALL | 条件付き要件 | IF \<condition\>, THEN THE \<system\> SHALL \<response\> |

### 1.3 優先度定義

| 優先度 | 説明 | 対象バージョン |
|--------|------|---------------|
| **P0** | 必須 - リリースブロッカー | v3.1.0 |
| **P1** | 重要 - 可能な限り実装 | v3.1.0 |
| **P2** | 任意 - 時間があれば | v3.2.0+ |

### 1.4 要件ID体系

```
REQ-<カテゴリ>-<連番>
```

| カテゴリ | 説明 |
|---------|------|
| CLI | コマンドラインインターフェース |
| VAL | 検証機能 |
| LRN | 学習機能 |
| PAT | パターンライブラリ |
| GEN | コード生成 |
| TST | テスト生成 |
| NFR | 非機能要件 |

---

## 2. 機能要件

---

### 2.1 CLI機能要件

---

#### REQ-CLI-001: initコマンドパス正規化

| 属性 | 値 |
|------|-----|
| **ID** | REQ-CLI-001 |
| **名称** | initコマンドパス正規化 |
| **種別** | Event-Driven |
| **優先度** | P0（必須） |
| **報告元** | medical-records, smart-home, music-streaming, pet-care |

**EARS要件**:

> WHEN ユーザーが `musubix init` コマンドに絶対パスを指定した際,  
> THE システム SHALL 指定されたパスを正規化し,  
> AND THE システム SHALL カレントディレクトリとの二重連結を防止し,  
> AND THE システム SHALL 正規化されたパスにプロジェクトを作成する。

**根拠**: 4プロジェクトで絶対パス指定時に `/home/user/MUSUBIX/home/user/project` のような二重パスが生成される問題が報告された。

**受入基準**:
- [ ] AC-001-1: 絶対パス `/home/user/project` が正しく解決される
- [ ] AC-001-2: 相対パス `./project` が正しく解決される
- [ ] AC-001-3: `--force` オプション使用時も正常動作する
- [ ] AC-001-4: 無効なパス指定時にアクショナブルなエラーメッセージを表示する

**トレーサビリティ**: DES-CLI-001, TSK-CLI-001

---

#### REQ-CLI-002: feedbackコマンドガイダンス

| 属性 | 値 |
|------|-----|
| **ID** | REQ-CLI-002 |
| **名称** | feedbackコマンドガイダンス |
| **種別** | 複合型（Ubiquitous + Event-Driven） |
| **優先度** | P1（重要） |
| **報告元** | medical-records, pet-care |

**EARS要件**:

> THE `musubix learn feedback` コマンド SHALL 必須オプション不足時に具体的なガイダンスを表示する。

> THE コマンド SHALL `--artifact-type` オプションのエイリアスとして `-a` を提供する。

> WHEN ユーザーが `--interactive` オプションを指定した際,  
> THE コマンド SHALL 対話形式で必須項目の入力を促す。

**根拠**: `--artifact-type` が必須パラメータであることが分かりにくく、CLIヘルプなしでは使用困難であった。

**受入基準**:
- [ ] AC-002-1: 必須オプション不足時に不足オプション名と例を表示する
- [ ] AC-002-2: `-a design` で `--artifact-type design` と同等に動作する
- [ ] AC-002-3: `--interactive` で対話モードが起動する

**トレーサビリティ**: DES-CLI-002, TSK-CLI-002

---

#### REQ-CLI-003: scaffoldドメインモデル生成

| 属性 | 値 |
|------|-----|
| **ID** | REQ-CLI-003 |
| **名称** | scaffoldドメインモデル生成 |
| **種別** | Event-Driven |
| **優先度** | P1（重要） |
| **報告元** | 全プロジェクト（共通） |

**EARS要件**:

> WHEN ユーザーが `musubix scaffold domain-model <name> -e "Entity1,Entity2,..."` を実行した際,  
> THE システム SHALL 指定された各エンティティに対してTypeScriptファイルを生成し,  
> AND THE システム SHALL BP-CODE-001（Entity Input DTO）パターンを適用し,  
> AND THE システム SHALL BP-CODE-002（Date-based ID Format）パターンを適用し,  
> AND THE システム SHALL BP-CODE-004（Function-based Value Objects）パターンを適用し,  
> AND THE システム SHALL BP-CODE-005（Result Type）パターンを適用し,  
> AND THE システム SHALL 各エンティティのテストファイルを生成する。

**根拠**: 全プロジェクトで同じパターン（Branded ID、Result型、factory関数）を手動で繰り返し実装していた。

**受入基準**:
- [ ] AC-003-1: `src/domain/<entity>.ts` が生成される
- [ ] AC-003-2: `src/domain/<entity>.test.ts` が生成される
- [ ] AC-003-3: 生成コードに `Result<T, E>` 型が適用されている
- [ ] AC-003-4: 生成コードに Branded ID 型が含まれる
- [ ] AC-003-5: テストに `beforeEach` で `resetCounter()` が含まれる

**トレーサビリティ**: DES-CLI-003, TSK-CLI-003

---

### 2.2 検証機能要件

---

#### REQ-VAL-001: Markdown内EARS検出

| 属性 | 値 |
|------|-----|
| **ID** | REQ-VAL-001 |
| **名称** | Markdown内EARS検出 |
| **種別** | Ubiquitous |
| **優先度** | P0（必須） |
| **報告元** | medical-records, smart-home, recipe-sharing |

**EARS要件**:

> THE `musubix requirements validate` コマンド SHALL Markdownテーブル内のEARS構文を検出する。

> THE システム SHALL 箇条書き形式のEARS構文を検出する。

> THE システム SHALL 通常テキスト、テーブル、コードブロック内のEARS構文を区別して解析する。

> THE システム SHALL 検出された要件の総数と内訳を正確に報告する。

**根拠**: 3プロジェクトでMarkdownテーブル内に記述したEARS要件が「要件数0」と報告された。

**受入基準**:
- [ ] AC-004-1: テーブル形式 `| REQ-001 | WHEN... |` 内のEARSが検出される
- [ ] AC-004-2: 箇条書き形式 `- WHEN... THE system SHALL...` のEARSが検出される
- [ ] AC-004-3: コードブロック内のEARSは検出対象外とする
- [ ] AC-004-4: 検出結果に要件ID、パターン種別、行番号を含める

**トレーサビリティ**: DES-VAL-001, TSK-VAL-001

---

#### REQ-VAL-002: 設計トレーサビリティ検証

| 属性 | 値 |
|------|-----|
| **ID** | REQ-VAL-002 |
| **名称** | 設計トレーサビリティ検証 |
| **種別** | Ubiquitous |
| **優先度** | P1（重要） |
| **報告元** | smart-home, document-collaboration |

**EARS要件**:

> THE システム SHALL `musubix design validate` コマンドを提供する。

> THE コマンド SHALL 設計書（DES-*）と要件書（REQ-*）のトレーサビリティを検証する。

> THE コマンド SHALL 設計に紐づかない孤立要件（orphan requirements）を報告する。

> THE コマンド SHALL 要件に紐づかない過剰設計（orphan designs）を報告する。

**根拠**: 要件と設計の対応関係を手動で追跡する必要があり、見落としが発生していた。

**受入基準**:
- [ ] AC-005-1: `musubix design validate` コマンドが実行可能
- [ ] AC-005-2: 孤立要件がリスト表示される
- [ ] AC-005-3: 過剰設計がリスト表示される
- [ ] AC-005-4: 対応率（%）が計算・表示される

**トレーサビリティ**: DES-VAL-002, TSK-VAL-002

---

### 2.3 学習機能要件

---

#### REQ-LRN-001: パターン推薦ガイダンス

| 属性 | 値 |
|------|-----|
| **ID** | REQ-LRN-001 |
| **名称** | パターン推薦ガイダンス |
| **種別** | Event-Driven |
| **優先度** | P1（重要） |
| **報告元** | event-ticketing, inventory-management |

**EARS要件**:

> WHEN ユーザーがエンティティ実装ファイルを新規作成した際,  
> THE システム SHALL 関連する学習済みパターン（BP-CODE-*, BP-DESIGN-*）を推薦する。

> THE システム SHALL 推薦パターンのコードスニペット例を提示する。

> THE システム SHALL 推薦理由（過去の使用頻度、信頼度）を説明する。

**根拠**: 学習済みパターンが25+存在するが、どのパターンを適用すべきか判断が難しかった。

**受入基準**:
- [ ] AC-006-1: 新規エンティティ作成時に推薦が表示される
- [ ] AC-006-2: 推薦に信頼度スコアが含まれる
- [ ] AC-006-3: コードスニペット例が提供される

**トレーサビリティ**: DES-LRN-001, TSK-LRN-001

---

#### REQ-LRN-002: ドメイン固有パターン学習

| 属性 | 値 |
|------|-----|
| **ID** | REQ-LRN-002 |
| **名称** | ドメイン固有パターン学習 |
| **種別** | Event-Driven |
| **優先度** | P1（重要） |
| **報告元** | event-ticketing, inventory-management, fitness-coaching |

**EARS要件**:

> WHEN 特定ドメイン（Eコマース、在庫管理、ヘルスケア等）のパターンが3回以上使用された際,  
> THE システム SHALL 当該パターンをドメイン固有パターンとして分類する。

> WHEN ユーザーが類似ドメインのプロジェクトを開始した際,  
> THE システム SHALL ドメイン固有パターンを優先的に推薦する。

**学習対象ドメインパターン**:

| ドメイン | パターン名 | 用途 |
|---------|-----------|------|
| Eコマース | Optimistic Locking | 在庫競合防止 |
| Eコマース | Hold Pattern | カート一時確保 |
| 在庫管理 | Reorder Point | 自動発注トリガー |
| ヘルスケア | Streak Calculation | 連続日数計算 |
| コラボレーション | CRDT | 同時編集競合解決 |

**受入基準**:
- [ ] AC-007-1: パターンにドメインタグが付与される
- [ ] AC-007-2: ドメインベースの推薦が機能する
- [ ] AC-007-3: 類似ドメイン判定が信頼度80%以上で動作する

**トレーサビリティ**: DES-LRN-002, TSK-LRN-002

---

### 2.4 パターンライブラリ要件

---

#### REQ-PAT-001: 同時実行パターン追加

| 属性 | 値 |
|------|-----|
| **ID** | REQ-PAT-001 |
| **名称** | 同時実行パターン追加 |
| **種別** | Ubiquitous |
| **優先度** | P0（必須） |
| **報告元** | event-ticketing |

**EARS要件**:

> THE システム SHALL 以下の同時実行パターンをパターンライブラリに登録する:
> - PAT-CONC-001: Optimistic Locking（楽観的ロック）
> - PAT-CONC-002: Pessimistic Locking（悲観的ロック）
> - PAT-CONC-003: Hold Pattern（一時確保）
> - PAT-CONC-004: Idempotency Key（冪等性キー）

> THE システム SHALL 各パターンのTypeScriptテンプレートコードを提供する。

> THE システム SHALL 各パターンの適用ガイダンスを提供する。

**根拠**: event-ticketingで同時購入競合問題に対処するため、4つのパターンを手動実装した。

**受入基準**:
- [ ] AC-008-1: `npx musubix learn patterns --category concurrency` で4パターンが表示される
- [ ] AC-008-2: 各パターンのテンプレートコードが取得可能
- [ ] AC-008-3: パターン適用ガイダンスドキュメントが存在する

**トレーサビリティ**: DES-PAT-001, TSK-PAT-001

---

#### REQ-PAT-002: 時間制約パターン追加

| 属性 | 値 |
|------|-----|
| **ID** | REQ-PAT-002 |
| **名称** | 時間制約パターン追加 |
| **種別** | Ubiquitous |
| **優先度** | P1（重要） |
| **報告元** | travel-planner, smart-home, pet-care |

**EARS要件**:

> THE システム SHALL 以下の時間制約パターンをパターンライブラリに登録する:
> - PAT-TIME-001: Expiry Check（有効期限チェック）
> - PAT-TIME-002: Scheduled Action（スケジュール実行）
> - PAT-TIME-003: Interval Management（インターバル管理）
> - PAT-TIME-004: Streak Calculation（連続日数計算）

> THE システム SHALL 各パターンの使用例ドキュメントを提供する。

**根拠**: 3プロジェクトで時間に関連するビジネスロジック（有効期限、スケジュール、連続日数）を個別に実装していた。

**受入基準**:
- [ ] AC-009-1: `npx musubix learn patterns --category time` で4パターンが表示される
- [ ] AC-009-2: 各パターンの使用例がドキュメント化されている

**トレーサビリティ**: DES-PAT-002, TSK-PAT-002

---

### 2.5 コード生成要件

---

#### REQ-GEN-001: Value Object自動生成

| 属性 | 値 |
|------|-----|
| **ID** | REQ-GEN-001 |
| **名称** | Value Object自動生成 |
| **種別** | Event-Driven |
| **優先度** | P1（重要） |
| **報告元** | 全プロジェクト |

**EARS要件**:

> WHEN ユーザーが `musubix codegen vo <name> --type <type>` を実行した際,  
> THE システム SHALL 指定された型のValue Objectを生成する。

> THE 生成コード SHALL BP-CODE-004（Function-based Value Objects）パターンを適用する。

> THE 生成コード SHALL BP-CODE-005（Result Type）パターンを適用する。

**対応タイプ**:

| タイプ | 説明 | 生成内容 |
|--------|------|---------|
| `id` | ブランド型ID | Branded Type + generateXxxId() + resetXxxCounter() |
| `money` | 金額 | amount + currency + バリデーション |
| `temperature` | 温度 | value + unit(℃/℉) + 変換関数 |
| `weight` | 重量 | value + unit(kg/lb) + 変換関数 |
| `duration` | 時間 | minutes/seconds + 変換関数 |
| `percentage` | 割合 | 0-100制約 + バリデーション |
| `custom` | カスタム | ユーザー定義バリデーション |

**受入基準**:
- [ ] AC-010-1: `--type id` で Branded ID が生成される
- [ ] AC-010-2: `--type money` で Money VO が生成される
- [ ] AC-010-3: 生成コードに `Result<T, E>` 型が適用されている
- [ ] AC-010-4: 生成コードにバリデーションロジックが含まれる

**トレーサビリティ**: DES-GEN-001, TSK-GEN-001

---

#### REQ-GEN-002: Status Transition Map生成

| 属性 | 値 |
|------|-----|
| **ID** | REQ-GEN-002 |
| **名称** | Status Transition Map生成 |
| **種別** | Event-Driven |
| **優先度** | P1（重要） |
| **報告元** | event-ticketing, inventory-management, job-matching |

**EARS要件**:

> WHEN ユーザーが `musubix codegen status <entity> --states "s1,s2,s3,..."` を実行した際,  
> THE システム SHALL BP-DESIGN-001（Status Transition Map）パターンを適用したコードを生成する。

> THE システム SHALL `validStatusTransitions` マップを生成する。

> THE システム SHALL `transitionStatus()` 関数を生成する。

> THE システム SHALL Mermaid形式の状態遷移図を出力する。

**生成例**:

```typescript
// 生成される validStatusTransitions マップ
const validStatusTransitions: Record<OrderStatus, OrderStatus[]> = {
  draft: ['submitted', 'cancelled'],
  submitted: ['approved', 'rejected'],
  approved: ['completed', 'cancelled'],
  rejected: [],
  completed: [],
  cancelled: [],
};
```

**受入基準**:
- [ ] AC-011-1: `validStatusTransitions` マップが生成される
- [ ] AC-011-2: `transitionStatus()` 関数が生成される
- [ ] AC-011-3: Mermaid状態遷移図が `*.mmd` ファイルとして出力される

**トレーサビリティ**: DES-GEN-002, TSK-GEN-002

---

### 2.6 テスト生成要件

---

#### REQ-TST-001: Status Transitionテスト生成

| 属性 | 値 |
|------|-----|
| **ID** | REQ-TST-001 |
| **名称** | Status Transitionテスト生成 |
| **種別** | Event-Driven |
| **優先度** | P1（重要） |
| **報告元** | event-ticketing, job-matching |

**EARS要件**:

> WHEN エンティティに `validStatusTransitions` マップが定義されている際,  
> THE システム SHALL 有効遷移の全パターンに対するテストを生成する。

> THE システム SHALL 無効遷移の全パターンに対するテストを生成する。

> THE システム SHALL BP-TEST-005（Status Transition Testing）パターンを適用する。

**根拠**: 状態遷移テストは網羅性が重要だが、手動では漏れが発生しやすい。

**受入基準**:
- [ ] AC-012-1: 有効な遷移がすべてテストされる
- [ ] AC-012-2: 無効な遷移がすべてテストされる
- [ ] AC-012-3: 終端状態（遷移先なし）がテストされる

**トレーサビリティ**: DES-TST-001, TSK-TST-001

---

#### REQ-TST-002: カウンターリセット自動挿入

| 属性 | 値 |
|------|-----|
| **ID** | REQ-TST-002 |
| **名称** | カウンターリセット自動挿入 |
| **種別** | Ubiquitous |
| **優先度** | P0（必須） |
| **報告元** | 全プロジェクト |

**EARS要件**:

> THE テスト生成機能 SHALL BP-TEST-001（Test Counter Reset）パターンを自動適用する。

> THE 生成されるテストファイル SHALL `beforeEach` ブロックを含む。

> THE `beforeEach` ブロック SHALL `resetAllCounters()` 呼び出しを含む。

**根拠**: 全プロジェクトでIDカウンターのリセット忘れによるテスト間干渉が発生した。

**受入基準**:
- [ ] AC-013-1: 生成テストに `beforeEach` ブロックが含まれる
- [ ] AC-013-2: `resetAllCounters()` または個別の `resetXxxCounter()` が呼び出される
- [ ] AC-013-3: テスト間で ID が干渉しない

**トレーサビリティ**: DES-TST-002, TSK-TST-002

---

## 3. 非機能要件

---

#### REQ-NFR-001: アクショナブルエラーメッセージ

| 属性 | 値 |
|------|-----|
| **ID** | REQ-NFR-001 |
| **名称** | アクショナブルエラーメッセージ |
| **種別** | Ubiquitous |
| **優先度** | P1（重要） |
| **報告元** | medical-records, pet-care |

**EARS要件**:

> THE システム SHALL すべてのCLIエラーに対してアクショナブルなエラーメッセージを表示する。

> THE エラーメッセージ SHALL エラー原因を明確に説明する。

> THE エラーメッセージ SHALL 解決方法または次のステップを提案する。

> THE エラーメッセージ SHALL 関連するヘルプコマンドを案内する。

**例**:

```
❌ 現状:
error: required option '-a, --artifact-type <type>' not specified

✅ 改善後:
Error: Missing required option '--artifact-type'

Required: Specify the artifact type using one of:
  -a design    For design artifacts (DES-*)
  -a code      For code artifacts
  -a test      For test artifacts

Example:
  musubix learn feedback "artifact-id" -t accept -a design -r "reason"

Run 'musubix learn feedback --help' for more information.
```

**受入基準**:
- [ ] AC-014-1: エラー原因が1行目に明確に表示される
- [ ] AC-014-2: 解決方法が箇条書きで提示される
- [ ] AC-014-3: 実行例が含まれる
- [ ] AC-014-4: ヘルプコマンドが案内される

**トレーサビリティ**: DES-NFR-001, TSK-NFR-001

---

#### REQ-NFR-002: コマンド応答性能

| 属性 | 値 |
|------|-----|
| **ID** | REQ-NFR-002 |
| **名称** | コマンド応答性能 |
| **種別** | Ubiquitous |
| **優先度** | P2（任意） |

**EARS要件**:

> THE `musubix requirements validate` コマンド SHALL 100要件を5秒以内に検証する。

> THE `musubix learn status` コマンド SHALL 結果を1秒以内に表示する。

> THE `musubix design validate` コマンド SHALL 50設計を3秒以内に検証する。

**受入基準**:
- [ ] AC-015-1: 100要件検証が5秒以内に完了する（CI環境）
- [ ] AC-015-2: 学習ステータス表示が1秒以内に完了する
- [ ] AC-015-3: 50設計検証が3秒以内に完了する（CI環境）

**トレーサビリティ**: DES-NFR-002, TSK-NFR-002

---

## 4. 要件マトリクス

### 4.1 優先度別サマリー

| 優先度 | 要件数 | 要件ID |
|--------|--------|--------|
| **P0** | 4 | REQ-CLI-001, REQ-VAL-001, REQ-PAT-001, REQ-TST-002 |
| **P1** | 10 | REQ-CLI-002, REQ-CLI-003, REQ-VAL-002, REQ-LRN-001, REQ-LRN-002, REQ-PAT-002, REQ-GEN-001, REQ-GEN-002, REQ-TST-001, REQ-NFR-001 |
| **P2** | 1 | REQ-NFR-002 |
| **合計** | **15** | |

### 4.2 カテゴリ別サマリー

| カテゴリ | 要件数 | 要件ID |
|---------|--------|--------|
| CLI機能 | 3 | REQ-CLI-001〜003 |
| 検証機能 | 2 | REQ-VAL-001〜002 |
| 学習機能 | 2 | REQ-LRN-001〜002 |
| パターンライブラリ | 2 | REQ-PAT-001〜002 |
| コード生成 | 2 | REQ-GEN-001〜002 |
| テスト生成 | 2 | REQ-TST-001〜002 |
| 非機能要件 | 2 | REQ-NFR-001〜002 |

### 4.3 EARSパターン別サマリー

| パターン | 要件数 | 要件ID |
|----------|--------|--------|
| Ubiquitous | 8 | REQ-VAL-001, REQ-VAL-002, REQ-PAT-001, REQ-PAT-002, REQ-TST-002, REQ-NFR-001, REQ-NFR-002, REQ-CLI-002* |
| Event-Driven | 7 | REQ-CLI-001, REQ-CLI-003, REQ-LRN-001, REQ-LRN-002, REQ-GEN-001, REQ-GEN-002, REQ-TST-001 |
| 複合型 | 1 | REQ-CLI-002*（Ubiquitous + Event-Driven） |
| State-Driven | 0 | - |
| Unwanted | 0 | - |
| Optional | 0 | - |

*注: REQ-CLI-002はUbiquitous要件とEvent-Driven要件の複合型であり、両方のパターンを含む。

---

## 5. 用語集

| 用語 | 定義 |
|------|------|
| **EARS** | Easy Approach to Requirements Syntax - 要件記述の標準形式 |
| **Branded Type** | TypeScriptの型安全なID型（`type UserId = string & { _brand: 'UserId' }`） |
| **Result Type** | 成功/失敗を表す型（`Result<T, E> = { ok: true, value: T } | { ok: false, error: E }`） |
| **Status Transition Map** | 有効なステータス遷移を定義するマップ |
| **Optimistic Locking** | 楽観的ロック - バージョン番号による競合検出 |
| **Pessimistic Locking** | 悲観的ロック - 排他的なリソースロック |
| **Hold Pattern** | 一時確保パターン - 期限付きリソース予約 |
| **Idempotency Key** | 冪等性キー - 重複処理防止のためのユニークキー |

---

## 6. 変更履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|----------|--------|
| 1.0 | 2026-01-13 | 初版作成 - REQ-IMPROVEMENT-v3.1.0.mdからEARS形式に変換 | AI Agent |
| 1.1 | 2026-01-13 | レビュー修正: REQ-CLI-002を複合型に変更、EARSパターン別サマリー修正 | AI Agent |

---

## 7. 承認

| 役割 | 氏名 | 署名 | 日付 |
|------|------|------|------|
| 作成者 | AI Agent | - | 2026-01-13 |
| レビュアー | | | |
| 承認者 | | | |

---

**文書終端**
