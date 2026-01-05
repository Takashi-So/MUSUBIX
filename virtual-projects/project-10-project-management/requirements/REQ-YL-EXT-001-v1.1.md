# YATA Local 拡張機能要件定義書（修正版）

**Document ID**: REQ-YL-EXT-001  
**Version**: 1.1.0  
**Status**: Reviewed  
**Created**: 2026-01-06  
**Updated**: 2026-01-06  
**Author**: GitHub Copilot (Claude Opus 4.5)

---

## 改訂履歴

| バージョン | 日付 | 変更内容 |
|-----------|------|----------|
| 1.0.0 | 2026-01-06 | 初版作成 |
| 1.1.0 | 2026-01-06 | レビュー指摘対応（MOD-001〜005） |

---

## 1. 概要

本文書は、YATA Local機能検証で特定された将来拡張機能について、EARS形式による要件定義を行います。

### 1.1 対象機能

| 機能ID | 名称 | 概要 |
|--------|------|------|
| KGPR | Knowledge Graph Pull Request | ローカルKG → グローバルKGへのPull Request機能 |
| REC | 推論エンジン拡張 | 関連パターンの自動推薦機能 |
| WSL | Wake-Sleep学習 | コードパターンの自動学習・圧縮機能 |

### 1.2 関連ドキュメント

- [YATA-LOCAL-TEST-REPORT.md](../YATA-LOCAL-TEST-REPORT.md) - 機能検証レポート
- [BEST-PRACTICES.md](../../../../packages/yata-local/docs/BEST-PRACTICES.md) - EntityType使用ガイドライン
- [REV-YL-EXT-001.md](./REV-YL-EXT-001.md) - レビュー報告書

---

## 2. KGPR（Knowledge Graph Pull Request）要件

### 2.1 背景

YATA Localはローカル環境での知識グラフ管理を実現しますが、チーム間での知識共有にはYATA Globalとの連携が必要です。KGPRはGitHub Pull Requestモデルに基づき、ローカルの学習成果をグローバルに安全に共有する仕組みを提供します。

### 2.2 機能要件

#### REQ-KGPR-001: KGPR作成

**EARS Pattern**: Event-driven

> **WHEN** ユーザーがローカル知識グラフの変更をグローバルに共有したい場合, **THE** システム **SHALL** 指定されたエンティティと関係性の差分を抽出し、ドラフトKGPRを作成する。

**Acceptance Criteria**:
- [ ] ローカルKGから指定namespace/entityKindのエンティティを抽出できる
- [ ] 差分（新規追加、更新、削除）を計算できる
- [ ] ドラフトKGPRがJSON形式で生成される
- [ ] KGPR IDが一意に採番される（KGPR-YYYYMMDD-NNN形式）

**Priority**: P0  
**Trace**: DES-KGPR-001  
**Test**: TST-KGPR-001, TST-KGPR-002

---

#### REQ-KGPR-002: プライバシーフィルタリング

**EARS Pattern**: State-driven

> **WHILE** KGPRが作成または送信される状態にある場合, **THE** システム **SHALL** 設定されたプライバシーレベル（strict/moderate/none）に基づき、機密情報を自動的にフィルタリングする。

**Acceptance Criteria**:
- [ ] strictレベル: ファイルパス、URL、認証情報、全メタデータをフィルタ
- [ ] moderateレベル: ファイルパス、URL、認証情報をフィルタ
- [ ] noneレベル: フィルタなし
- [ ] フィルタされた項目は`[REDACTED]`に置換される

**Priority**: P0  
**Trace**: DES-KGPR-002  
**Test**: TST-KGPR-003, TST-KGPR-004, TST-KGPR-005

---

#### REQ-KGPR-003: KGPRレビューワークフロー

**EARS Pattern**: Event-driven

> **WHEN** KGPRが送信（submit）された場合, **THE** システム **SHALL** ステータスを`open`に変更し、CLI出力およびオプションのWebhook経由でレビュー担当者に通知する。

**Acceptance Criteria**:
- [ ] ステータス遷移: draft → open → reviewing → approved/changes_requested → merged/closed
- [ ] 各状態遷移にタイムスタンプが記録される
- [ ] レビューコメントが追加できる
- [ ] approve/changes_requested/commentedの判定が可能
- [ ] 通知方法: CLI stdout出力（デフォルト）、Webhook URL（オプション設定）

**Notification Methods**:
| 方法 | 設定 | 説明 |
|------|------|------|
| CLI出力 | デフォルト | `kgpr submit`実行時にコンソールに出力 |
| Webhook | `KGPR_WEBHOOK_URL`環境変数 | HTTP POSTで外部サービスに通知 |
| ファイル | `--notify-file <path>` | 通知内容をファイルに書き出し |

**Priority**: P1  
**Trace**: DES-KGPR-003  
**Test**: TST-KGPR-006, TST-KGPR-007, TST-KGPR-008

---

#### REQ-KGPR-004: KGPRマージ

**EARS Pattern**: Event-driven

> **WHEN** KGPRがapprovedステータスでマージ操作が実行された場合, **THE** システム **SHALL** グローバルKGに差分を適用し、KGPRステータスを`merged`に更新する。

**Acceptance Criteria**:
- [ ] マージ前にコンフリクト検出を実行する
- [ ] コンフリクトがある場合はマージを中止し、詳細を報告する
- [ ] マージ成功時にグローバルKGのバージョンが更新される
- [ ] マージ履歴が監査ログとして記録される

**Priority**: P1  
**Trace**: DES-KGPR-004  
**Test**: TST-KGPR-009, TST-KGPR-010, TST-KGPR-011

---

#### REQ-KGPR-005: KGPR差分プレビュー

**EARS Pattern**: Event-driven

> **WHEN** ユーザーがKGPR差分をプレビューリクエストした場合, **THE** システム **SHALL** 追加・更新・削除されるエンティティと関係性の一覧を人間可読な形式で表示する。

**Acceptance Criteria**:
- [ ] 追加エンティティ数、更新エンティティ数、削除エンティティ数を表示
- [ ] 各エンティティの詳細（名前、タイプ、namespace）を表示
- [ ] Mermaid形式での差分グラフ出力オプション
- [ ] JSON形式での差分エクスポート

**Priority**: P2  
**Trace**: DES-KGPR-005  
**Test**: TST-KGPR-012, TST-KGPR-013

---

## 3. 推論エンジン拡張（REC）要件

### 3.1 背景

YATA Localには基本的な推論エンジンが実装されていますが、パターンの自動推薦機能を追加することで、開発者の意思決定を支援できます。

### 3.2 機能要件

#### REQ-REC-001: コンテキスト分析

**EARS Pattern**: Event-driven

> **WHEN** ユーザーが新しいエンティティを追加しようとした場合, **THE** システム **SHALL** 既存の知識グラフを分析し、関連する可能性のあるエンティティを特定する。

**Acceptance Criteria**:
- [ ] 同一namespace内のエンティティを関連候補として抽出
- [ ] 類似した名前パターンを持つエンティティを特定（Levenshtein距離 ≤ 3）
- [ ] 同一entityKindを持つエンティティとの関係性を推定
- [ ] 関連度スコア（0.0〜1.0）を算出

**Relevance Score Calculation**:
```
score = w1 * namespace_match + w2 * name_similarity + w3 * kind_match + w4 * relationship_count
where:
  w1 = 0.3 (namespace一致: 1.0, 不一致: 0.0)
  w2 = 0.3 (名前類似度: 1 - levenshtein_distance / max_length)
  w3 = 0.2 (entityKind一致: 1.0, 不一致: 0.0)
  w4 = 0.2 (関係数: min(relationship_count / 10, 1.0))
```

**Priority**: P1  
**Trace**: DES-REC-001  
**Test**: TST-REC-001, TST-REC-002, TST-REC-003

---

#### REQ-REC-002: パターン推薦

**EARS Pattern**: Event-driven

> **WHEN** ユーザーがコード生成またはタスク作成を実行した場合, **THE** システム **SHALL** 過去の類似コンテキストで使用されたパターンを推薦リストとして提示する。

**Acceptance Criteria**:
- [ ] 最大5つの推薦パターンを返す
- [ ] 各推薦に信頼度スコア（confidence）を付与
- [ ] 推薦理由（どの類似コンテキストに基づくか）を説明
- [ ] ユーザーフィードバック（accept/reject）を収集可能

**Priority**: P1  
**Trace**: DES-REC-002  
**Test**: TST-REC-004, TST-REC-005

---

#### REQ-REC-003: 推論ルール管理

**EARS Pattern**: Ubiquitous

> **THE** システム **SHALL** カスタム推論ルールの追加・削除・一覧表示機能を提供する。

**Acceptance Criteria**:
- [ ] ルールをJSON/YAML形式で定義可能
- [ ] ルールの優先度設定が可能
- [ ] ルールの有効/無効切り替えが可能
- [ ] デフォルトルールセットが提供される

**Priority**: P2  
**Trace**: DES-REC-003  
**Test**: TST-REC-006, TST-REC-007

---

#### REQ-REC-004: 推論結果説明

**EARS Pattern**: Event-driven

> **WHEN** 推論エンジンが結果を返した場合, **THE** システム **SHALL** 推論チェーン（どのルールがどの順序で適用されたか）を説明可能な形式で提供する。

**Acceptance Criteria**:
- [ ] 適用されたルールのリストを表示
- [ ] 各ルールの入力と出力を表示
- [ ] 推論グラフをMermaid形式で出力可能
- [ ] 信頼度の計算根拠を説明

**Priority**: P2  
**Trace**: DES-REC-004  
**Test**: TST-REC-008, TST-REC-009

---

## 4. Wake-Sleep学習（WSL）要件

### 4.1 背景

Wake-Sleep学習は、神経科学に基づく学習アルゴリズムで、観察（Wake）と統合（Sleep）のサイクルを繰り返すことで、効率的なパターン学習を実現します。

### 4.2 機能要件

#### REQ-WSL-001: Wakeフェーズ - パターン観察

**EARS Pattern**: Event-driven

> **WHEN** 新しいコードファイルまたは成果物が追加された場合, **THE** システム **SHALL** コード構造を解析し、潜在的なパターンを抽出する。

**Acceptance Criteria**:
- [ ] TypeScript/JavaScript/Pythonファイルのパース
- [ ] 関数シグネチャ、クラス構造、インポート関係を抽出
- [ ] 繰り返し出現する構造パターンを検出
- [ ] パターン候補をYATA Localに一時保存

**Priority**: P0  
**Trace**: DES-WSL-001  
**Test**: TST-WSL-001, TST-WSL-002, TST-WSL-003

---

#### REQ-WSL-002: Sleepフェーズ - パターン統合

**EARS Pattern**: Event-driven

> **WHEN** Sleep学習サイクルが実行された場合, **THE** システム **SHALL** 蓄積されたパターン候補を分析し、類似パターンを統合・圧縮する。

**Acceptance Criteria**:
- [ ] 類似度閾値（デフォルト0.8）に基づくパターンクラスタリング
- [ ] 代表パターンの選出（最も汎用的なパターン）
- [ ] パターン信頼度の更新（出現頻度に基づく）
- [ ] 低頻度パターンの減衰・削除

**Priority**: P0  
**Trace**: DES-WSL-002  
**Test**: TST-WSL-004, TST-WSL-005

---

#### REQ-WSL-003: パターン圧縮

**EARS Pattern**: State-driven

> **WHILE** パターンライブラリが閾値（デフォルト1000パターン）を超えた状態にある場合, **THE** システム **SHALL** 低信頼度パターンを自動的に圧縮または削除する。

**Acceptance Criteria**:
- [ ] 信頼度閾値（デフォルト0.3）未満のパターンを削除候補にする
- [ ] `lastUsedAt`フィールドが現在時刻から6ヶ月以上前のパターンに減衰を適用
- [ ] 削除前に確認プロンプトを表示（設定で無効化可能）
- [ ] 圧縮ログを保存

**Usage Tracking**:
| イベント | lastUsedAt更新 |
|---------|---------------|
| パターンが推薦に含まれた | ✅ |
| パターンがマッチした | ✅ |
| パターンがユーザーに表示された | ✅ |
| パターンがaccept/rejectフィードバックを受けた | ✅ |

**Priority**: P1  
**Trace**: DES-WSL-003  
**Test**: TST-WSL-006, TST-WSL-007, TST-WSL-008

---

#### REQ-WSL-004: 学習サイクル自動化

**EARS Pattern**: Optional

> **IF** 自動学習モードが有効な場合, **THEN THE** システム **SHALL** 定期的（デフォルト1時間ごと）にWake-Sleepサイクルを実行する。

**Acceptance Criteria**:
- [ ] cronライクなスケジュール設定
- [ ] バックグラウンド実行（非ブロッキング）
- [ ] 学習サイクル完了時の通知オプション
- [ ] 手動トリガーも可能

**Priority**: P2  
**Trace**: DES-WSL-004  
**Test**: TST-WSL-009, TST-WSL-010

---

#### REQ-WSL-005: 学習状態可視化

**EARS Pattern**: Event-driven

> **WHEN** ユーザーが学習ダッシュボードを表示リクエストした場合, **THE** システム **SHALL** 現在の学習状態（パターン数、信頼度分布、直近の学習履歴）を表示する。

**Acceptance Criteria**:
- [ ] 総パターン数、カテゴリ別パターン数を表示
- [ ] 信頼度分布ヒストグラム
- [ ] 直近10回の学習サイクル履歴
- [ ] JSON/Markdown形式での出力オプション

**Priority**: P2  
**Trace**: DES-WSL-005  
**Test**: TST-WSL-011, TST-WSL-012

---

## 5. 非機能要件

### REQ-NFR-001: パフォーマンス

**EARS Pattern**: Ubiquitous

> **THE** システム **SHALL** 1000エンティティ以下の知識グラフに対して、クエリ応答時間100ms以内を維持する。

**Priority**: P1  
**Test**: TST-NFR-001, TST-NFR-002

---

### REQ-NFR-002: データ整合性

**EARS Pattern**: Unwanted

> **THE** システム **SHALL NOT** データベース操作中にクラッシュした場合でも、知識グラフの整合性を損なわない。

**Priority**: P0  
**Test**: TST-NFR-003, TST-NFR-004

---

### REQ-NFR-003: プライバシー保護

**EARS Pattern**: Ubiquitous

> **THE** システム **SHALL** デフォルトでstrictプライバシーレベルを適用し、ユーザーの明示的な承認なしに機密情報を外部に送信しない。

**Priority**: P0  
**Test**: TST-NFR-005, TST-NFR-006

---

### REQ-NFR-004: 後方互換性

**EARS Pattern**: Ubiquitous

> **THE** システム **SHALL** YATA Local v0.1.0以降のデータベース形式との後方互換性を維持する。

**Compatibility Matrix**:
| YATA Local Version | 互換性 |
|-------------------|--------|
| v0.1.0+ | ✅ 完全互換 |
| v0.0.x | ⚠️ マイグレーション必要 |

**Priority**: P1  
**Test**: TST-NFR-007, TST-NFR-008

---

## 6. テストID一覧

### 6.1 KGPR テスト

| テストID | 対象要件 | テスト内容 |
|---------|---------|-----------|
| TST-KGPR-001 | REQ-KGPR-001 | KGPR作成成功ケース |
| TST-KGPR-002 | REQ-KGPR-001 | KGPR ID採番形式検証 |
| TST-KGPR-003 | REQ-KGPR-002 | strictレベルフィルタリング |
| TST-KGPR-004 | REQ-KGPR-002 | moderateレベルフィルタリング |
| TST-KGPR-005 | REQ-KGPR-002 | noneレベル（フィルタなし） |
| TST-KGPR-006 | REQ-KGPR-003 | ステータス遷移検証 |
| TST-KGPR-007 | REQ-KGPR-003 | CLI通知出力 |
| TST-KGPR-008 | REQ-KGPR-003 | Webhook通知 |
| TST-KGPR-009 | REQ-KGPR-004 | マージ成功ケース |
| TST-KGPR-010 | REQ-KGPR-004 | コンフリクト検出 |
| TST-KGPR-011 | REQ-KGPR-004 | 監査ログ記録 |
| TST-KGPR-012 | REQ-KGPR-005 | 差分プレビュー表示 |
| TST-KGPR-013 | REQ-KGPR-005 | Mermaid形式出力 |

### 6.2 推論エンジン テスト

| テストID | 対象要件 | テスト内容 |
|---------|---------|-----------|
| TST-REC-001 | REQ-REC-001 | namespace内エンティティ抽出 |
| TST-REC-002 | REQ-REC-001 | 名前類似度計算 |
| TST-REC-003 | REQ-REC-001 | 関連度スコア算出 |
| TST-REC-004 | REQ-REC-002 | パターン推薦（最大5件） |
| TST-REC-005 | REQ-REC-002 | フィードバック収集 |
| TST-REC-006 | REQ-REC-003 | ルール追加 |
| TST-REC-007 | REQ-REC-003 | ルール削除・一覧 |
| TST-REC-008 | REQ-REC-004 | 推論チェーン表示 |
| TST-REC-009 | REQ-REC-004 | Mermaid推論グラフ |

### 6.3 Wake-Sleep学習 テスト

| テストID | 対象要件 | テスト内容 |
|---------|---------|-----------|
| TST-WSL-001 | REQ-WSL-001 | TypeScriptパース |
| TST-WSL-002 | REQ-WSL-001 | パターン検出 |
| TST-WSL-003 | REQ-WSL-001 | 一時保存 |
| TST-WSL-004 | REQ-WSL-002 | パターンクラスタリング |
| TST-WSL-005 | REQ-WSL-002 | 信頼度更新 |
| TST-WSL-006 | REQ-WSL-003 | 削除候補選定 |
| TST-WSL-007 | REQ-WSL-003 | lastUsedAt減衰 |
| TST-WSL-008 | REQ-WSL-003 | 圧縮ログ |
| TST-WSL-009 | REQ-WSL-004 | 自動サイクル実行 |
| TST-WSL-010 | REQ-WSL-004 | 手動トリガー |
| TST-WSL-011 | REQ-WSL-005 | ダッシュボード表示 |
| TST-WSL-012 | REQ-WSL-005 | JSON出力 |

### 6.4 非機能要件 テスト

| テストID | 対象要件 | テスト内容 |
|---------|---------|-----------|
| TST-NFR-001 | REQ-NFR-001 | 1000エンティティクエリ性能 |
| TST-NFR-002 | REQ-NFR-001 | 応答時間計測 |
| TST-NFR-003 | REQ-NFR-002 | クラッシュ復旧 |
| TST-NFR-004 | REQ-NFR-002 | トランザクション整合性 |
| TST-NFR-005 | REQ-NFR-003 | strictデフォルト検証 |
| TST-NFR-006 | REQ-NFR-003 | 機密情報漏洩防止 |
| TST-NFR-007 | REQ-NFR-004 | v0.1.0互換性 |
| TST-NFR-008 | REQ-NFR-004 | マイグレーション検証 |

---

## 7. 要件サマリー

### 7.1 優先度別要件数

| 優先度 | KGPR | REC | WSL | NFR | 合計 |
|--------|------|-----|-----|-----|------|
| P0 | 2 | 0 | 2 | 2 | 6 |
| P1 | 2 | 2 | 1 | 2 | 7 |
| P2 | 1 | 2 | 2 | 0 | 5 |
| **合計** | 5 | 4 | 5 | 4 | **18** |

### 7.2 EARS パターン分布

| パターン | 数 |
|---------|-----|
| Event-driven | 11 |
| Ubiquitous | 4 |
| State-driven | 2 |
| Optional | 1 |
| Unwanted | 1 |
| **合計** | 19 |

### 7.3 テスト数

| カテゴリ | テスト数 |
|---------|---------|
| KGPR | 13 |
| REC | 9 |
| WSL | 12 |
| NFR | 8 |
| **合計** | **42** |

---

## 8. 次のステップ

1. [x] 本要件書のレビュー実施 → REV-YL-EXT-001.md
2. [x] レビュー指摘事項の修正 → 本ドキュメント（v1.1.0）
3. [ ] 設計書（DES-YL-EXT-001）の作成
4. [ ] タスク分解（TSK-YL-EXT-001）の作成
5. [ ] 実装フェーズへの移行

---

**Document End**

---

## 修正履歴（v1.1.0）

### MOD-001: REQ-KGPR-003 通知メカニズム明確化
- 「通知可能な状態」を具体的な通知方法（CLI出力、Webhook、ファイル）に変更
- Notification Methods表を追加

### MOD-002: REQ-REC-001 関連度スコア計算方法追記
- 重み付き計算式を追加
- 各要素（namespace, name_similarity, kind, relationship_count）の重みを定義

### MOD-003: REQ-WSL-003 使用定義追加
- `lastUsedAt`フィールドによる判定を明記
- Usage Tracking表を追加（更新トリガーイベント一覧）

### MOD-004: REQ-NFR-004 互換性バージョン明記
- 「v0.1.0以降」と具体的なバージョンを明記
- Compatibility Matrixを追加

### MOD-005: 全要件にテストID追加
- 各要件に`Test:`フィールドを追加
- セクション6「テストID一覧」を新設
- 42テストケースを定義
