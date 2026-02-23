# SDD開発ワークフロー

MUSUBIXの開発は **SDD（Specification-Driven Development: 仕様駆動型開発）** に基づいています。5つのフェーズを順番に進め、各フェーズで品質ゲート（レビュー→承認）を通過してから次に進みます。

---

## 全体フロー

```
Phase 1          Phase 2        Phase 3          Phase 4         Phase 5
要件定義    →    設計      →    タスク分解  →    実装       →    完了
(REQ-*)         (DES-*)        (TSK-*)          コード          CHANGELOG
                                                テスト          コミット
    ↓              ↓              ↓
  レビュー       レビュー       レビュー
    ↓              ↓              ↓
  承認            承認            承認
```

### フローの制約

- 各フェーズは**ユーザーの明示的な承認**がないと次に進めない
- **Phase 2（設計）→ Phase 4（実装）の直接遷移は禁止**。必ずPhase 3（タスク分解）を経ること
- 承認キーワード: `承認` / `OK` / `LGTM` / `approve` / `進める`

---

## Phase 1: 要件定義

### 目的

何を作るかを **EARS形式** で明確にする。

### 進め方

1. AIエージェントに「〇〇の要件を定義して」と依頼
2. コンテキストが不足している場合、AIが明確化質問を返す
3. EARS形式の要件ドキュメントが生成される
4. 自動レビューが実行される
5. 指摘を修正し、指摘がゼロになるまで繰り返す
6. 「承認」で Phase 2 へ

### EARS形式とは

EARS（Easy Approach to Requirements Syntax）は、要件を曖昧さなく記述するための形式です。

| パターン | 構文 | 使う場面 |
|---------|------|---------|
| **Ubiquitous** | `THE [system] SHALL [requirement]` | システムが常に満たすべき要件 |
| **Event-driven** | `WHEN [event], THE [system] SHALL [response]` | 特定のイベントが発生した時 |
| **State-driven** | `WHILE [state], THE [system] SHALL [response]` | 特定の状態にある間 |
| **Unwanted** | `THE [system] SHALL NOT [behavior]` | やってはいけないこと |
| **Optional** | `IF [condition], THEN THE [system] SHALL [response]` | 条件付きの要件 |

### 例

曖昧な要件:
```
ユーザーがログインできるようにする
```

EARS形式に変換:
```
WHEN a user submits valid credentials,
THE authentication system SHALL generate a JWT token
AND redirect the user to the dashboard within 2 seconds.

THE authentication system SHALL NOT store plain-text passwords.

IF the user fails authentication 5 times,
THEN THE system SHALL lock the account for 30 minutes.
```

### レビュー観点

| 観点 | チェック内容 |
|------|------------|
| EARS形式準拠 | 5つのパターンのいずれかに該当するか |
| 測定可能性 | 応答時間、文字数制限など定量的な基準があるか |
| 網羅性 | 正常系・異常系・境界条件がカバーされているか |
| 整合性 | 既存の要件と矛盾がないか |
| 優先度 | P0（必須）/ P1（重要）/ P2（任意）が設定されているか |

### 成果物

- `storage/specs/REQ-*.md` — EARS形式の要件ドキュメント

---

## Phase 2: 設計

### 目的

C4モデルでシステム構造を設計する。

### 進め方

1. AIエージェントに「設計を作成して」と依頼
2. 要件ファイル（REQ-*）から C4モデル設計が生成される
3. SOLID原則・トレーサビリティの自動検証が実行される
4. 指摘を修正し、100%通過を目指す
5. 「承認」で Phase 3 へ（Phase 4 への直接遷移は禁止）

### C4モデルの4レベル

| レベル | 内容 | 対象読者 |
|-------|------|---------|
| **Context** | システム境界と外部アクター | 全員 |
| **Container** | 技術選択とコンテナ構成（Web、DB、API等） | 開発チーム |
| **Component** | コンテナ内部の主要コンポーネント | 開発者 |
| **Code** | クラス・関数レベルの実装詳細 | 実装者 |

### レビュー観点

| 観点 | チェック内容 |
|------|------------|
| トレーサビリティ | すべてのREQ-*がDES-*にマッピングされているか |
| SOLID原則 | 単一責任・開放閉鎖・リスコフ置換・IF分離・依存性逆転 |
| 設計パターン | 適切なパターン（Repository, Service, Factory等）が適用されているか |
| 憲法準拠 | Article V（トレーサビリティ）, VII（設計パターン）, IX（品質ゲート） |

### 成果物

- `storage/design/DES-*.md` — C4モデル設計ドキュメント

---

## Phase 3: タスク分解

### 目的

設計を実装可能な単位のタスクに分解する。

### 進め方

1. AIエージェントに「タスク分解して」と依頼
2. 設計ファイル（DES-*）から実装タスクが生成される
3. トレーサビリティ検証（REQ↔DES↔TSK）が実行される
4. 「承認」で Phase 4 へ

### タスクの粒度

- 各タスクは **1〜4時間** で完了できる粒度
- 優先度（P0/P1/P2）と依存関係が設定される
- 要件との対応（REQ-* → DES-* → TSK-*）が明確

### タスク分類

| 分類 | 内容 | 例 |
|-----|------|-----|
| **基盤設定** | プロジェクト初期設定 | package.json, tsconfig.json, テスト設定 |
| **ドメインモデル** | 型定義・Value Object | エンティティ、ステータス遷移 |
| **コア機能（P0）** | 必須機能の実装 | CRUD操作、バリデーション |
| **追加機能（P1）** | 重要だが必須でない機能 | 検索、フィルタリング |
| **インフラ・テスト** | 永続化・CLI・テスト | Repository、CLI、ユニットテスト |

### レビュー観点

| 観点 | チェック内容 |
|------|------------|
| 設計対応 | すべてのDES-*がTSK-*にマッピングされているか |
| タスクサイズ | 1〜4時間で完了可能か |
| 依存関係 | TSK間の依存が明確で、実行順序が妥当か |

### 成果物

- TSK-* リスト（AIエージェントのTodoリストとして管理）

---

## Phase 4: 実装

### 目的

テスト先行（Red-Green-Blue）でコードを書く。

### 進め方

タスクごとに以下のサイクルを繰り返します：

```
1. Red:   テストを書く（まだ失敗する状態）
2. Green: テストが通る最小限の実装を書く
3. Blue:  リファクタリング（コード品質の向上）
4. 検証:  ユニットテスト実行・合格確認
```

### 前提条件

Phase 4を開始するには、以下が必須です：
- Phase 3（タスク分解）が完了し、ユーザーが承認済み
- TSK-* が定義されている

未完了の場合は Phase 3 に戻ります。

### 実装中に使えるスキル

| スキル | 用途 | 使い方 |
|-------|------|-------|
| `/checkpoint` | 作業状態の保存・復元 | 「チェックポイントを作成して」 |
| `/build-fix` | ビルドエラーの自動修正 | 「ビルドエラーを修正して」 |
| `/verification-loop` | 多段階検証 | 「検証して」 |

### レビュー観点

| 観点 | チェック内容 |
|------|------------|
| テストカバレッジ | 各タスクにテストが存在するか |
| トレーサビリティ | コードが要件（REQ-*）に紐づいているか |
| セキュリティ | 脆弱性がないか（`codegen security`） |

---

## Phase 5: 完了

### 目的

ドキュメント更新とコミット。

### 進め方

1. CHANGELOG.md を更新
2. 必要に応じてその他ドキュメントを更新
3. Git コミット

---

## 9つの憲法条項

すべてのフェーズを通じて適用される不変のルールです。

| 条項 | 名称 | 概要 | 関連フェーズ |
|-----|------|------|------------|
| I | Library-First | 機能は独立ライブラリとして開始 | Phase 4 |
| II | CLI Interface | すべてのライブラリはCLI公開必須 | Phase 4 |
| III | Test-First | Red-Green-Blueサイクルでテスト先行 | Phase 4 |
| IV | EARS Format | 要件はEARS形式で記述 | Phase 1 |
| V | Traceability | 要件↔設計↔コード↔テストの100%追跡 | 全フェーズ |
| VI | Project Memory | steering/を参照してから決定 | 全フェーズ |
| VII | Design Patterns | 設計パターン適用の文書化 | Phase 2 |
| VIII | Decision Records | すべての決定をADRで記録 | 全フェーズ |
| IX | Quality Gates | フェーズ移行前の品質検証 | Phase 1→2→3→4 |

---

## ディレクトリ構造

MUSUBIXプロジェクトの成果物は以下に保存されます：

```
your-project/
├── steering/                  # プロジェクトメモリ（AIが参照するルール）
│   ├── rules/
│   │   └── constitution.md    # 9つの憲法条項
│   ├── product.md             # プロダクトコンテキスト
│   ├── tech.md                # 技術スタック
│   └── structure.md           # プロジェクト構造
├── storage/                   # 成果物ストレージ
│   ├── specs/                 # 要件(REQ-*)、設計(DES-*)、タスク(TSK-*)
│   ├── design/                # 設計ドキュメント、C4ダイアグラム
│   ├── traceability/          # トレーサビリティマトリクス
│   └── reviews/               # レビュー結果
└── musubix.config.json        # プロジェクト設定
```

---

## 関連ドキュメント

| ドキュメント | 内容 |
|-------------|------|
| [クイックスタート](quickstart.md) | 5分で始めるMUSUBIX |
| [プロンプトガイド](prompt-guide.md) | プロンプト例と内部処理の対応表 |
| [チュートリアル](tutorial/01-setup.md) | 備品管理システムを作るハンズオン |
| [FAQ](faq.md) | よくある質問 |
