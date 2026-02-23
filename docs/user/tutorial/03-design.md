# チュートリアル Part 3: 設計

> 所要時間: 約15分
> 前提: [Part 2: 要件定義](02-requirements.md) が完了し、承認済みであること

---

## 1. 設計の生成

AIエージェントに以下のように話しかけます：

```
設計書を作成して
```

### 内部で起きること

1. AIエージェントが `sdd_create_design` ツールを呼び出し
2. 要件ファイル（`storage/specs/REQ-EQUIP-001.md`）を読み込み
3. C4モデル（Context → Container → Component）の設計を生成
4. 自動で設計レビューを実行

## 2. 生成される設計の例

### Context レベル

```
備品管理システムの外部アクター:
- 総務部スタッフ（ユーザー）
- CLI インターフェース
```

### Component レベル

```
主要コンポーネント:
- EquipmentEntity: 備品エンティティ（ドメインモデル）
- BorrowRecordEntity: 貸出記録エンティティ
- EquipmentService: 備品管理ビジネスロジック
- EquipmentRepository: 備品の永続化
- EquipmentIdGenerator: EQ-YYYYMMDD-NNN形式のID生成
```

### 設計パターン

```
適用パターン:
- Repository Pattern: 永続化の抽象化
- Service Layer with DI: ビジネスロジックの分離
- Value Object: Price, EquipmentIdなどのドメイン概念
- Status Transition Map: ステータス遷移の制御
```

**保存先**: `storage/design/DES-EQUIP-001.md`

## 3. 自動レビュー結果

設計生成後、自動でレビューが実行されます。

### 内部で起きること

`musubix design validate storage/design/DES-EQUIP-001.md` が実行されます。

### レビュー結果の例

```
設計レビュー結果: 100% (8/8 checks)

憲法準拠:
  ✅ Article V  - トレーサビリティ: 全要件が設計要素にマッピング済み
  ✅ Article VII - 設計パターン: 2パターン適用（Repository, Service）
  ✅ Article IX  - 品質ゲート: 全チェック通過

SOLID原則:
  ✅ [S] 単一責任: 各コンポーネントが単一の責務を持つ
  ✅ [O] 開放閉鎖: 拡張に開き、修正に閉じている
  ✅ [L] リスコフ置換: 置換可能性を維持
  ✅ [I] インターフェース分離: 適切に分離されている
  ✅ [D] 依存性逆転: 抽象に依存している

トレーサビリティ:
  ✅ REQ-EQUIP-001-01 → DES-EQUIP-001-ENTITY
  ✅ REQ-EQUIP-001-02 → DES-EQUIP-001-SERVICE
  ✅ REQ-EQUIP-001-03 → DES-EQUIP-001-REPOSITORY
  ... (全要件がマッピング済み)

指摘事項: なし
```

> **指摘があった場合**: 「設計を修正して」とAIエージェントに依頼し、指摘がゼロになるまで繰り返してください。

## 4. 承認

レビュー結果に問題がなければ承認します：

```
承認
```

> **注意**: ここで「実装して」と言っても、Phase 3（タスク分解）を先に行う必要があります。設計から直接実装に進むことはできません。

## このパートのまとめ

| 項目 | 結果 |
|------|------|
| レビュー回数 | 1回（指摘なしの場合） |
| SOLID原則 | 5/5 準拠 |
| トレーサビリティ | REQ-* → DES-* 全マッピング完了 |
| 設計パターン | Repository, Service等を適用 |
| 成果物 | `storage/design/DES-EQUIP-001.md` |

### 学んだこと

- 設計はC4モデル（Context/Container/Component/Code）で構造化される
- SOLID原則と憲法条項の自動検証が行われる
- 要件（REQ-*）と設計（DES-*）のトレーサビリティが自動チェックされる
- 設計の承認後は、タスク分解（Phase 3）に進む（実装には直接進めない）

---

**前へ**: [Part 2: 要件定義](02-requirements.md) | **次へ**: [Part 4: 実装](04-implementation.md)
