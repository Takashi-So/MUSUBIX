# チュートリアル Part 2: 要件定義

> 所要時間: 約15分
> 前提: [Part 1: セットアップ](01-setup.md) が完了していること

---

## 1. 要件定義の開始

AIエージェントに以下のように話しかけます：

```
備品管理システムを開発するので、要件定義を開始して
```

### 内部で起きること

AIエージェントが `sdd_create_requirements` ツールを呼び出します。コンテキストが不足している場合、以下のような明確化質問が返されます：

- **WHY**: なぜ備品管理システムが必要ですか？
- **WHO**: 対象ユーザーは誰ですか？
- **WHAT-IF**: 成功した場合の理想状態は？
- **CONSTRAINT**: 制約条件はありますか？
- **SUCCESS**: 成功基準は何ですか？

### 回答例

```
WHY: 社内の備品の所在管理ができていないため
WHO: 総務部のスタッフ（10名程度）
WHAT-IF: 全備品の所在と貸出状況がリアルタイムで把握できる
CONSTRAINT: ローカル実行（外部DB不要）、TypeScriptで実装
SUCCESS: 備品の登録・検索・貸出・返却・廃棄が管理できること
```

## 2. EARS形式の要件が生成される

回答に基づいて、AIエージェントがEARS形式の要件ドキュメントを生成します。

### 生成される要件の例

```markdown
# REQ-EQUIP-001: 備品管理システム要件

## 機能要件

### REQ-EQUIP-001-01: 備品登録
EARS形式: Ubiquitous
THE system SHALL allow users to register equipment with name (1-100 chars),
category, purchase date, price (0-10,000,000 JPY), and storage location
within 200ms response time.

### REQ-EQUIP-001-02: 備品ID自動生成
EARS形式: Event-driven
WHEN a new equipment is registered,
THE system SHALL generate a unique ID in EQ-YYYYMMDD-NNN format.

### REQ-EQUIP-001-03: 備品検索
EARS形式: Ubiquitous
THE system SHALL allow users to search equipment by name, category,
or status and return results within 500ms.

### REQ-EQUIP-001-04: 貸出記録
EARS形式: Event-driven
WHEN a user borrows equipment,
THE system SHALL record the borrower name, borrow date,
and expected return date.

### REQ-EQUIP-001-05: 返却記録
EARS形式: Event-driven
WHEN a user returns equipment,
THE system SHALL update the status to "available"
and record the actual return date.

### REQ-EQUIP-001-06: 貸出中の重複防止
EARS形式: State-driven
WHILE equipment is in "borrowed" status,
THE system SHALL reject new borrow requests within 50ms
and return an error message "Equipment is currently borrowed".

### REQ-EQUIP-001-07: 廃棄記録
EARS形式: Event-driven
WHEN equipment is disposed,
THE system SHALL record the disposal date and reason,
and update the status to "disposed".

### REQ-EQUIP-001-08: 廃棄済み備品の貸出防止
EARS形式: Unwanted
THE system SHALL NOT allow any borrow operations on equipment
with "disposed" status and SHALL return an error message
"Equipment has been disposed" within 50ms.
```

**保存先**: `storage/specs/REQ-EQUIP-001.md`

## 3. レビュー（1回目）

要件が生成されると、自動でレビューが実行されます。

### 内部で起きること

`musubix requirements validate storage/specs/REQ-EQUIP-001.md` が実行されます。

### レビュー結果の例

```
レビュー結果:
✅ EARS形式: 全8要件が準拠
✅ 優先度: 設定済み
⚠️ 測定可能な基準が不足（6件）: "Consider adding measurable criteria"

errors: 0, warnings: 0, info: 6
```

## 4. 修正と再レビュー

指摘事項があった場合、AIエージェントに修正を依頼します：

```
全ての要件に応答時間などの測定可能な基準を追加して
```

### レビュー結果（2回目）

```
レビュー結果:
✅ EARS形式: 全8要件が準拠
✅ 優先度: 設定済み
⚠️ State-driven/Unwanted要件の応答時間が不足（2件）

errors: 0, warnings: 0, info: 2
```

さらに修正を依頼します：

```
State-driven要件とUnwanted要件にも応答時間を追加して
```

### レビュー結果（3回目・最終）

```
レビュー結果:
✅ EARS形式: 全8要件が準拠
✅ 優先度: 設定済み
✅ 測定可能な基準: 全要件に設定済み

errors: 0, warnings: 0, info: 0
✅ All 10 requirements are valid
```

## 5. 承認

指摘がゼロになったら承認します：

```
承認
```

これで Phase 1（要件定義）が完了し、Phase 2（設計）に進みます。

## このパートのまとめ

| 項目 | 結果 |
|------|------|
| レビュー回数 | 3回（指摘→修正→再レビューの繰り返し） |
| 最終的な要件数 | 8〜10件（機能要件 + 非機能要件） |
| EARS形式準拠 | 100% |
| 成果物 | `storage/specs/REQ-EQUIP-001.md` |

### 学んだこと

- 自然言語でAIに依頼するだけで、EARS形式の要件が生成される
- 自動レビューで指摘が出るので、指摘がゼロになるまで修正を繰り返す
- 「承認」で次のフェーズに進む

---

**前へ**: [Part 1: セットアップ](01-setup.md) | **次へ**: [Part 3: 設計](03-design.md)
