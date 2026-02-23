# チュートリアル Part 5: 検証・学習・完了

> 所要時間: 約15分
> 前提: [Part 4: 実装](04-implementation.md) が完了していること

---

## 1. トレーサビリティ検証

実装が完了したら、要件→設計→コードの追跡可能性を検証します。

AIエージェントに以下のように話しかけます：

```
トレーサビリティを検証して
```

### 内部で起きること

1. `musubix trace matrix` でトレーサビリティマトリクスを生成
2. `musubix trace validate` でリンクの整合性を検証

### マトリクス結果の例

```
トレーサビリティマトリクス:

REQ-EQUIP-001-01 (備品登録)
  → DES-EQUIP-001-ENTITY (Equipmentエンティティ)
  → TSK-004 (備品登録機能)
  → src/domain/equipment.ts
  → src/domain/equipment.test.ts

REQ-EQUIP-001-02 (備品ID自動生成)
  → DES-EQUIP-001-SERVICE (EquipmentService)
  → TSK-003 (備品ID生成ロジック)
  → src/domain/equipment-id.ts
  → src/domain/equipment-id.test.ts

... (全要件のマッピング)

カバレッジ: 8/8 要件 (100%)
```

### 検証結果の例

```
検証結果:
✅ 全要件がマッピング済み
✅ 壊れたリンクなし
✅ 孤児の要件なし

summary: { total: 8, valid: 8, broken: 0, orphans: 0 }
```

> **orphan（孤児）が出た場合**: 要件に対応する実装がまだないことを意味します。未実装のタスクがあれば完了させてください。

---

## 2. セキュリティチェック

セキュリティスキャンを実行します：

```
セキュリティスキャンして
```

### 内部で起きること

`musubix codegen security src/` が実行されます。

### 結果の例

```
セキュリティスキャン結果:
✅ 脆弱性: 0件
✅ シークレット検出: 0件
✅ テイント解析: 問題なし
```

---

## 3. 憲法準拠チェック

9つの憲法条項への準拠を検証します：

```
憲法準拠を検証して
```

### 内部で起きること

`sdd_validate_constitution` ツールが実行されます。

### 結果の例

```
憲法準拠チェック結果:
✅ Article I   - Library-First: 機能がライブラリとして実装されている
✅ Article II  - CLI Interface: CLIが提供されている
✅ Article III - Test-First: テストが実装に先行している
✅ Article IV  - EARS Format: 要件がEARS形式で記述されている
✅ Article V   - Traceability: 100%の追跡可能性
✅ Article VI  - Project Memory: steering/が参照されている
✅ Article VII - Design Patterns: Repository, Serviceパターンが適用・文書化済み
✅ Article VIII- Decision Records: 技術決定がADRで記録済み
✅ Article IX  - Quality Gates: 全フェーズの品質ゲートが通過済み
```

---

## 4. ADR（Architecture Decision Records）の記録

開発中に行った技術的な判断をADRとして記録します：

```
この開発で行った技術選定をADRとして記録して
```

### 内部で起きること

`musubix design adr` が実行されます。

### 記録される判断の例

```
ADR-001: JSONファイルによるローカル永続化を採用
- 状態: Accepted
- コンテキスト: 小規模な社内ツールで外部DB不要
- 決定: JSONファイルによるローカルストレージ
- 理由: セットアップ不要、ポータブル、十分なパフォーマンス

ADR-002: Function-based Value Objectパターンの採用
- 状態: Accepted
- コンテキスト: TypeScriptの構造的型付けとの相性
- 決定: クラスではなくinterface + factory関数
- 理由: BP-CODE-004に準拠、テスタビリティが高い
```

---

## 5. 学習システムの活用

MUSUBIXには自己学習システムが搭載されています。今回の開発から学んだパターンを確認し、将来のプロジェクトに活かせます。

### 5-1. 学習状態の確認

```
学習状態を確認して
```

### 内部で起きること

`musubix learn status` が実行されます。

### 結果の例

```
学習システム ダッシュボード:

パターン数: 17
フィードバック数: 12
信頼度平均: 0.89

カテゴリ別:
  code: 5パターン (BP-CODE-001〜005)
  design: 7パターン (BP-DESIGN-001〜007)
  test: 5パターン (BP-TEST-001〜005)

最近適用されたパターン:
  - BP-CODE-002 (Date-based ID Format) → equipment-id.ts
  - BP-DESIGN-001 (Status Transition Map) → equipment-status.ts
  - BP-CODE-005 (Result Type) → equipment-service.ts
```

### 5-2. ベストプラクティスの確認

```
ベストプラクティスを表示して
```

### 内部で起きること

`musubix learn best-practices` が実行されます。

今回の開発で使用されたベストプラクティスが表示されます：

```
学習済みベストプラクティス:

コードパターン:
  BP-CODE-001 (95%): Entity Input DTO - 登録時にInput DTOを使用
  BP-CODE-002 (90%): Date-based ID Format - EQ-YYYYMMDD-NNN
  BP-CODE-004 (95%): Function-based Value Objects - interface + factory関数
  BP-CODE-005 (95%): Result Type - Result<T, E>で失敗を表現

設計パターン:
  BP-DESIGN-001 (95%): Status Transition Map - ステータス遷移をMapで定義
  BP-DESIGN-003 (90%): Service Layer with DI - リポジトリをDI
  BP-DESIGN-006 (95%): Entity Counter Reset - テスト用のresetCounter()

テストパターン:
  BP-TEST-001 (95%): Test Counter Reset - beforeEachでIDカウンターをリセット
  BP-TEST-004 (95%): Result Type Test - isOk()/isErr()で両パスをテスト
  BP-TEST-005 (90%): Status Transition Testing - 有効・無効遷移を網羅テスト
```

### 5-3. フィードバックの記録

今回の開発で特にうまくいったパターンにフィードバックを記録し、学習精度を高めます：

```
BP-DESIGN-001のStatus Transition Mapパターンが非常に有効だった。フィードバックを記録して
```

### 内部で起きること

`musubix learn feedback` が実行され、パターンの信頼度が更新されます。

```
フィードバック記録:
  パターン: BP-DESIGN-001 (Status Transition Map)
  評価: accept
  信頼度: 0.95 → 0.97
```

### 5-4. パターン学習サイクルの実行（オプション）

開発完了後、Wake-Sleep学習サイクルを実行すると、今回の開発から新しいパターンを抽出・統合できます：

```
学習サイクルを実行して
```

### 内部で起きること

`musubix learn cycle` が実行されます。

```
Wake-Sleep学習サイクル:

Wake Phase (パターン抽出):
  ✅ equipment-id.ts → Date-based ID Pattern (既知)
  ✅ equipment-status.ts → Status Transition Pattern (既知)
  🆕 equipment-repository.ts → JSON File Repository Pattern (新規候補)

Sleep Phase (パターン統合):
  ✅ 既存パターン17件の信頼度を更新
  🆕 新規パターン候補1件を評価中 (閾値: 0.7)
  ✅ メモリ最適化完了

結果: パターン数 17 → 17 (新規候補は信頼度不足で保留)
```

> 新しいパターンは複数のプロジェクトで繰り返し観測されると、信頼度が閾値を超えて正式にパターンとして登録されます。

---

## 6. 知識グラフへの記録

今回の開発で得た知識を知識グラフに記録できます：

```
このプロジェクトの知識をグラフに記録して
```

### 内部で起きること

`musubix knowledge add` が実行されます。

```
知識グラフ更新:
  ✅ requirement:REQ-EQUIP-001 を追加
  ✅ design:DES-EQUIP-001 を追加
  ✅ リレーション: REQ-EQUIP-001 → tracesTo → DES-EQUIP-001
  ✅ パターン: status-transition, repository を記録
```

記録した知識は将来のプロジェクトで検索・再利用できます：

```
# 将来のプロジェクトで
「ステータス遷移に関する知識を検索して」
→ 備品管理システムで使用した Status Transition Map パターンが提案される
```

---

## 7. CHANGELOG更新とコミット（Phase 5）

最後にCHANGELOGを更新してコミットします。

```
CHANGELOGを更新して
```

### CHANGELOG更新例

```markdown
## [1.0.0] - 2026-02-23

### Added
- 備品登録機能（REQ-EQUIP-001-01）
- 備品ID自動生成 EQ-YYYYMMDD-NNN形式（REQ-EQUIP-001-02）
- 備品検索機能（REQ-EQUIP-001-03）
- 貸出・返却記録機能（REQ-EQUIP-001-04, 05）
- 貸出中の重複防止（REQ-EQUIP-001-06）
- 廃棄記録・廃棄済み貸出防止（REQ-EQUIP-001-07, 08）
- JSON永続化層
- CLIインターフェース
- 全要件のトレーサビリティ確認済み（100%カバレッジ）
```

コミット：

```
コミットして
```

---

## 8. チュートリアル全体のまとめ

### 各フェーズの振り返り

| フェーズ | やったこと | レビュー回数 | 成果物 |
|---------|-----------|-------------|-------|
| Phase 1: 要件定義 | EARS形式で8要件を定義 | 3回 | `storage/specs/REQ-EQUIP-001.md` |
| Phase 2: 設計 | C4モデルで設計 | 1回 | `storage/design/DES-EQUIP-001.md` |
| Phase 3: タスク分解 | 14タスクに分解 | 1回 | TSKリスト |
| Phase 4: 実装 | Red-Green-Blueで開発 | — | `src/` 以下のコード + テスト |
| Phase 5: 検証・学習・完了 | 検証6種 + 学習 + コミット | — | CHANGELOG.md, ADR, 知識グラフ |

### Phase 5 で実施した検証・学習

| 工程 | プロンプト | 内部コマンド |
|------|-----------|-------------|
| トレーサビリティ検証 | 「トレーサビリティを検証して」 | `trace matrix` + `trace validate` |
| セキュリティチェック | 「セキュリティスキャンして」 | `codegen security` |
| 憲法準拠チェック | 「憲法準拠を検証して」 | `sdd_validate_constitution` |
| ADR記録 | 「技術選定をADRとして記録して」 | `design adr` |
| 学習状態確認 | 「学習状態を確認して」 | `learn status` |
| ベストプラクティス確認 | 「ベストプラクティスを表示して」 | `learn best-practices` |
| フィードバック記録 | 「フィードバックを記録して」 | `learn feedback` |
| 学習サイクル | 「学習サイクルを実行して」 | `learn cycle` |
| 知識グラフ記録 | 「知識をグラフに記録して」 | `knowledge add` |
| CHANGELOG更新 | 「CHANGELOGを更新して」 | ファイル編集 |

### SDDのメリット（このチュートリアルで体験したこと）

1. **自然言語で始められる**: 「備品管理システムを作りたい」と話しかけるだけ
2. **品質が自動で保証される**: EARS検証、SOLID原則、トレーサビリティが自動チェック
3. **レビューサイクルで品質向上**: 指摘→修正を繰り返して品質を高める
4. **完全な追跡可能性**: 要件→設計→コード→テストがすべて紐付けられる
5. **ベストプラクティスの自動適用**: 学習済みパターンが適用される
6. **知識が蓄積される**: 開発経験がパターンとして学習され、次のプロジェクトに活かせる
7. **決定が記録される**: ADRにより「なぜこの実装になったか」が追跡可能

---

## 次のステップ

このチュートリアルで基本的な開発フローを学びました。さらに深く学ぶには：

| ドキュメント | 内容 |
|-------------|------|
| [プロンプトガイド](../prompt-guide.md) | より多くのプロンプト例と内部処理の対応表 |
| [SDDワークフロー](../workflow.md) | 各フェーズの詳細なルールとレビュー観点 |
| [FAQ](../faq.md) | よくある質問と回答 |
| [トラブルシューティング](../troubleshooting.md) | エラー時の対処法 |

---

**前へ**: [Part 4: 実装](04-implementation.md) | [チュートリアルトップ](README.md)
