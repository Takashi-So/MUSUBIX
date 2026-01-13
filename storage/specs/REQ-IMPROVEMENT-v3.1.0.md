# MUSUBIX v3.1.0 改善要件定義書
# 10仮想プロジェクト開発から得られた知見に基づく機能強化

**文書ID**: REQ-IMPROVEMENT-v3.1.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-13  
**ステータス**: Draft  
**準拠規格**: EARS（Easy Approach to Requirements Syntax）  
**データソース**: 10仮想プロジェクト開発（114フィードバック、26パターン学習）

---

## 1. 文書概要

### 1.1 目的

本文書は、以下の10仮想プロジェクト開発を通じて発見された問題点・改善点をEARS形式で要件化し、MUSUBIX v3.1.0の機能強化計画を定義する。

### 1.2 対象プロジェクト

| # | プロジェクト名 | ドメイン | テスト数 | 主要発見事項 |
|---|---------------|---------|---------|-------------|
| 1 | medical-records | 医療 | 40 | initコマンドのパス処理問題 |
| 2 | smart-home | IoT | 16 | イベント駆動EARS適合性 |
| 3 | event-ticketing | Eコマース | 54 | 同時購入競合状態パターン |
| 4 | recipe-sharing | SNS | 33 | Markdown内EARS検出不可 |
| 5 | fitness-coaching | ヘルスケア | 26 | ストリーク計算パターン |
| 6 | inventory-management | 物流 | 41 | 自動発注ルール設計 |
| 7 | document-collaboration | コラボレーション | 53 | CRDT設計パターン |
| 8 | music-streaming | メディア | 57 | プレイリスト管理パターン |
| 9 | job-matching | HR | - | マッチスコア計算設計 |
| 10 | travel-planner | 旅行 | 45 | 時間制約最適化 |
| 11 | pet-care | ペット | 45 | 予防接種スケジュール管理 |

**合計**: 410+テスト、114フィードバック、26パターン学習

### 1.3 優先度定義

| 優先度 | 説明 |
|--------|------|
| **P0** | 必須 - 複数プロジェクトで深刻な問題として報告 |
| **P1** | 重要 - 生産性に大きく影響する機能 |
| **P2** | 任意 - あれば便利な機能 |

---

## 2. CLI機能改善

### REQ-CLI-001: initコマンドのパス正規化

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）  
**報告元**: medical-records, smart-home, music-streaming, pet-care

**要件**:  
WHEN ユーザーが`musubix init`に絶対パスを指定した際,  
THE システム SHALL パスを正規化し二重連結を防止し、  
AND THE システム SHALL カレントディレクトリと指定パスを適切に解決する。

**現状の問題**:
```bash
# 現状: 二重パスが生成される
$ musubix init /home/user/project
→ /home/user/MUSUBIX/home/user/project  # NG

# 期待: 正しく解決される
→ /home/user/project  # OK
```

**検証方法**: ユニットテスト、E2Eテスト  
**受入基準**:
- [ ] 絶対パスが正しく解決される
- [ ] 相対パスが正しく解決される
- [ ] `--force`オプションでも正常動作
- [ ] エラー時に明確なメッセージを表示

---

### REQ-CLI-002: feedbackコマンドのオプション改善

**種別**: UBIQUITOUS  
**優先度**: P1（重要）  
**報告元**: medical-records, pet-care

**要件**:  
THE `musubix learn feedback`コマンド SHALL 必須オプション不足時に具体的なガイダンスを表示し、  
AND THE コマンド SHALL よく使うオプション（`--artifact-type`）のエイリアス（`-a`）を提供し、  
AND THE コマンド SHALL インタラクティブモードで必須項目を対話的に入力可能とする。

**検証方法**: CLIテスト  
**受入基準**:
- [ ] 必須オプション不足時にヘルプを自動表示
- [ ] `-a`エイリアスが動作する
- [ ] `--interactive`オプションで対話モード起動

---

### REQ-CLI-003: scaffold拡張コマンド

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）  
**報告元**: 全プロジェクト（共通）

**要件**:  
WHEN ユーザーが`musubix scaffold domain-model <name> -e "Entity1,Entity2"`を実行した際,  
THE システム SHALL 指定されたエンティティごとにTypeScriptファイルを自動生成し、  
AND THE 生成コード SHALL BP-CODE-001〜005パターンを適用し、  
AND THE システム SHALL テストファイルも同時に生成する。

**検証方法**: スキャフォールドテスト  
**受入基準**:
- [ ] エンティティファイルが生成される（factory関数付き）
- [ ] Result<T,E>型が適用される
- [ ] Branded ID型が生成される
- [ ] テストファイルが生成される（beforeEachにresetCounter）

---

## 3. 要件検証機能改善

### REQ-VAL-001: Markdown内EARS検出強化

**種別**: UBIQUITOUS  
**優先度**: P0（必須）  
**報告元**: medical-records, smart-home, recipe-sharing

**要件**:  
THE `musubix requirements validate`コマンド SHALL Markdownテーブル内のEARS構文を検出し、  
AND THE システム SHALL 通常テキスト・テーブル・コードブロック内のEARSを区別して解析し、  
AND THE システム SHALL 検出された要件の総数を正確に報告する。

**現状の問題**:
```markdown
| ID | 要件 |
|----|------|
| REQ-001 | WHEN user logs in, THE system SHALL... |
```
→ 現状: 要件数0と報告される

**検証方法**: パーサーテスト  
**受入基準**:
- [ ] テーブル形式のEARSが検出される
- [ ] 箇条書き形式のEARSが検出される
- [ ] 検出された要件のリストが出力可能

---

### REQ-VAL-002: 設計検証コマンド追加

**種別**: UBIQUITOUS  
**優先度**: P1（重要）  
**報告元**: smart-home, document-collaboration

**要件**:  
THE システム SHALL `musubix design validate`コマンドを提供し、  
AND THE コマンド SHALL 設計書と要件書のトレーサビリティを検証し、  
AND THE コマンド SHALL 未対応の要件（orphan requirements）を報告する。

**検証方法**: トレーサビリティテスト  
**受入基準**:
- [ ] DES-*からREQ-*への逆引きが可能
- [ ] 未対応要件がリストされる
- [ ] 過剰設計（要件なし設計）も検出される

---

## 4. 学習機能強化

### REQ-LEARN-001: パターン適用ガイダンス

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）  
**報告元**: event-ticketing, inventory-management

**要件**:  
WHEN ユーザーがエンティティ実装を開始した際,  
THE システム SHALL 関連する学習済みパターン（BP-CODE-*, BP-DESIGN-*）を推薦し、  
AND THE システム SHALL パターン適用例をコードスニペットで提示する。

**検証方法**: 推薦テスト  
**受入基準**:
- [ ] コンテキストに応じたパターンが推薦される
- [ ] 推薦理由が説明される
- [ ] コードスニペットが提供される

---

### REQ-LEARN-002: ドメイン固有パターン学習

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）  
**報告元**: event-ticketing, inventory-management, fitness-coaching

**要件**:  
WHEN 特定ドメイン（Eコマース、在庫管理、ヘルスケア等）のパターンが繰り返し使用された際,  
THE システム SHALL ドメイン固有パターンとして分類・学習し、  
AND THE システム SHALL 類似ドメインのプロジェクトで自動推薦する。

**学習対象パターン例**:
| ドメイン | パターン名 | 適用事例 |
|---------|-----------|---------|
| Eコマース | Optimistic Locking | チケット在庫管理 |
| Eコマース | Hold Pattern | カート一時確保 |
| 在庫管理 | Reorder Point | 自動発注トリガー |
| ヘルスケア | Streak Calculation | 連続日数計算 |

**検証方法**: パターンマッチングテスト  
**受入基準**:
- [ ] ドメインタグがパターンに付与される
- [ ] ドメインベースの推薦が機能する
- [ ] 類似ドメイン判定が適切

---

## 5. 設計パターンライブラリ拡充

### REQ-PAT-001: 同時実行パターン追加

**種別**: UBIQUITOUS  
**優先度**: P0（必須）  
**報告元**: event-ticketing

**要件**:  
THE システム SHALL 以下の同時実行パターンをライブラリに追加する:
- Optimistic Locking（楽観的ロック）
- Pessimistic Locking（悲観的ロック）
- Hold Pattern（一時確保）
- Idempotency Key（冪等性キー）

AND THE システム SHALL 各パターンのテンプレートコードを提供する。

**検証方法**: パターンライブラリテスト  
**受入基準**:
- [ ] 4つのパターンが登録されている
- [ ] テンプレートコードが生成可能
- [ ] パターン適用ガイダンスがある

---

### REQ-PAT-002: 時間制約パターン追加

**種別**: UBIQUITOUS  
**優先度**: P1（重要）  
**報告元**: travel-planner, smart-home, pet-care

**要件**:  
THE システム SHALL 以下の時間制約パターンをライブラリに追加する:
- Expiry Check（有効期限チェック）
- Scheduled Action（スケジュール実行）
- Interval Management（インターバル管理）
- Streak Calculation（連続日数計算）

**検証方法**: パターンライブラリテスト  
**受入基準**:
- [ ] 4つのパターンが登録されている
- [ ] 各パターンの使用例がドキュメント化

---

## 6. ドメインモデル生成機能

### REQ-GEN-001: Value Object自動生成

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）  
**報告元**: 全プロジェクト

**要件**:  
WHEN ユーザーが`musubix codegen vo <name> --type <type>`を実行した際,  
THE システム SHALL 指定された型のValue Objectを生成し、  
AND THE 生成コード SHALL BP-CODE-004（Function-based VO）パターンを適用する。

**対応タイプ**:
- `id`: Branded ID + factory関数
- `money`: 金額 + 通貨
- `temperature`: 温度 + 単位（℃/℉）
- `weight`: 重量 + 単位
- `duration`: 時間 + 分/秒
- `percentage`: 0-100制約
- `custom`: カスタムバリデーション

**検証方法**: コード生成テスト  
**受入基準**:
- [ ] 各タイプのVOが正しく生成される
- [ ] バリデーションロジックが含まれる
- [ ] Result<T,E>型で返却される

---

### REQ-GEN-002: Status Transition Map自動生成

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）  
**報告元**: event-ticketing, inventory-management, job-matching

**要件**:  
WHEN ユーザーが`musubix codegen status <entity> --states "s1,s2,s3"`を実行した際,  
THE システム SHALL BP-DESIGN-001（Status Transition Map）パターンを適用したコードを生成し、  
AND THE システム SHALL 遷移図をMermaidで出力する。

**検証方法**: コード生成テスト  
**受入基準**:
- [ ] validStatusTransitionsマップが生成される
- [ ] transitionStatus関数が生成される
- [ ] Mermaid状態遷移図が出力される

---

## 7. テスト生成機能強化

### REQ-TEST-001: Status Transitionテスト自動生成

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）  
**報告元**: event-ticketing, job-matching

**要件**:  
WHEN エンティティにStatus Transition Mapが定義されている際,  
THE システム SHALL 有効遷移・無効遷移の全組み合わせテストを自動生成し、  
AND THE システム SHALL BP-TEST-005パターンを適用する。

**検証方法**: テスト生成検証  
**受入基準**:
- [ ] 有効な遷移がすべてテストされる
- [ ] 無効な遷移がすべてテストされる
- [ ] エッジケース（終端状態）がテストされる

---

### REQ-TEST-002: カウンターリセット自動挿入

**種別**: UBIQUITOUS  
**優先度**: P0（必須）  
**報告元**: 全プロジェクト

**要件**:  
THE テスト生成 SHALL BP-TEST-001（Test Counter Reset）パターンを自動適用し、  
AND THE 生成テスト SHALL `beforeEach`に`resetAllCounters()`呼び出しを含める。

**検証方法**: テスト生成検証  
**受入基準**:
- [ ] beforeEachブロックが生成される
- [ ] resetAllCounters()が呼び出される
- [ ] テスト間の干渉がない

---

## 8. 非機能要件

### REQ-NFR-001: エラーメッセージ改善

**種別**: UBIQUITOUS  
**優先度**: P1（重要）  
**報告元**: medical-records, pet-care

**要件**:  
THE システム SHALL すべてのCLIエラーに対してアクショナブルなメッセージを表示し、  
AND THE メッセージ SHALL 解決方法または次のステップを提案する。

**検証方法**: エラーハンドリングテスト  
**受入基準**:
- [ ] エラー原因が明確に表示される
- [ ] 解決方法が提案される
- [ ] 関連するヘルプコマンドが案内される

---

### REQ-NFR-002: パフォーマンス改善

**種別**: UBIQUITOUS  
**優先度**: P2（任意）

**要件**:  
THE `musubix requirements validate`コマンド SHALL 100要件を5秒以内に検証し、  
AND THE `musubix learn status`コマンド SHALL 1秒以内に結果を表示する。

**検証方法**: パフォーマンステスト  
**受入基準**:
- [ ] 100要件検証が5秒以内
- [ ] 学習ステータス表示が1秒以内

---

## 9. 要件サマリー

### 優先度別要件数

| 優先度 | 要件数 | 説明 |
|--------|--------|------|
| **P0** | 4 | 必須 - 複数プロジェクトで深刻な問題 |
| **P1** | 10 | 重要 - 生産性に大きく影響 |
| **P2** | 1 | 任意 - あれば便利 |
| **合計** | **15** | |

### カテゴリ別要件数

| カテゴリ | 要件数 |
|---------|--------|
| CLI機能改善 | 3 |
| 要件検証機能改善 | 2 |
| 学習機能強化 | 2 |
| 設計パターンライブラリ | 2 |
| ドメインモデル生成 | 2 |
| テスト生成強化 | 2 |
| 非機能要件 | 2 |

---

## 10. 学習データサマリー

### 開発前後の比較

| 指標 | 開発前 | 開発後 | 増加率 |
|------|--------|--------|--------|
| フィードバック数 | 96 | 114 | +19% |
| パターン数 | 25 | 26 | +4% |
| 平均信頼度 | 65.8% | 69.0% | +3.2pp |

### 高頻度パターン（開発後）

| パターンID | カテゴリ | 出現回数 | 増加数 |
|-----------|---------|---------|--------|
| PAT-FC49A670 | code prefer | 1855 | +446 |
| PAT-E5AEFFBA | design prefer | 900 | +347 |
| PAT-86DEF551 | requirement prefer | 825 | +265 |
| PAT-298803B3 | code prefer | 537 | +129 |
| PAT-CB21FC93 | code avoid | 439 | +75 |

---

## 11. 変更履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|----------|--------|
| 1.0 | 2026-01-13 | 初版作成（10仮想プロジェクト開発結果に基づく） | AI Agent |

---

**文書終端**
