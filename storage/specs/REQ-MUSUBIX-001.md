# MUSUBIX - ニューロシンボリックAI統合システム 要件定義書

**文書ID**: REQ-MUSUBIX-001  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.4  
**作成日**: 2026-01-01  
**更新日**: 2026-01-02  
**ステータス**: Approved  
**準拠規格**: EARS（Easy Approach to Requirements Syntax）

---

## 1. 文書概要

### 1.1 目的

本文書は、MUSUBIとYATAを統合したニューロシンボリックAI Codingシステム「MUSUBIX」の機能要件・非機能要件を、EARS形式で定義する。

### 1.2 スコープ

本システムの対象範囲：
- ニューロシンボリック統合レイヤー
- 要求分析強化機能
- 設計生成強化機能
- コード生成・検証機能
- 説明生成機能
- トレーサビリティ管理
- アーキテクチャ・ライブラリ構成
- CLIインターフェース
- エラーリカバリ・データ永続性
- 国際化対応

### 1.3 EARS パターン凡例

| パターン | 説明 | 構文例 |
|----------|------|--------|
| **UBIQUITOUS** | システムが常に満たすべき要件 | THE システム SHALL... |
| **EVENT-DRIVEN** | 特定イベント発生時の要件 | WHEN <event>, THE システム SHALL... |
| **STATE-DRIVEN** | 特定状態における要件 | WHILE <state>, THE システム SHALL... |
| **UNWANTED** | 回避すべき動作の要件 | THE システム SHALL NOT... |
| **OPTIONAL** | 条件付き要件 | IF <condition>, THEN THE システム SHALL... |

### 1.4 優先度定義

| 優先度 | 説明 |
|--------|------|
| **P0** | 必須 - リリースに必要 |
| **P1** | 重要 - できる限り実装 |
| **P2** | 任意 - 時間があれば実装 |

---

## 2. アーキテクチャ要件

### REQ-ARC-001: ライブラリファースト構成

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
WHILE システムが開発される際,  
THE 各機能 SHALL 独立したライブラリとして実装され、  
AND THE ライブラリ SHALL 独自のテストスイートを持ち、  
AND THE ライブラリ SHALL アプリケーションコードに依存してはならない。

**検証方法**: コードレビュー、依存関係解析  
**受入基準**:
- [ ] 各機能が`/lib`または独立パッケージとして実装されている
- [ ] ライブラリごとに独立したテストスイートが存在する
- [ ] ライブラリからアプリケーションコードへの依存が0件
- [ ] 公開APIがエクスポートされている

**トレーサビリティ**: DES-ARC-001, TEST-ARC-001  
**憲法準拠**: Article I（Library-First Principle）

---

### REQ-ARC-002: CLIインターフェース

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
WHILE システムが稼働中,  
THE システム SHALL すべての主要機能をCLI経由で提供し、  
AND THE システム SHALL `--help`フラグでドキュメントを表示し、  
AND THE システム SHALL 一貫した引数パターン（フラグ、オプション）を使用し、  
AND THE システム SHALL 終了コード規約（0=成功、非0=エラー）に従う。

**検証方法**: E2Eテスト、CLIテスト  
**受入基準**:
- [ ] 全主要機能がCLIから実行可能
- [ ] `--help`で全コマンドのドキュメント表示
- [ ] 引数パターンが一貫している
- [ ] 終了コードが規約に準拠

**トレーサビリティ**: DES-ARC-002, TEST-ARC-002  
**憲法準拠**: Article II（CLI Interface Mandate）

---

## 3. 統合レイヤー要件

### REQ-INT-001: ニューロシンボリック統合

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
WHILE システムが稼働中,  
THE システム SHALL MUSUBIのLLMエージェントとYATAの知識グラフを統合し、  
AND THE システム SHALL ニューラル推論とシンボリック推論の結果を組み合わせ、  
AND THE システム SHALL 両者の信頼度を評価して最終結果を生成する。

**検証方法**: 統合テスト  
**受入基準**:
- [ ] MUSUBIエージェントとYATA MCPサーバーが正常に通信できる
- [ ] ニューラル・シンボリック双方の結果が取得できる
- [ ] 信頼度評価アルゴリズムが動作する

**トレーサビリティ**: DES-INT-001, TEST-INT-001

---

### REQ-INT-002: 信頼度評価

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
WHILE 推論結果を統合する際,  
THE システム SHALL ニューラル推論の信頼度を0.0-1.0で算出し、  
AND THE システム SHALL シンボリック推論の検証結果（valid/invalid）を取得し、  
AND THE システム SHALL 以下のルールで最終結果を決定する:

| シンボリック結果 | ニューラル信頼度 | 最終決定 |
|-----------------|-----------------|---------|
| invalid | - | ニューラル結果を棄却 |
| valid | ≥0.8 | ニューラル結果を採用 |
| valid | <0.8 | シンボリック結果を優先 |

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] 信頼度計算が正確に動作する
- [ ] 決定ルールが仕様通りに実装されている
- [ ] テストケースで95%以上の正答率

**トレーサビリティ**: DES-INT-002, TEST-INT-002

---

### REQ-INT-003: 矛盾検出

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN ニューラル推論とシンボリック推論の結果が矛盾する場合,  
THE システム SHALL 矛盾箇所を特定し、  
AND THE システム SHALL 矛盾の種類（論理的、制約違反、パターン不一致等）を分類し、  
AND THE システム SHALL 矛盾解消の提案をユーザーに提示する。

**検証方法**: 統合テスト  
**受入基準**:
- [ ] 既知の矛盾パターン10種類を100%検出
- [ ] 矛盾の種類が4カテゴリ（論理的、制約違反、パターン不一致、型不整合）に正確に分類される
- [ ] 解消提案が生成される（提案妥当性80%以上）

**トレーサビリティ**: DES-INT-003, TEST-INT-003

---

## 4. 要求分析要件

### REQ-RA-001: EARS形式検証

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN ユーザーが自然言語で要求を入力した場合,  
THE システム SHALL LLMを使用してEARS形式の要件に変換し、  
AND THE システム SHALL EARS構文の妥当性を検証し（5パターン準拠）、  
AND THE システム SHALL 構文エラーがある場合は修正案を提示する。

**検証方法**: ユニットテスト、E2Eテスト  
**受入基準**:
- [ ] EARS 5パターン（UBIQUITOUS, EVENT-DRIVEN, STATE-DRIVEN, UNWANTED, OPTIONAL）すべてに対応
- [ ] 構文検証精度95%以上
- [ ] 修正提案の妥当性をエキスパートが確認

**トレーサビリティ**: DES-RA-001, TEST-RA-001  
**憲法準拠**: Article IV（EARS Format）

---

### REQ-RA-002: オントロジー検証

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN EARS形式の要件が生成された場合,  
THE システム SHALL 要件をオントロジーにマッピングし、  
AND THE システム SHALL 論理的一貫性を検証し、  
AND THE システム SHALL 既存要件との矛盾を検出し、  
AND THE システム SHALL 検証結果をレポート形式で出力する。

**検証方法**: 統合テスト、オントロジー推論エンジンテスト  
**受入基準**:
- [ ] オントロジーマッピング成功率95%以上（失敗時はエラーレポート生成）
- [ ] 矛盾検出精度95%以上
- [ ] 検証レポートが生成される

**トレーサビリティ**: DES-RA-002, TEST-RA-002

---

### REQ-RA-003: 関連要件検索

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN 新しい要件が追加される場合,  
THE システム SHALL YATA知識グラフを使用して関連する既存要件を検索し、  
AND THE システム SHALL 関連度スコアを算出し（0.0-1.0）、  
AND THE システム SHALL 関連度が0.7以上の要件をリストアップする。

**検証方法**: 統合テスト  
**受入基準**:
- [ ] 関連要件が適切に検索される
- [ ] 関連度スコアが妥当（専門家評価）
- [ ] 検索時間が5秒以内

**トレーサビリティ**: DES-RA-003, TEST-RA-003

---

### REQ-RA-004: 要件分解

**種別**: OPTIONAL  
**優先度**: P2（任意）

**要件**:  
IF ユーザーが要件分解を要求した場合,  
THEN THE システム SHALL 複雑な要件をサブ要件に分解し、  
AND THE システム SHALL 各サブ要件にIDを付与し、  
AND THE システム SHALL 親子関係をグラフで記録する。

**検証方法**: E2Eテスト  
**受入基準**:
- [ ] 分解ロジックが適切に動作
- [ ] 親子関係が正しく記録される

**トレーサビリティ**: DES-RA-004, TEST-RA-004

---

## 5. 設計生成要件

### REQ-DES-001: パターン検出

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN 設計生成が要求された場合,  
THE システム SHALL YATA知識グラフを使用して適用可能なデザインパターンを検出し、  
AND THE システム SHALL 各パターンの適用可能性スコア（0.0-1.0）を算出し、  
AND THE システム SHALL スコアが0.8以上のパターンを推奨する。

**検証方法**: 統合テスト  
**受入基準**:
- [ ] 10種類以上のデザインパターンを検出可能
- [ ] パターン検出精度90%以上
- [ ] スコア計算が妥当

**トレーサビリティ**: DES-DES-001, TEST-DES-001

---

### REQ-DES-002: フレームワーク最適化

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN 特定のフレームワークが指定された場合,  
THE システム SHALL YATAの26フレームワーク知識を参照し、  
AND THE システム SHALL フレームワークのベストプラクティスを適用し、  
AND THE システム SHALL 推奨される設計パターンをコード例と共に提示する。

**検証方法**: E2Eテスト  
**受入基準**:
- [ ] 26フレームワークすべてに対応
- [ ] ベストプラクティス適用率90%以上
- [ ] コード例が実行可能

**トレーサビリティ**: DES-DES-002, TEST-DES-002

---

### REQ-DES-003: SOLID原則検証

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN 設計が生成された場合,  
THE システム SHALL SOLID原則への準拠を検証し、  
AND THE システム SHALL 違反箇所を特定し、  
AND THE システム SHALL 修正案を生成する。

**SOLID原則チェックリスト**:
| 原則 | 検証項目 |
|------|---------|
| S - 単一責任 | 各クラス/モジュールが1つの責任のみを持つ |
| O - 開放閉鎖 | 拡張に対して開、修正に対して閉 |
| L - リスコフ置換 | サブタイプが基底型と置換可能 |
| I - インターフェース分離 | 小さな特定インターフェースに分割 |
| D - 依存性逆転 | 抽象に依存、具象に依存しない |

**検証方法**: ユニットテスト、静的解析  
**受入基準**:
- [ ] SOLID 5原則すべてを検証
- [ ] 違反検出精度95%以上
- [ ] 修正案の妥当性

**トレーサビリティ**: DES-DES-003, TEST-DES-003

---

### REQ-DES-004: C4モデル生成

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN 設計が確定した場合,  
THE システム SHALL C4モデル（Context, Container, Component, Code）を自動生成し、  
AND THE システム SHALL PlantUML形式で出力し、  
AND THE システム SHALL 要件とのトレーサビリティリンクを埋め込む。

**検証方法**: 統合テスト  
**受入基準**:
- [ ] 4レベルすべてのダイアグラム生成
- [ ] PlantUML構文が正確
- [ ] トレーサビリティIDが正しい

**トレーサビリティ**: DES-DES-004, TEST-DES-004

---

### REQ-DES-005: ADR（アーキテクチャ決定記録）

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN 重要な設計決定が行われた場合,  
THE システム SHALL ADRを自動生成し、  
AND THE システム SHALL 決定の背景、選択肢、理由を記録し、  
AND THE システム SHALL Markdown形式で保存する。

**検証方法**: E2Eテスト  
**受入基準**:
- [ ] ADRフォーマット準拠
- [ ] 決定理由が明確に記載
- [ ] ファイルが正しく保存される

**トレーサビリティ**: DES-DES-005, TEST-DES-005

---

## 6. コード生成・検証要件

### REQ-COD-001: コード生成

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN 設計からコード生成が要求された場合,  
THE システム SHALL LLMを使用してコードを生成し、  
AND THE システム SHALL 生成されたコードをYATAで解析し、  
AND THE システム SHALL 設計との整合性を検証する。

**検証方法**: E2Eテスト  
**受入基準**:
- [ ] コード生成成功率95%以上（1000件のテストケースで測定）
- [ ] 構文エラー率5%以下（生成コードの静的解析で測定）
- [ ] 設計整合性95%以上（設計要素とコード要素のマッピング率）

**トレーサビリティ**: DES-COD-001, TEST-COD-001

---

### REQ-COD-002: 静的解析

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN コードが生成された場合,  
THE システム SHALL Tree-sitterを使用してASTを解析し、  
AND THE システム SHALL コード品質メトリクスを算出し（複雑度、重複等）、  
AND THE システム SHALL 品質基準を満たさない場合は警告を発する。

**検証方法**: ユニットテスト  
**受入基準**:
- [ ] AST解析成功率100%
- [ ] メトリクス計算が正確
- [ ] 品質基準が適切

**トレーサビリティ**: DES-COD-002, TEST-COD-002

---

### REQ-COD-003: デザインパターン適合性

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN 設計でデザインパターンが指定された場合,  
THE システム SHALL 生成コードがパターンに準拠しているか検証し、  
AND THE システム SHALL 準拠していない場合は修正を試み、  
AND THE システム SHALL 3回の試行後も準拠しない場合はエラーを報告する。

**検証方法**: 統合テスト  
**受入基準**:
- [ ] パターン準拠検証精度90%以上
- [ ] 自動修正成功率80%以上
- [ ] エラーレポートが詳細

**トレーサビリティ**: DES-COD-003, TEST-COD-003

---

### REQ-COD-004: 依存関係検証

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN コードが生成された場合,  
THE システム SHALL YATA知識グラフで依存関係を解析し、  
AND THE システム SHALL 循環依存を検出し、  
AND THE システム SHALL 未解決の依存を特定する。

**検証方法**: 統合テスト  
**受入基準**:
- [ ] 循環依存検出率100%
- [ ] 未解決依存の特定精度95%以上

**トレーサビリティ**: DES-COD-004, TEST-COD-004

---

### REQ-COD-005: コーディング規約検証

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
WHILE コードが生成される際,  
THE システム SHALL プロジェクト固有のコーディング規約を適用し、  
AND THE システム SHALL 命名規則、インデント、コメント等を検証し、  
AND THE システム SHALL 違反箇所を自動修正する。

**検証方法**: ユニットテスト  
**受入基準**:
- [ ] 規約違反検出率95%以上
- [ ] 自動修正成功率90%以上

**トレーサビリティ**: DES-COD-005, TEST-COD-005

---

### REQ-COD-006: セキュリティ検証

**種別**: UNWANTED  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL 以下のセキュリティ脆弱性を含むコードを生成してはならない:
- SQLインジェクション
- クロスサイトスクリプティング（XSS）
- ハードコードされた認証情報
- 安全でない暗号化アルゴリズム
- パストラバーサル
- コマンドインジェクション
- 安全でないデシリアライゼーション
- XML外部エンティティ（XXE）
- サーバーサイドリクエストフォージェリ（SSRF）
- オープンリダイレクト

AND IF 脆弱性が検出された場合,  
THEN THE システム SHALL コード生成を中止し、  
AND THE システム SHALL 脆弱性詳細をレポートする。

**検証方法**: セキュリティテスト、SAST統合  
**受入基準**:
- [ ] 主要脆弱性の検出率98%以上
- [ ] 誤検出率10%以下
- [ ] レポートが詳細

**トレーサビリティ**: DES-COD-006, TEST-COD-006

---

## 7. テスト生成要件

### REQ-TST-001: ユニットテスト生成

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN コードが生成された場合,  
THE システム SHALL 各関数/メソッドに対してユニットテストを生成し、  
AND THE システム SHALL EARS要件とマッピングし、  
AND THE システム SHALL カバレッジ80%以上を目標とする。

**検証方法**: E2Eテスト、カバレッジ測定  
**受入基準**:
- [ ] テスト生成成功率90%以上
- [ ] カバレッジ目標達成率85%以上
- [ ] 要件マッピング100%

**トレーサビリティ**: DES-TST-001, TEST-TST-001  
**憲法準拠**: Article III（Test-First）

---

### REQ-TST-002: 統合テスト生成

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
WHILE 統合テストが実行される際,  
THE システム SHALL コンポーネント間の相互作用をテストするコードを生成し、  
AND THE システム SHALL 実データベース（Docker、テストスキーマ）を使用し、  
AND THE システム SHALL 外部APIはテスト/サンドボックス環境を使用し、  
AND THE システム SHALL モックは以下の場合のみ許可する:
- 外部サービスがテスト環境で利用不可
- 外部サービスに使用制限/コストがある
- 外部サービスにテスト環境がない

**検証方法**: E2Eテスト、Docker Compose環境  
**受入基準**:
- [ ] 統合テストが実データベースで実行可能
- [ ] 外部APIがサンドボックス環境で動作
- [ ] モック使用時は理由が文書化されている
- [ ] テストデータのクリーンアップが自動化

**トレーサビリティ**: DES-TST-002, TEST-TST-002  
**憲法準拠**: Article IX（Integration-First Testing）

---

## 8. 説明生成要件

### REQ-EXP-001: 推論チェーン記録

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
WHILE システムが要求から設計、コード生成を行う際,  
THE システム SHALL すべての推論ステップを記録し、  
AND THE システム SHALL ニューラル・シンボリック双方の判断根拠を保存し、  
AND THE システム SHALL 時系列順に構造化されたログを生成する。

**検証方法**: 統合テスト  
**受入基準**:
- [ ] 推論ステップ記録率100%
- [ ] ログ構造が適切
- [ ] 時系列が正確

**トレーサビリティ**: DES-EXP-001, TEST-EXP-001

---

### REQ-EXP-002: 自然言語説明生成

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN ユーザーが説明を要求した場合,  
THE システム SHALL 推論チェーンから自然言語の説明を生成し、  
AND THE システム SHALL 以下を含む:
- なぜその要件が必要か
- なぜその設計を選択したか
- どのパターンを適用したか
- どの制約を満たしているか

**検証方法**: E2Eテスト、ユーザー評価  
**受入基準**:
- [ ] 説明生成成功率95%以上
- [ ] 説明の分かりやすさ（ユーザー評価4.0/5.0以上）

**トレーサビリティ**: DES-EXP-002, TEST-EXP-002

---

### REQ-EXP-003: ビジュアル説明

**種別**: OPTIONAL  
**優先度**: P2（任意）

**要件**:  
IF ユーザーがビジュアル説明を要求した場合,  
THEN THE システム SHALL 推論グラフをGraphvizで可視化し、  
AND THE システム SHALL ノード（決定点）とエッジ（推論）を表示し、  
AND THE システム SHALL インタラクティブに探索可能にする。

**検証方法**: E2Eテスト  
**受入基準**:
- [ ] グラフが正しく生成される
- [ ] インタラクティブ機能が動作

**トレーサビリティ**: DES-EXP-003, TEST-EXP-003

---

## 9. トレーサビリティ要件

### REQ-TRA-001: 完全トレーサビリティ

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
WHILE システムが稼働中,  
THE システム SHALL 要求↔設計↔コード↔テストの完全な双方向トレーサビリティを維持し、  
AND THE システム SHALL トレーサビリティマトリクスを自動生成し、  
AND THE システム SHALL カバレッジ100%を保証する。

**検証方法**: トレーサビリティ監査  
**受入基準**:
- [ ] トレーサビリティマトリクス生成成功
- [ ] カバレッジ100%達成
- [ ] リンク切れ0件

**トレーサビリティ**: DES-TRA-001, TEST-TRA-001  
**憲法準拠**: Article V（Traceability）

---

### REQ-TRA-002: 影響分析

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN 要求が変更された場合,  
THE システム SHALL 影響を受ける設計・コード・テストを特定し、  
AND THE システム SHALL 影響範囲をレポートし、  
AND THE システム SHALL 変更推奨事項を提示する。

**検証方法**: 統合テスト  
**受入基準**:
- [ ] 影響範囲特定精度95%以上
- [ ] レポート生成成功率100%

**トレーサビリティ**: DES-TRA-002, TEST-TRA-002  
**憲法準拠**: Article V（Traceability）

---

## 10. エラーリカバリ・データ永続性要件

### REQ-ERR-001: グレースフルデグラデーション

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN YATAサーバーが応答しない場合,  
THE システム SHALL LLM単体モードにフォールバックし、  
AND THE システム SHALL ユーザーに機能制限を通知し、  
AND THE システム SHALL 30秒ごとにYATAサーバーへの再接続を試みる。

**検証方法**: 障害注入テスト  
**受入基準**:
- [ ] YATAサーバー障害時にシステムが継続動作
- [ ] フォールバック通知がユーザーに表示される
- [ ] 復旧後に自動的に通常モードに復帰

**トレーサビリティ**: DES-ERR-001, TEST-ERR-001

---

### REQ-ERR-002: データ永続性

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
WHILE システムが稼働中,  
THE システム SHALL すべての推論結果・設計決定を永続化し、  
AND THE システム SHALL システム障害後に最後の安定状態から復旧可能とし、  
AND THE システム SHALL 自動バックアップを1時間ごとに実行する。

**検証方法**: 障害復旧テスト  
**受入基準**:
- [ ] 障害発生前の状態から復旧可能
- [ ] データ損失が最大1時間以内
- [ ] 自動バックアップが正常動作

**トレーサビリティ**: DES-ERR-002, TEST-ERR-002

---

### REQ-ERR-003: バージョン互換性

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN システムがアップグレードされた場合,  
THE システム SHALL 既存のプロジェクトデータとの後方互換性を維持し、  
AND THE システム SHALL マイグレーションスクリプトを提供し、  
AND THE システム SHALL 互換性のない変更時は明示的な警告を表示する。

**検証方法**: アップグレードテスト  
**受入基準**:
- [ ] 旧バージョンのデータが読み込み可能
- [ ] マイグレーションが自動実行される
- [ ] 破壊的変更時に警告表示

**トレーサビリティ**: DES-ERR-003, TEST-ERR-003

---

## 11. パフォーマンス要件（非機能要件）

### REQ-PER-001: 応答時間

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
WHILE システムが稼働中,  
THE システム SHALL 以下の応答時間を満たす:

| 処理 | 目標応答時間 |
|------|-------------|
| 要求分析 | 10秒以内 |
| 設計生成 | 30秒以内 |
| コード生成 | 60秒以内 |
| 説明生成 | 5秒以内 |

**検証方法**: パフォーマンステスト  
**受入基準**:
- [ ] 95%のリクエストが目標時間内に完了

**トレーサビリティ**: DES-PER-001, TEST-PER-001

---

### REQ-PER-002: スケーラビリティ

**種別**: STATE-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHILE 同時ユーザー数が100人以下の場合,  
THE システム SHALL すべてのリクエストを処理し、  
AND THE システム SHALL 応答時間の劣化を20%以内に抑える。

**検証方法**: 負荷テスト  
**受入基準**:
- [ ] 100同時ユーザーで安定動作
- [ ] 応答時間劣化20%以内

**トレーサビリティ**: DES-PER-002, TEST-PER-002

---

## 12. 品質要件（非機能要件）

### REQ-QUA-001: コード品質

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
WHILE コードが生成される際,  
THE システム SHALL 以下の品質メトリクスを満たす:

| メトリクス | 目標値 |
|-----------|--------|
| サイクロマティック複雑度 | 10以下 |
| 関数の行数 | 50行以下 |
| クラスの行数 | 300行以下 |
| 重複コード | 5%以下 |

**検証方法**: 静的解析  
**受入基準**:
- [ ] 90%のコードがメトリクスを満たす

**トレーサビリティ**: DES-QUA-001, TEST-QUA-001

---

### REQ-QUA-002: テストカバレッジ

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
WHILE テストが実行される際,  
THE システム SHALL 以下のカバレッジを達成する:

| カバレッジ種別 | 目標値 |
|---------------|--------|
| ラインカバレッジ | 80%以上 |
| ブランチカバレッジ | 75%以上 |
| 関数カバレッジ | 90%以上 |

**検証方法**: カバレッジ測定  
**受入基準**:
- [ ] カバレッジ目標達成

**トレーサビリティ**: DES-QUA-002, TEST-QUA-002

---

## 13. セキュリティ要件（非機能要件）

### REQ-SEC-001: データ保護

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
WHILE システムが稼働中,  
THE システム SHALL すべてのコードとデータをローカルで処理し、  
AND THE システム SHALL 外部への送信を行わず（LLM API除く）、  
AND THE システム SHALL ユーザーデータを暗号化して保存する。

**検証方法**: セキュリティ監査  
**受入基準**:
- [ ] 外部通信0件（LLM API除く）
- [ ] データ暗号化100%

**トレーサビリティ**: DES-SEC-001, TEST-SEC-001

---

### REQ-SEC-002: 認証・認可

**種別**: STATE-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHILE マルチユーザー環境で動作する場合,  
THE システム SHALL ユーザー認証を要求し、  
AND THE システム SHALL ロールベースのアクセス制御を実装し、  
AND THE システム SHALL 監査ログを記録する。

**検証方法**: セキュリティテスト  
**受入基準**:
- [ ] 認証100%成功
- [ ] 権限エラー0件
- [ ] 監査ログ完全

**トレーサビリティ**: DES-SEC-002, TEST-SEC-002

---

## 14. 統合・互換性要件（非機能要件）

### REQ-INT-101: AIプラットフォーム対応

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
WHILE システムが稼働中,  
THE システム SHALL 以下の7つのAIプラットフォームをサポートする:

| プラットフォーム | 対応状況 |
|-----------------|---------|
| Claude Code | 必須 |
| GitHub Copilot | 必須 |
| Cursor | 必須 |
| Gemini CLI | 必須 |
| Codex CLI | 必須 |
| Qwen Code | 必須 |
| Windsurf | 必須 |

**検証方法**: 統合テスト（各プラットフォーム）  
**受入基準**:
- [ ] 7プラットフォームすべてで動作
- [ ] 機能差異を文書化

**トレーサビリティ**: DES-INT-101, TEST-INT-101

---

### REQ-INT-102: MCP準拠

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
WHILE システムが稼働中,  
THE システム SHALL Model Context Protocol（MCP）に準拠し、  
AND THE システム SHALL stdio/SSE両方のトランスポートをサポートし、  
AND THE システム SHALL Tools/Prompts/Resourcesを提供する。

**検証方法**: MCP準拠テスト  
**受入基準**:
- [ ] MCP仕様100%準拠
- [ ] 両トランスポート動作

**トレーサビリティ**: DES-INT-102, TEST-INT-102

---

## 15. 保守性要件（非機能要件）

### REQ-MNT-001: ログ記録

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
WHILE システムが稼働中,  
THE システム SHALL すべての重要な操作をログに記録し、  
AND THE システム SHALL ログレベル（DEBUG, INFO, WARN, ERROR）を適切に設定し、  
AND THE システム SHALL 構造化ログ（JSON）で出力する。

**検証方法**: ログ監査  
**受入基準**:
- [ ] 重要操作100%記録
- [ ] ログ形式が適切

**トレーサビリティ**: DES-MNT-001, TEST-MNT-001

---

### REQ-MNT-002: エラーハンドリング

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN エラーが発生した場合,  
THE システム SHALL エラーを適切にキャッチし、  
AND THE システム SHALL ユーザーフレンドリーなメッセージを表示し、  
AND THE システム SHALL 詳細なスタックトレースをログに記録し、  
AND THE システム SHALL 可能な場合は自動リカバリを試みる。

**検証方法**: エラーテスト  
**受入基準**:
- [ ] エラーキャッチ率100%
- [ ] リカバリ成功率80%以上

**トレーサビリティ**: DES-MNT-002, TEST-MNT-002

---

## 16. 国際化要件（非機能要件）

### REQ-I18N-001: 多言語対応

**種別**: OPTIONAL  
**優先度**: P2（任意）

**要件**:  
IF ユーザーが言語設定を変更した場合,  
THEN THE システム SHALL 日本語・英語でUIを表示し、  
AND THE システム SHALL エラーメッセージを選択言語で表示し、  
AND THE システム SHALL ドキュメントを選択言語で提供する。

**検証方法**: ローカライゼーションテスト  
**受入基準**:
- [ ] 日本語・英語の切り替えが可能
- [ ] 全UIテキストが翻訳されている
- [ ] エラーメッセージが翻訳されている

**トレーサビリティ**: DES-I18N-001, TEST-I18N-001

---

## 17. GitHub Agent Skills要件

### REQ-SKL-001: Agent Skillsディレクトリ構造

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL `.github/skills/` ディレクトリにAgent Skillsを格納し、  
AND THE システム SHALL 各スキルを独立したサブディレクトリとして構成し、  
AND THE システム SHALL サブディレクトリ名を小文字・ハイフン区切りとする。

**検証方法**: ディレクトリ構造検証  
**受入基準**:
- [ ] `.github/skills/` ディレクトリが存在する
- [ ] 各スキルが独立サブディレクトリを持つ
- [ ] ディレクトリ名が小文字・ハイフン区切り

**トレーサビリティ**: DES-SKL-001, TEST-SKL-001  
**憲法準拠**: Article VI（Project Memory）  
**外部仕様**: https://docs.github.com/ja/copilot/concepts/agents/about-agent-skills

---

### REQ-SKL-002: SKILL.mdファイル形式

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
THE 各スキルディレクトリ SHALL `SKILL.md` ファイルを含み、  
AND THE `SKILL.md` SHALL YAML frontmatter を含み、  
AND THE frontmatter SHALL `name` フィールド（必須・小文字・ハイフン区切り）を含み、  
AND THE frontmatter SHALL `description` フィールド（必須・使用タイミングを含む）を含み、  
AND THE frontmatter SHALL `license` フィールド（任意）を含むことができる。

**検証方法**: ファイル形式検証  
**受入基準**:
- [ ] 全スキルディレクトリに `SKILL.md` が存在
- [ ] YAML frontmatter が正しくパースできる
- [ ] `name` が小文字・ハイフン区切り
- [ ] `description` が存在し、使用タイミングを含む

**トレーサビリティ**: DES-SKL-002, TEST-SKL-002  
**憲法準拠**: Article VI（Project Memory）  
**外部仕様**: https://docs.github.com/ja/copilot/concepts/agents/about-agent-skills

---

### REQ-SKL-003: スキルコンテンツ

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
THE `SKILL.md` SHALL Markdown本文を含み、  
AND THE 本文 SHALL Copilotへの指示を記述し、  
AND THE 本文 SHALL 実行例やコードサンプルを含み、  
AND THE 本文 SHALL ガイドラインやチェックリストを含む。

**検証方法**: コンテンツ検証  
**受入基準**:
- [ ] 指示セクションが存在
- [ ] 実行例が1つ以上含まれる
- [ ] ガイドラインまたはチェックリストが含まれる

**トレーサビリティ**: DES-SKL-003, TEST-SKL-003  
**憲法準拠**: Article VI（Project Memory）

---

### REQ-SKL-004: MUSUBIXスキルセット

**種別**: UBIQUITOUS  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL 以下の3つのAgent Skillsを提供する:

| スキル名 | 用途 |
|---------|------|
| `musubix-sdd-workflow` | SDDワークフロー全体、9憲法条項ガイド |
| `musubix-ears-validation` | EARS形式要件の作成・検証 |
| `musubix-code-generation` | 設計からのコード生成 |

AND THE 各スキル SHALL 対応するCLIコマンドを記載し、  
AND THE 各スキル SHALL 憲法条項への準拠方法を記載する。

**検証方法**: スキル存在検証  
**受入基準**:
- [ ] 3つのスキルが全て存在
- [ ] 各スキルにCLIコマンドが記載
- [ ] 各スキルに憲法準拠情報が記載

**トレーサビリティ**: DES-SKL-004, TEST-SKL-004  
**憲法準拠**: Article VI（Project Memory）

---

## 17. CLIコマンド要件

### REQ-CLI-001: Requirements CLIコマンド

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN ユーザーが`musubix requirements`コマンドを実行した場合,  
THE システム SHALL 以下のサブコマンドを提供する:

| サブコマンド | 説明 | 例 |
|-------------|------|-----|
| `analyze <file>` | 自然言語からEARS形式に変換 | `musubix requirements analyze input.md` |
| `validate <file>` | EARS構文を検証 | `musubix requirements validate REQ-001.md` |
| `map <file>` | オントロジーにマッピング | `musubix requirements map REQ-001.md` |
| `search <query>` | 関連要件を検索 | `musubix requirements search "認証"` |

AND THE システム SHALL `--json`オプションでJSON出力をサポートし、  
AND THE システム SHALL `--verbose`オプションで詳細出力をサポートする。

**検証方法**: CLIテスト、E2Eテスト  
**受入基準**:
- [ ] 4つのサブコマンドが全て動作する
- [ ] --json出力が正しいJSON形式
- [ ] --verboseで追加情報が表示される
- [ ] ヘルプが適切に表示される

**トレーサビリティ**: DES-CLI-001, TEST-CLI-001  
**憲法準拠**: Article II（CLI Interface Mandate）, Article IV（EARS Format）

---

### REQ-CLI-002: Design CLIコマンド

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN ユーザーが`musubix design`コマンドを実行した場合,  
THE システム SHALL 以下のサブコマンドを提供する:

| サブコマンド | 説明 | 例 |
|-------------|------|-----|
| `generate <file>` | 要件から設計を生成 | `musubix design generate REQ-001.md` |
| `patterns <context>` | デザインパターンを検出 | `musubix design patterns "認証システム"` |
| `validate <file>` | SOLID原則を検証 | `musubix design validate DES-001.md` |
| `c4 <file>` | C4ダイアグラムを生成 | `musubix design c4 DES-001.md` |
| `adr <decision>` | ADRを生成 | `musubix design adr "JWT認証を採用"` |

AND THE システム SHALL `--output <dir>`オプションで出力先を指定可能にし、  
AND THE システム SHALL `--format <fmt>`オプションでフォーマットを指定可能にする。

**検証方法**: CLIテスト、E2Eテスト  
**受入基準**:
- [ ] 5つのサブコマンドが全て動作する
- [ ] 出力先指定が機能する
- [ ] フォーマット指定が機能する（markdown, plantuml）
- [ ] ヘルプが適切に表示される

**トレーサビリティ**: DES-CLI-002, TEST-CLI-002  
**憲法準拠**: Article II（CLI Interface Mandate）, Article VII（Design Patterns）

---

### REQ-CLI-003: Codegen CLIコマンド

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN ユーザーが`musubix codegen`コマンドを実行した場合,  
THE システム SHALL 以下のサブコマンドを提供する:

| サブコマンド | 説明 | 例 |
|-------------|------|-----|
| `generate <file>` | 設計からコードを生成 | `musubix codegen generate DES-001.md` |
| `analyze <file>` | 静的解析を実行 | `musubix codegen analyze src/` |
| `security <path>` | セキュリティスキャン | `musubix codegen security src/` |

AND THE システム SHALL `--language <lang>`オプションで出力言語を指定可能にし、  
AND THE システム SHALL `--framework <fw>`オプションでフレームワークを指定可能にする。

**検証方法**: CLIテスト、E2Eテスト  
**受入基準**:
- [ ] 3つのサブコマンドが全て動作する
- [ ] 言語指定が機能する（typescript, python, java等）
- [ ] フレームワーク指定が機能する
- [ ] ヘルプが適切に表示される

**トレーサビリティ**: DES-CLI-003, TEST-CLI-003  
**憲法準拠**: Article II（CLI Interface Mandate）

---

### REQ-CLI-004: Test CLIコマンド

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN ユーザーが`musubix test`コマンドを実行した場合,  
THE システム SHALL 以下のサブコマンドを提供する:

| サブコマンド | 説明 | 例 |
|-------------|------|-----|
| `generate <file>` | テストコードを生成 | `musubix test generate src/auth.ts` |
| `coverage <dir>` | カバレッジを測定 | `musubix test coverage src/` |

AND THE システム SHALL `--framework <fw>`オプションでテストフレームワークを指定可能にし、  
AND THE システム SHALL `--min-coverage <n>`オプションで最低カバレッジを指定可能にする。

**検証方法**: CLIテスト、E2Eテスト  
**受入基準**:
- [ ] 2つのサブコマンドが全て動作する
- [ ] フレームワーク指定が機能する（vitest, jest, pytest等）
- [ ] カバレッジ閾値チェックが機能する
- [ ] ヘルプが適切に表示される

**トレーサビリティ**: DES-CLI-004, TEST-CLI-004  
**憲法準拠**: Article II（CLI Interface Mandate）, Article III（Test-First）

---

### REQ-CLI-005: Trace CLIコマンド

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN ユーザーが`musubix trace`コマンドを実行した場合,  
THE システム SHALL 以下のサブコマンドを提供する:

| サブコマンド | 説明 | 例 |
|-------------|------|-----|
| `matrix` | トレーサビリティマトリクスを生成 | `musubix trace matrix` |
| `impact <id>` | 変更影響分析を実行 | `musubix trace impact REQ-001` |
| `validate` | トレーサビリティリンクを検証 | `musubix trace validate` |

AND THE システム SHALL `--format <fmt>`オプションでフォーマットを指定可能にし、  
AND THE システム SHALL `--output <file>`オプションで出力ファイルを指定可能にする。

**検証方法**: CLIテスト、E2Eテスト  
**受入基準**:
- [ ] 3つのサブコマンドが全て動作する
- [ ] フォーマット指定が機能する（markdown, csv, html）
- [ ] 出力ファイル指定が機能する
- [ ] ヘルプが適切に表示される

**トレーサビリティ**: DES-CLI-005, TEST-CLI-005  
**憲法準拠**: Article II（CLI Interface Mandate）, Article V（Traceability）

---

### REQ-CLI-006: Explain CLIコマンド

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN ユーザーが`musubix explain`コマンドを実行した場合,  
THE システム SHALL 以下のサブコマンドを提供する:

| サブコマンド | 説明 | 例 |
|-------------|------|-----|
| `why <id>` | 決定理由を説明 | `musubix explain why DES-001` |
| `graph <id>` | 推論グラフを生成 | `musubix explain graph DES-001` |

AND THE システム SHALL `--level <n>`オプションで説明の詳細度を指定可能にし、  
AND THE システム SHALL `--audience <type>`オプションで対象者を指定可能にする。

**検証方法**: CLIテスト、E2Eテスト  
**受入基準**:
- [ ] 2つのサブコマンドが全て動作する
- [ ] 詳細度指定が機能する（1-3）
- [ ] 対象者指定が機能する（developer, manager, stakeholder）
- [ ] ヘルプが適切に表示される

**トレーサビリティ**: DES-CLI-006, TEST-CLI-006  
**憲法準拠**: Article II（CLI Interface Mandate）

---

## 18. 要件トレーサビリティマトリクス

| 要件ID | カテゴリ | 設計コンポーネント | テストケース | 優先度 | 憲法準拠 |
|--------|---------|------------------|-------------|--------|----------|
| REQ-ARC-001 | アーキテクチャ | LibraryStructure | TEST-ARC-001 | P0 | Article I |
| REQ-ARC-002 | アーキテクチャ | CLIInterface | TEST-ARC-002 | P0 | Article II |
| REQ-INT-001 | 統合 | NeuroSymbolicIntegrator | TEST-INT-001 | P0 | - |
| REQ-INT-002 | 統合 | ConfidenceEvaluator | TEST-INT-002 | P0 | - |
| REQ-INT-003 | 統合 | ContradictionDetector | TEST-INT-003 | P0 | - |
| REQ-RA-001 | 要求分析 | EARSValidator | TEST-RA-001 | P0 | Article IV |
| REQ-RA-002 | 要求分析 | OntologyMapper | TEST-RA-002 | P0 | - |
| REQ-RA-003 | 要求分析 | RelatedRequirementsFinder | TEST-RA-003 | P1 | - |
| REQ-RA-004 | 要求分析 | RequirementsDecomposer | TEST-RA-004 | P2 | - |
| REQ-DES-001 | 設計 | PatternDetector | TEST-DES-001 | P0 | - |
| REQ-DES-002 | 設計 | FrameworkOptimizer | TEST-DES-002 | P0 | - |
| REQ-DES-003 | 設計 | SOLIDValidator | TEST-DES-003 | P0 | - |
| REQ-DES-004 | 設計 | C4ModelGenerator | TEST-DES-004 | P1 | - |
| REQ-DES-005 | 設計 | ADRGenerator | TEST-DES-005 | P1 | - |
| REQ-COD-001 | コード | CodeGenerator | TEST-COD-001 | P0 | - |
| REQ-COD-002 | コード | StaticAnalyzer | TEST-COD-002 | P0 | - |
| REQ-COD-003 | コード | PatternConformanceChecker | TEST-COD-003 | P0 | - |
| REQ-COD-004 | コード | DependencyAnalyzer | TEST-COD-004 | P0 | - |
| REQ-COD-005 | コード | CodingStandardsChecker | TEST-COD-005 | P1 | - |
| REQ-COD-006 | コード | SecurityScanner | TEST-COD-006 | P0 | - |
| REQ-TST-001 | テスト | UnitTestGenerator | TEST-TST-001 | P0 | Article III |
| REQ-TST-002 | テスト | IntegrationTestGenerator | TEST-TST-002 | P0 | Article IX |
| REQ-EXP-001 | 説明 | ReasoningChainRecorder | TEST-EXP-001 | P0 | - |
| REQ-EXP-002 | 説明 | ExplanationGenerator | TEST-EXP-002 | P0 | - |
| REQ-EXP-003 | 説明 | VisualExplanationGenerator | TEST-EXP-003 | P2 | - |
| REQ-TRA-001 | トレーサビリティ | TraceabilityManager | TEST-TRA-001 | P0 | Article V |
| REQ-TRA-002 | トレーサビリティ | ImpactAnalyzer | TEST-TRA-002 | P0 | Article V |
| REQ-ERR-001 | エラーリカバリ | GracefulDegradation | TEST-ERR-001 | P0 | - |
| REQ-ERR-002 | エラーリカバリ | DataPersistence | TEST-ERR-002 | P0 | - |
| REQ-ERR-003 | エラーリカバリ | VersionCompatibility | TEST-ERR-003 | P1 | - |
| REQ-PER-001 | パフォーマンス | - | TEST-PER-001 | P1 | - |
| REQ-PER-002 | パフォーマンス | - | TEST-PER-002 | P1 | - |
| REQ-QUA-001 | 品質 | QualityMetricsCalculator | TEST-QUA-001 | P0 | - |
| REQ-QUA-002 | 品質 | CoverageReporter | TEST-QUA-002 | P0 | Article III |
| REQ-SEC-001 | セキュリティ | DataProtector | TEST-SEC-001 | P0 | - |
| REQ-SEC-002 | セキュリティ | AuthManager | TEST-SEC-002 | P1 | - |
| REQ-INT-101 | 互換性 | PlatformAdapter | TEST-INT-101 | P0 | - |
| REQ-INT-102 | 互換性 | MCPServer | TEST-INT-102 | P0 | - |
| REQ-MNT-001 | 保守性 | Logger | TEST-MNT-001 | P1 | - |
| REQ-MNT-002 | 保守性 | ErrorHandler | TEST-MNT-002 | P0 | - |
| REQ-I18N-001 | 国際化 | I18nManager | TEST-I18N-001 | P2 | - |
| REQ-SKL-001 | Agent Skills | SkillDirectoryStructure | TEST-SKL-001 | P0 | Article VI |
| REQ-SKL-002 | Agent Skills | SkillFileValidator | TEST-SKL-002 | P0 | Article VI |
| REQ-SKL-003 | Agent Skills | SkillContentValidator | TEST-SKL-003 | P0 | Article VI |
| REQ-SKL-004 | Agent Skills | MuSubixSkillSet | TEST-SKL-004 | P0 | Article VI |
| REQ-CLI-001 | CLIコマンド | RequirementsCLI | TEST-CLI-001 | P0 | Article II, IV |
| REQ-CLI-002 | CLIコマンド | DesignCLI | TEST-CLI-002 | P0 | Article II, VII |
| REQ-CLI-003 | CLIコマンド | CodegenCLI | TEST-CLI-003 | P0 | Article II |
| REQ-CLI-004 | CLIコマンド | TestCLI | TEST-CLI-004 | P0 | Article II, III |
| REQ-CLI-005 | CLIコマンド | TraceCLI | TEST-CLI-005 | P0 | Article II, V |
| REQ-CLI-006 | CLIコマンド | ExplainCLI | TEST-CLI-006 | P1 | Article II |

---

## 19. 要件サマリー

### 優先度別集計

| 優先度 | 件数 | 割合 |
|--------|------|------|
| P0（必須） | 36 | 71% |
| P1（重要） | 8 | 16% |
| P2（任意） | 3 | 6% |
| Agent Skills | 4 | 8% |
| **合計** | **51** | **100%** |

### カテゴリ別集計

| カテゴリ | 件数 |
|---------|------|
| アーキテクチャ | 2 |
| 統合レイヤー | 3 |
| 要求分析 | 4 |
| 設計生成 | 5 |
| コード生成・検証 | 6 |
| テスト生成 | 2 |
| 説明生成 | 3 |
| トレーサビリティ | 2 |
| エラーリカバリ | 3 |
| CLIコマンド | 6 |
| パフォーマンス | 2 |
| 品質 | 2 |
| セキュリティ | 2 |
| 互換性 | 2 |
| 保守性 | 2 |
| 国際化 | 1 |
| Agent Skills | 4 |
| **合計** | **51** |

### 憲法準拠状況

| Article | 原則 | 対応要件 |
|---------|--------|----------|
| I | Library-First | REQ-ARC-001 |
| II | CLI Interface | REQ-ARC-002, REQ-CLI-001～006 |
| III | Test-First | REQ-TST-001, REQ-QUA-002, REQ-CLI-004 |
| IV | EARS Format | REQ-RA-001, REQ-CLI-001 |
| V | Traceability | REQ-TRA-001, REQ-TRA-002, REQ-CLI-005 |
| VI | Project Memory | REQ-SKL-001, REQ-SKL-002, REQ-SKL-003, REQ-SKL-004 |
| VII | Design Patterns | REQ-CLI-002 |
| VIII | Anti-Abstraction | (設計時に検証) |
| IX | Integration Testing | REQ-TST-002 |

---

## 19. 承認

| 役割 | 氏名 | 署名 | 日付 |
|------|------|------|------|
| プロダクトオーナー | | | |
| リードアーキテクト | | | |
| QAリード | | | |

---

## 改訂履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 1.0 | 2026-01-01 | 初版作成 | MUSUBIX |
| 1.1 | 2026-01-01 | 憲法準拠レビュー反映: アーキテクチャ要件追加、エラーリカバリ要件追加、国際化要件追加、数値基準具体化、セキュリティ脆弱性リスト拡充、REQ-TST-002をP0に格上げ | MUSUBIX |
| 1.2 | 2026-01-02 | GitHub Agent Skills仕様準拠: REQ-SKL-001〜004追加、要件数41→45、Article VI対応 | MUSUBIX |
| 1.3 | 2026-01-02 | 憲法準拠フィールド強化: REQ-SKL-001〜004にArticle VI、REQ-TST-001にArticle III、REQ-RA-001にArticle IV、REQ-TRA-001/002にArticle Vを追加 | MUSUBIX |
| 1.4 | 2026-01-02 | CLIコマンド要件追加: REQ-CLI-001〜006追加（requirements, design, codegen, test, trace, explain）、要件数45→51 | MUSUBIX |

---

**文書ID**: REQ-MUSUBIX-001  
**バージョン**: 1.4  
**最終更新**: 2026-01-02  
**次回レビュー**: 2026-01-15
