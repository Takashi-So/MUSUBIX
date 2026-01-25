---
name: eval-harness
description: |
  評価ハーネススキル。pass@kメトリクスでAIコード生成の品質を評価する。
  機能評価（Capability）と回帰評価（Regression）の両方をサポートする。
  Human Graderによる人手評価もサポート。
license: MIT
---

# Eval Harness Skill

## 目的

AIコード生成の品質を定量的に評価し、以下を実現する：
- 機能評価（Capability Eval）による新機能の品質測定
- 回帰評価（Regression Eval）による既存機能の品質維持確認
- pass@kメトリクスによる統計的な信頼度評価
- 人手評価（Human Grader）による主観的品質評価

## トレーサビリティ

- REQ-EH-001: Capability Eval Definition
- REQ-EH-002: Regression Eval Definition
- REQ-EH-003: pass@k Metrics
- REQ-EH-004: Grader Types
- REQ-EH-005: Human Grader Support

---

## 1. 機能評価（Capability Eval）の定義

新機能や新しいタスクの品質を評価する際は、以下の形式で評価を定義してください：

### 評価定義フォーマット

```markdown
[CAPABILITY EVAL: <feature-name>]

Task: <達成すべきタスクの説明>

Success Criteria:
  - [ ] <成功基準1>
  - [ ] <成功基準2>
  - [ ] <成功基準3>
  - [ ] <成功基準4（任意）>

Expected Output: <期待される出力の説明>

Constraints:
  - <制約条件1>
  - <制約条件2>

Test Command: <テスト実行コマンド>
```

### 使用例

```markdown
[CAPABILITY EVAL: user-authentication]

Task: JWTベースのユーザー認証機能を実装する

Success Criteria:
  - [ ] ログインエンドポイントが正常に動作する
  - [ ] JWTトークンが正しく生成される
  - [ ] トークン検証ミドルウェアが機能する
  - [ ] リフレッシュトークンが実装されている

Expected Output: 
  - POST /api/auth/login → 200 OK + JWT token
  - GET /api/protected → 401 without token, 200 with valid token

Constraints:
  - bcryptを使用したパスワードハッシュ
  - トークン有効期限: 15分

Test Command: npm run test:auth
```

---

## 2. 回帰評価（Regression Eval）の定義

既存機能の品質が維持されているかを評価する際は、以下の形式を使用してください：

### 評価定義フォーマット

```markdown
[REGRESSION EVAL: <feature-name>]

Baseline: <ベースラインのGit SHA またはチェックポイント名>

Tests:
  - <test-name-1>: <PASS|FAIL>
  - <test-name-2>: <PASS|FAIL>
  - <test-name-3>: <PASS|FAIL>

Result: X/Y passed (previously Y/Y)

Regression Detected: <Yes|No>

Notes:
  - <追加の注記>
```

### 使用例

```markdown
[REGRESSION EVAL: user-service]

Baseline: abc1234 (v3.6.0 release)

Tests:
  - user.create.test.ts: PASS
  - user.update.test.ts: PASS
  - user.delete.test.ts: FAIL
  - user.search.test.ts: PASS

Result: 3/4 passed (previously 4/4)

Regression Detected: Yes

Notes:
  - user.delete.test.ts: 新しいバリデーションにより失敗
  - 意図的な変更か確認が必要
```

---

## 3. pass@k メトリクス

AIコード生成の信頼度を評価するため、以下のメトリクスを計算・報告してください：

### メトリクス定義

| メトリクス | 定義 | 用途 |
|-----------|------|------|
| **pass@1** | 初回試行で成功する確率 | 基本的な信頼度の指標 |
| **pass@3** | 3回の試行で少なくとも1回成功する確率 | 一般的なターゲット |
| **consecutive@3** | 3回連続で成功する確率 | クリティカルパス向け |

### 計算方法

```
pass@1 = (成功回数) / (試行回数)
pass@k = 1 - C(n-c, k) / C(n, k)
  where n = 総試行回数, c = 成功回数, k = 試行数
consecutive@3 = (3回連続成功のシーケンス数) / (可能なシーケンス数)
```

### レポートフォーマット

```markdown
[PASS@K REPORT: <feature-name>]

Trials: <試行回数>
Successes: <成功回数>

Metrics:
  - pass@1: XX.X%
  - pass@3: XX.X%
  - consecutive@3: XX.X%

Target: pass@3 >= 90%
Status: <PASS|FAIL>

Trial History:
  1. [PASS] - <説明>
  2. [FAIL] - <失敗理由>
  3. [PASS] - <説明>
  ...
```

### 目標値

| シナリオ | pass@1 | pass@3 | consecutive@3 |
|---------|--------|--------|---------------|
| **標準** | >= 60% | >= 90% | >= 70% |
| **クリティカル** | >= 80% | >= 95% | >= 90% |
| **実験的** | >= 40% | >= 70% | >= 50% |

---

## 4. 評価器タイプ（Grader Types）

評価を実行する際は、以下の評価器タイプを適切に選択してください：

### 4.1 Code-Based Grader（コードベース評価器）

**用途**: 決定的に判定可能な評価

**実行方法**:
```bash
# テストコマンドを実行
npm run test:<feature>

# 終了コードで判定
# 0 = PASS, non-0 = FAIL
```

**適用例**:
- ユニットテストの合格/不合格
- ビルドの成功/失敗
- リントエラーの有無
- 型チェックの結果

### 4.2 Model-Based Grader（モデルベース評価器）

**用途**: 自由形式の出力を評価

**評価プロンプト例**:
```markdown
以下のコード出力を評価してください：

[コード出力]
...

評価基準：
1. 機能要件を満たしているか (0-10)
2. コード品質は適切か (0-10)
3. エッジケースが考慮されているか (0-10)
4. ドキュメントは十分か (0-10)

総合スコア: XX/40
合格ライン: 30/40
```

**適用例**:
- コードレビュー品質の評価
- ドキュメント生成の品質
- リファクタリングの適切性
- 設計判断の妥当性

---

## 5. Human Grader（人手評価）

自動評価だけでは判定が困難な場合、以下のテンプレートで人手評価を記録してください：

### 評価テンプレート

```markdown
[HUMAN GRADE: <feature-name>]

Reviewer: @<username>
Date: YYYY-MM-DD

Checklist:
  - [ ] 仕様を満たしている
  - [ ] エッジケースが考慮されている
  - [ ] 既存API互換性が維持されている
  - [ ] セキュリティ上の懸念がない
  - [ ] パフォーマンス要件を満たす
  - [ ] コードが読みやすい
  - [ ] テストカバレッジが十分

Scores (1-5):
  - Functionality: X/5
  - Code Quality: X/5
  - Maintainability: X/5
  - Documentation: X/5

Total: XX/20

Notes:
  - <評価者のコメント>
  - <改善提案>

Verdict: <PASS|FAIL|NEEDS_REVISION>

Signature: [Reviewer Name] - [Date]
```

### 使用タイミング

Human Graderを使用すべき場合：
- UI/UXの主観的評価
- アーキテクチャ決定の妥当性
- コードスタイルの一貫性
- ドメイン固有の要件適合性
- セキュリティレビュー

---

## 6. 評価ワークフロー

### 6.1 評価の実行手順

1. **評価定義**: Capability または Regression Evalを定義
2. **評価器選択**: Code-Based, Model-Based, Human のいずれかを選択
3. **試行実行**: 複数回の試行を実行（pass@k測定時）
4. **結果記録**: 評価結果をMarkdown形式で記録
5. **レポート生成**: 最終レポートを生成

### 6.2 統合コマンド

```bash
# 機能評価の実行
/eval capability <feature-name>

# 回帰評価の実行
/eval regression <feature-name> --baseline <sha>

# pass@kの計算
/eval pass-at-k <feature-name> --trials 10

# 人手評価テンプレートの生成
/eval human <feature-name>
```

---

## 7. MCP ツール統合

このスキルはMUSUBIX MCPサーバーの以下のツールと連携します：

- `workflow_get_status`: ワークフロー状態取得（評価フェーズの確認）
- `sdd_validate_traceability`: トレーサビリティ検証（要件↔テストの追跡）
- `knowledge_query`: 知識グラフ検索（過去の評価結果の参照）

MCPツールが利用可能な場合は、それらを優先的に使用してください。

---

## 8. 評価結果の保存

評価結果は以下のディレクトリ構造で保存してください：

```
.reports/
└── evals/
    ├── capability/
    │   └── <feature-name>-YYYY-MM-DD.md
    ├── regression/
    │   └── <feature-name>-YYYY-MM-DD.md
    └── pass-at-k/
        └── <feature-name>-YYYY-MM-DD.md
```

---

## 9. ベストプラクティス

### 評価定義時

- 成功基準は測定可能で明確にする
- 最低3つ、最大7つの成功基準を設定
- Expected Outputは具体例を含める
- 制約条件は明示的に記述

### pass@k測定時

- 最低5回、推奨10回の試行を実行
- 各試行は独立して実行（キャッシュをクリア）
- 失敗理由を詳細に記録
- 環境要因（ネットワーク、リソース）を考慮

### Human Grader使用時

- 複数のレビュアーによる評価を推奨
- チェックリストは事前に合意
- 評価基準は文書化して一貫性を保つ
- 主観的判断は理由を明記

---

**Version**: 1.0.0  
**Last Updated**: 2026-01-25  
**Maintainer**: MUSUBIX Team
