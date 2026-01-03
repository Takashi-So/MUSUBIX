# MUSUBIX 自己学習機能 要件定義書

**文書ID**: REQ-LEARN-001  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-03  
**ステータス**: Draft  
**準拠規格**: EARS（Easy Approach to Requirements Syntax）

---

## 1. 概要

### 1.1 目的

MUSUBIXに自己学習機能を追加し、プロジェクト開発を通じて得られたフィードバックとパターンから能動的に学習・改善する能力を実現する。

### 1.2 スコープ

- フィードバック収集・分析
- パターン抽出・登録
- 学習モデル更新
- 適応的推論

---

## 2. 機能要件

### REQ-LEARN-001: フィードバック収集

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN ユーザーがコード生成・設計・要件分析の結果を受け入れまたは拒否した時,  
THE システム SHALL フィードバックデータを収集し,  
AND THE システム SHALL フィードバックを構造化形式で永続化し,  
AND THE システム SHALL フィードバックにコンテキスト情報（プロジェクト、言語、フレームワーク）を付与する。

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] accept/reject フィードバックが記録される
- [ ] フィードバックがJSON形式で永続化される
- [ ] コンテキスト情報が自動付与される

**トレーサビリティ**: DES-LEARN-001, TSK-LEARN-001

---

### REQ-LEARN-002: パターン抽出

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN 同一パターンのフィードバックが閾値（デフォルト3回）を超えた時,  
THE システム SHALL パターンを自動抽出し,  
AND THE システム SHALL パターンに信頼度スコアを付与し,  
AND THE システム SHALL パターンを知識グラフに登録する。

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] 繰り返しパターンが自動検出される
- [ ] 信頼度スコアが計算される
- [ ] パターンが知識グラフに追加される

**トレーサビリティ**: DES-LEARN-002, TSK-LEARN-002

---

### REQ-LEARN-003: 適応的推論

**種別**: STATE-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHILE 学習済みパターンが存在する状態で,  
THE システム SHALL 新しい推論時にパターンを参照し,  
AND THE システム SHALL パターンの信頼度に基づいて推論を調整し,  
AND THE システム SHALL 高信頼度パターンを優先適用する。

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] 推論時にパターンが参照される
- [ ] 信頼度による重み付けが行われる
- [ ] パターン適用の説明が生成される

**トレーサビリティ**: DES-LEARN-003, TSK-LEARN-003

---

### REQ-LEARN-004: パターン減衰

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN パターンが一定期間（デフォルト30日）使用されなかった時,  
THE システム SHALL パターンの信頼度を減衰させ,  
AND THE システム SHALL 信頼度が閾値（0.1）を下回ったパターンをアーカイブする。

**検証方法**: ユニットテスト  
**受入基準**:
- [ ] 未使用パターンの信頼度が減衰する
- [ ] 低信頼度パターンがアーカイブされる

**トレーサビリティ**: DES-LEARN-004, TSK-LEARN-004

---

### REQ-LEARN-005: 学習状態の可視化

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
THE システム SHALL 学習状態のダッシュボードを提供し,  
AND THE システム SHALL パターン一覧と信頼度を表示し,  
AND THE システム SHALL 学習履歴をエクスポート可能にする。

**検証方法**: E2Eテスト、CLIテスト  
**受入基準**:
- [ ] `musubix learn status` でダッシュボード表示
- [ ] パターン一覧がJSON/Markdown形式で出力可能
- [ ] 学習履歴のエクスポート機能

**トレーサビリティ**: DES-LEARN-005, TSK-LEARN-005

---

### REQ-LEARN-006: プライバシー保護

**種別**: UNWANTED  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL NOT 個人情報・機密情報を学習データに含め,  
AND THE システム SHALL NOT 学習データを外部に送信し,  
AND THE システム SHALL ローカルストレージのみを使用する。

**検証方法**: セキュリティレビュー、コードレビュー  
**受入基準**:
- [ ] 学習データがローカルに保存される
- [ ] 外部通信がない
- [ ] 機密情報フィルタリングが実装されている

**トレーサビリティ**: DES-LEARN-006, TSK-LEARN-006

---

## 3. 非機能要件

### REQ-LEARN-NFR-001: パフォーマンス

**要件**:  
THE システム SHALL フィードバック記録を100ms以内に完了し,  
AND THE システム SHALL パターン検索を50ms以内に完了する。

### REQ-LEARN-NFR-002: スケーラビリティ

**要件**:  
THE システム SHALL 10,000件以上のパターンを効率的に管理し,  
AND THE システム SHALL パターン数増加に対してO(log n)の検索性能を維持する。

---

## 4. CLIコマンド

```bash
# フィードバック記録
npx musubix learn feedback <id> --accept|--reject [--reason <text>]

# パターン一覧表示
npx musubix learn patterns [--format json|markdown]

# 学習状態表示
npx musubix learn status

# パターン手動登録
npx musubix learn add-pattern <name> --context <ctx> --confidence <0-1>

# パターン削除
npx musubix learn remove-pattern <id>

# 学習データエクスポート
npx musubix learn export [--output <file>]

# 学習データインポート
npx musubix learn import <file>

# パターン減衰実行
npx musubix learn decay [--days <n>]
```

---

## 5. データモデル

### 5.1 Feedback

```typescript
interface Feedback {
  id: string;
  timestamp: Date;
  type: 'accept' | 'reject' | 'modify';
  artifactType: 'requirement' | 'design' | 'code' | 'test';
  artifactId: string;
  context: {
    project: string;
    language?: string;
    framework?: string;
    tags: string[];
  };
  reason?: string;
  original?: string;
  modified?: string;
}
```

### 5.2 Pattern

```typescript
interface LearnedPattern {
  id: string;
  name: string;
  category: 'code' | 'design' | 'requirement' | 'test';
  trigger: {
    context: Record<string, string>;
    conditions: string[];
  };
  action: {
    type: 'prefer' | 'avoid' | 'suggest';
    content: string;
  };
  confidence: number;  // 0.0 - 1.0
  occurrences: number;
  lastUsed: Date;
  createdAt: Date;
  source: 'auto' | 'manual';
}
```

---

## 6. トレーサビリティマトリクス

| 要件ID | 設計ID | タスクID | テストID |
|--------|--------|----------|----------|
| REQ-LEARN-001 | DES-LEARN-001 | TSK-LEARN-001 | TEST-LEARN-001 |
| REQ-LEARN-002 | DES-LEARN-002 | TSK-LEARN-002 | TEST-LEARN-002 |
| REQ-LEARN-003 | DES-LEARN-003 | TSK-LEARN-003 | TEST-LEARN-003 |
| REQ-LEARN-004 | DES-LEARN-004 | TSK-LEARN-004 | TEST-LEARN-004 |
| REQ-LEARN-005 | DES-LEARN-005 | TSK-LEARN-005 | TEST-LEARN-005 |
| REQ-LEARN-006 | DES-LEARN-006 | TSK-LEARN-006 | TEST-LEARN-006 |

---

**承認者**: _________________  
**承認日**: _________________
