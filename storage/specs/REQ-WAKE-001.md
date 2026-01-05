# MUSUBIX Wake-Sleep学習エンジン 要件定義書

**文書ID**: REQ-WAKE-001  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.0  
**作成日**: 2026-01-05  
**ステータス**: Draft  
**準拠規格**: EARS（Easy Approach to Requirements Syntax）  
**ロードマップ参照**: Phase 3 - 学習・推論拡張

---

## 1. 概要

### 1.1 目的

DreamCoderアーキテクチャに基づくWake-Sleep学習エンジンを開発し、タスク解決（Wake Phase）と抽象化学習（Sleep Phase）の交互サイクルにより、プログラム合成の効率を継続的に向上させる。

### 1.2 スコープ

- Wake Phase: パターンライブラリを使用したタスク解決
- Sleep Phase: 解決策からのパターン抽象化
- 学習サイクルの自動実行
- パターンライブラリの継続的更新

### 1.3 理論的背景

DreamCoderは以下の2フェーズで学習を行う：

1. **Wake Phase（覚醒）**: 現在のパターンライブラリを使用してタスクを解決
2. **Sleep Phase（睡眠）**: 解決策から共通パターンを抽出・抽象化

この交互サイクルにより、ライブラリが徐々に強化され、より複雑なタスクを効率的に解決可能になる。

---

## 2. 機能要件

### REQ-WAKE-001-F001: Wake Phase - タスク解決

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN タスク例（入力→出力）の集合と現在のパターンライブラリが与えられた時,  
THE システム SHALL パターンを組み合わせてタスクを解決し,  
AND THE システム SHALL 解決策の探索に列挙的探索を使用し,  
AND THE システム SHALL 探索の深さと時間を制限し,  
AND THE システム SHALL 見つかった解決策と使用パターンの統計を返却する。

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] パターン組み合わせによる解決が動作する
- [ ] 探索深度制限が機能する
- [ ] タイムアウトが正しく動作する
- [ ] 使用パターン統計が生成される

**トレーサビリティ**: DES-WAKE-001, TSK-WAKE-001

---

### REQ-WAKE-001-F002: Sleep Phase - パターン抽象化

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN 解決策の集合が与えられた時,  
THE システム SHALL 共通サブ構造を識別し,  
AND THE システム SHALL 共通構造を抽象化して新規パターンを生成し,  
AND THE システム SHALL 新規パターンをライブラリに追加し,  
AND THE システム SHALL ライブラリの圧縮（冗長除去）を実行する。

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] 共通サブ構造が識別される
- [ ] 抽象化が正しく生成される
- [ ] ライブラリが更新される
- [ ] 冗長パターンが除去される

**トレーサビリティ**: DES-WAKE-002, TSK-WAKE-002

---

### REQ-WAKE-001-F003: 学習サイクル実行

**種別**: EVENT-DRIVEN  
**優先度**: P0（必須）

**要件**:  
WHEN Wake-Sleep学習サイクルの実行が要求された時,  
THE システム SHALL 指定回数のWake-Sleepサイクルを実行し,  
AND THE システム SHALL 各サイクルで解決成功率を記録し,  
AND THE システム SHALL ライブラリの成長を追跡し,  
AND THE システム SHALL 収束判定（改善停止）を行う。

**検証方法**: ユニットテスト、統合テスト  
**受入基準**:
- [ ] 複数サイクルが実行される
- [ ] 成功率が記録される
- [ ] ライブラリサイズが追跡される
- [ ] 収束判定が機能する

**トレーサビリティ**: DES-WAKE-003, TSK-WAKE-003

---

### REQ-WAKE-001-F004: 解決策の探索戦略

**種別**: STATE-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHILE タスク解決の探索中,  
THE システム SHALL 最小記述長（MDL）原理に基づいて解決策を評価し,  
AND THE システム SHALL 短いプログラムを優先的に探索し,  
AND THE システム SHALL ビームサーチで候補を絞り込む。

**検証方法**: ユニットテスト  
**受入基準**:
- [ ] MDLスコアが計算される
- [ ] 短いプログラムが優先される
- [ ] ビームサーチが動作する

**トレーサビリティ**: DES-WAKE-004, TSK-WAKE-004

---

### REQ-WAKE-001-F005: 抽象化の品質評価

**種別**: EVENT-DRIVEN  
**優先度**: P1（重要）

**要件**:  
WHEN 新規パターンの抽象化が生成された時,  
THE システム SHALL 抽象化の汎用性スコアを計算し,  
AND THE システム SHALL 再利用可能性を評価し,  
AND THE システム SHALL 低品質な抽象化をフィルタリングする。

**検証方法**: ユニットテスト  
**受入基準**:
- [ ] 汎用性スコアが計算される
- [ ] 再利用可能性が評価される
- [ ] フィルタリングが機能する

**トレーサビリティ**: DES-WAKE-005, TSK-WAKE-005

---

### REQ-WAKE-001-F006: 学習進捗の可視化

**種別**: UBIQUITOUS  
**優先度**: P1（重要）

**要件**:  
THE システム SHALL 学習サイクルごとの進捗をログ出力し,  
AND THE システム SHALL 解決成功率の推移グラフを生成し,  
AND THE システム SHALL ライブラリ成長の統計を表示する。

**検証方法**: E2Eテスト、CLIテスト  
**受入基準**:
- [ ] 進捗ログが出力される
- [ ] 成功率推移が表示される
- [ ] ライブラリ統計が表示される

**トレーサビリティ**: DES-WAKE-006, TSK-WAKE-006

---

## 3. MCPツール仕様

### 3.1 wake_phase

```typescript
{
  "name": "wake_phase",
  "description": "Wake Phase: パターンライブラリを使用してタスクを解決",
  "inputSchema": {
    "type": "object",
    "properties": {
      "task_examples": {
        "type": "array",
        "items": {
          "type": "object",
          "properties": {
            "input": { "type": "any" },
            "output": { "type": "any" }
          }
        },
        "description": "入力→出力のタスク例"
      },
      "library_path": { "type": "string", "description": "パターンライブラリのパス" },
      "max_depth": { "type": "number", "default": 5, "description": "探索深度上限" },
      "timeout_ms": { "type": "number", "default": 30000, "description": "タイムアウト（ミリ秒）" }
    },
    "required": ["task_examples", "library_path"]
  },
  "outputSchema": {
    "type": "object",
    "properties": {
      "solutions": {
        "type": "array",
        "items": {
          "type": "object",
          "properties": {
            "program": { "type": "string" },
            "mdl_score": { "type": "number" },
            "patterns_used": { "type": "array" }
          }
        }
      },
      "success_rate": { "type": "number" },
      "pattern_usage_stats": { "type": "object" }
    }
  }
}
```

### 3.2 sleep_phase

```typescript
{
  "name": "sleep_phase",
  "description": "Sleep Phase: 解決策から共通パターンを抽出・抽象化",
  "inputSchema": {
    "type": "object",
    "properties": {
      "solutions": {
        "type": "array",
        "items": { "type": "string" },
        "description": "Wake Phaseで見つかった解決策"
      },
      "library_path": { "type": "string", "description": "パターンライブラリのパス" },
      "min_abstraction_score": { "type": "number", "default": 0.5, "description": "抽象化品質閾値" }
    },
    "required": ["solutions", "library_path"]
  },
  "outputSchema": {
    "type": "object",
    "properties": {
      "new_patterns": {
        "type": "array",
        "items": {
          "type": "object",
          "properties": {
            "id": { "type": "string" },
            "abstraction": { "type": "string" },
            "generality_score": { "type": "number" }
          }
        }
      },
      "library_compression": {
        "type": "object",
        "properties": {
          "removed_count": { "type": "number" },
          "merged_count": { "type": "number" }
        }
      }
    }
  }
}
```

### 3.3 wake_sleep_cycle

```typescript
{
  "name": "wake_sleep_cycle",
  "description": "Wake-Sleep学習サイクルを実行",
  "inputSchema": {
    "type": "object",
    "properties": {
      "task_examples": {
        "type": "array",
        "description": "タスク例の集合"
      },
      "library_path": { "type": "string", "description": "パターンライブラリのパス" },
      "num_cycles": { "type": "number", "default": 3, "description": "サイクル回数" },
      "convergence_threshold": { "type": "number", "default": 0.01, "description": "収束判定閾値" }
    },
    "required": ["task_examples", "library_path"]
  },
  "outputSchema": {
    "type": "object",
    "properties": {
      "updated_library_path": { "type": "string" },
      "cycle_results": {
        "type": "array",
        "items": {
          "type": "object",
          "properties": {
            "cycle": { "type": "number" },
            "success_rate": { "type": "number" },
            "new_patterns_count": { "type": "number" },
            "library_size": { "type": "number" }
          }
        }
      },
      "converged": { "type": "boolean" },
      "total_new_patterns": { "type": "number" }
    }
  }
}
```

---

## 4. 非機能要件

### REQ-WAKE-001-NF001: パフォーマンス

**要件**:  
THE システム SHALL 100タスクのWake Phaseを5分以内に完了し,  
AND THE システム SHALL Sleep Phaseを1分以内に完了する。

### REQ-WAKE-001-NF002: スケーラビリティ

**要件**:  
THE システム SHALL 1000以上のタスク例に対応し,  
AND THE システム SHALL 10000パターン以上のライブラリで動作する。

### REQ-WAKE-001-NF003: 学習効率

**要件**:  
THE システム SHALL 3サイクル以内で解決成功率を20%以上向上させ,  
AND THE システム SHALL 無限ループを検出して回避する。

### REQ-WAKE-001-NF004: リソース制約

**種別**: UNWANTED  
**優先度**: P0（必須）

**要件**:  
THE システム SHALL NOT メモリ使用量2GBを超過し,  
AND THE システム SHALL NOT CPU使用率100%で10分以上連続して実行し,  
AND THE システム SHALL NOT ユーザーの同意なくバックグラウンドで学習を実行する。

**検証方法**: パフォーマンステスト  
**受入基準**:
- [ ] メモリ制限が守られる
- [ ] タイムアウトが機能する
- [ ] 明示的な実行要求が必要

---

## 5. アルゴリズム詳細

### 5.1 Wake Phase アルゴリズム

```
Algorithm: Wake Phase
Input: TaskExamples T, PatternLibrary L, MaxDepth d
Output: Solutions S, PatternUsageStats

1. Initialize priority queue Q with primitive patterns
2. For each task t in T:
   a. candidates ← ∅
   b. While Q is not empty and depth < d:
      i.  p ← Q.pop()
      ii. For each pattern π in L:
          - combined ← combine(p, π)
          - If combined satisfies t: add to candidates
          - Else: Q.push(combined) with MDL score
   c. S[t] ← best candidate by MDL
3. Return S, usage statistics
```

### 5.2 Sleep Phase アルゴリズム

```
Algorithm: Sleep Phase
Input: Solutions S, PatternLibrary L
Output: NewPatterns, CompressedLibrary

1. Build E-graph E from all solutions
2. Find common subexpressions using anti-unification
3. For each common subexpression c:
   a. abstraction ← generalize(c)
   b. score ← evaluate_generality(abstraction)
   c. If score > threshold: NewPatterns.add(abstraction)
4. L' ← L ∪ NewPatterns
5. CompressedLibrary ← compress(L')
6. Return NewPatterns, CompressedLibrary
```

---

## 6. 制約事項

- タスクはプログラム合成問題（入力→出力）の形式のみ
- 探索空間が指数的に増大するため、深度制限が必須
- リアルタイム学習は非サポート（バッチ処理のみ）
- メモリ使用量は最大2GBまで

---

## 7. 依存関係

| 依存先 | 種別 | 説明 |
|-------|------|------|
| REQ-PATTERN-001 | **機能委譲** | パターン抽出・抽象化・ライブラリ管理を使用（重複実装しない） |
| REQ-LEARN-001 | 機能連携 | 既存学習システムとのフィードバック連携 |
| tree-sitter | 外部ライブラリ | AST操作（REQ-PATTERN-001経由） |

**注意**: Sleep Phaseのパターン抽象化はREQ-PATTERN-001-F002を呼び出す。本要件はサイクル管理に特化する。

---

## 8. 用語定義

| 用語 | 定義 |
|------|------|
| Wake Phase | パターンを使用してタスクを解決するフェーズ |
| Sleep Phase | 解決策からパターンを抽象化するフェーズ |
| MDL | Minimum Description Length（最小記述長） |
| E-graph | 等価クラスを表現するデータ構造 |
| Anti-unification | 複数の式から最も一般的な形を抽出する操作 |
| DreamCoder | MIT発のプログラム合成・学習システム |

---

**文書履歴**:
| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 1.0 | 2026-01-05 | 初版作成 | Claude |
