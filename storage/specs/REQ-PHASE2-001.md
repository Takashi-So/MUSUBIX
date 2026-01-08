# REQ-PHASE2-001: Phase 2 Advanced Learning 要件定義

**バージョン**: 1.0  
**作成日**: 2026-01-08  
**ステータス**: Draft  
**優先度**: P0  
**トレーサビリティ**: MUSUBIX-Roadmap-v2.md Section 4

---

## 1. 概要

Phase 2「Advanced Learning」は、MUSUBIXの学習システムを高度化し、DreamCoder式のライブラリ学習、Neural誘導探索、およびプログラム合成DSLを実装する。

### 1.1 目標

- 学習済みパターンから階層的抽象概念を抽出
- ニューラルモデルによる探索空間の効率的削減
- ドメイン固有言語による演繹的プログラム合成

### 1.2 スコープ

| コンポーネント | パッケージ名 | 説明 |
|--------------|-------------|------|
| ライブラリ学習 | `@nahisaho/musubix-library-learner` | DreamCoder式階層的抽象化 |
| Neural探索 | `@nahisaho/musubix-neural-search` | 探索誘導・プルーニング |
| 合成DSL | `@nahisaho/musubix-synthesis` | PROSE式プログラム合成 |

---

## 2. コンポーネント1: ライブラリ学習 (musubix-library-learner)

### 2.1 機能要件

#### REQ-LL-001: 階層的抽象化 [P0]

**EARS形式**:
```
WHEN the system observes recurring code patterns,
THE LibraryLearner SHALL extract hierarchical abstractions
  at multiple levels of generalization.
```

**詳細**:
- 最低3レベルの抽象化階層をサポート
- パターン出現頻度に基づく抽象化候補の識別
- 型情報を考慮した抽象化

**受入基準**:
- [ ] レベル1: 具体的コードパターン
- [ ] レベル2: パラメータ化されたテンプレート
- [ ] レベル3: 高次抽象概念（デザインパターン等）

#### REQ-LL-002: ライブラリ成長 [P0]

**EARS形式**:
```
WHILE the system is in wake-sleep learning cycle,
THE LibraryLearner SHALL automatically expand the pattern library
  with newly discovered abstractions.
```

**詳細**:
- Wake Phaseで新パターン候補を検出
- Sleep Phaseでライブラリを最適化・統合
- 品質メトリクスに基づく自動プルーニング

**受入基準**:
- [ ] ライブラリ自動拡張機能
- [ ] 重複・類似パターンの統合
- [ ] 未使用パターンの減衰・削除

#### REQ-LL-003: 型指向探索 [P1]

**EARS形式**:
```
WHEN synthesizing code from specifications,
THE LibraryLearner SHALL use type information
  to reduce the search space.
```

**詳細**:
- TypeScript型情報の活用
- 型互換性による候補フィルタリング
- ジェネリクス・ユニオン型対応

**受入基準**:
- [ ] 型ベースの探索空間削減（50%以上）
- [ ] 型エラー候補の早期排除
- [ ] 型推論による候補スコアリング

#### REQ-LL-004: E-graph最適化 [P2]

**EARS形式**:
```
IF the pattern library contains equivalent expressions,
THEN THE LibraryLearner SHALL use E-graph representation
  to optimize and deduplicate patterns.
```

**詳細**:
- 等価性グラフ（E-graph）による表現
- 等価クラスの自動検出
- 最適表現の選択

**受入基準**:
- [ ] E-graph構築機能
- [ ] 等価性ルールの定義
- [ ] 表現最適化（20%以上のサイズ削減）

### 2.2 非機能要件

| ID | 要件 | 目標値 |
|----|------|--------|
| NFR-LL-001 | ライブラリサイズ | 10,000+パターン |
| NFR-LL-002 | 学習スループット | 100パターン/秒 |
| NFR-LL-003 | 探索削減率 | 10^6以上 |
| NFR-LL-004 | メモリ使用量 | <2GB |

---

## 3. コンポーネント2: Neural Search Guidance (musubix-neural-search)

### 3.1 機能要件

#### REQ-NS-001: 分岐スコアリング [P0]

**EARS形式**:
```
WHEN exploring the synthesis search tree,
THE NeuralSearch SHALL score each branch
  using a neural model to predict success probability.
```

**詳細**:
- 各探索分岐の成功確率を予測
- Embeddingベースの類似度計算
- 過去の探索履歴からの学習

**受入基準**:
- [ ] 分岐スコア計算（0-1）
- [ ] スコア予測精度 >70%
- [ ] リアルタイムスコアリング（<10ms/分岐）

#### REQ-NS-002: 探索優先順位付け [P0]

**EARS形式**:
```
WHILE searching for solutions,
THE NeuralSearch SHALL prioritize exploration
  of branches with higher neural scores.
```

**詳細**:
- Best-First探索の実装
- Beam Search with neural guidance
- 動的優先度調整

**受入基準**:
- [ ] Best-First探索実装
- [ ] Beam幅の動的調整
- [ ] 探索効率 >10x（ランダム探索比）

#### REQ-NS-003: 学習ベースプルーニング [P1]

**EARS形式**:
```
IF a search branch has consistently low scores,
THEN THE NeuralSearch SHALL prune that branch
  to avoid wasted computation.
```

**詳細**:
- 低スコア分岐の早期打ち切り
- 動的閾値調整
- 誤プルーニングの検出と回復

**受入基準**:
- [ ] プルーニング閾値の自動調整
- [ ] 誤プルーニング率 <5%
- [ ] 計算削減率 >50%

#### REQ-NS-004: 探索履歴学習 [P2]

**EARS形式**:
```
AFTER completing a synthesis task,
THE NeuralSearch SHALL learn from the search trajectory
  to improve future search guidance.
```

**詳細**:
- 成功/失敗パスの記録
- オンライン学習による改善
- 転移学習の活用

**受入基準**:
- [ ] 探索履歴の永続化
- [ ] 継続的学習メカニズム
- [ ] 学習後の精度向上 >10%

### 3.2 非機能要件

| ID | 要件 | 目標値 |
|----|------|--------|
| NFR-NS-001 | スコアリング速度 | <10ms/分岐 |
| NFR-NS-002 | 探索効率 | 10x向上 |
| NFR-NS-003 | メモリ使用量 | <500MB |
| NFR-NS-004 | モデルサイズ | <100MB |

---

## 4. コンポーネント3: プログラム合成DSL (musubix-synthesis)

### 4.1 機能要件

#### REQ-SYN-001: DSL定義フレームワーク [P0]

**EARS形式**:
```
THE DSLFramework SHALL provide a declarative way
  to define domain-specific languages
  with operators, types, and semantics.
```

**詳細**:
- 演算子の宣言的定義
- 型システムの定義
- 意味論（実行セマンティクス）の定義

**受入基準**:
- [ ] 演算子定義API
- [ ] 型シグネチャ定義
- [ ] 実行可能なDSL生成

#### REQ-SYN-002: Witness関数 [P1]

**EARS形式**:
```
WHEN synthesizing programs deductively,
THE DSLFramework SHALL use witness functions
  to decompose specifications into sub-problems.
```

**詳細**:
- FlashMeta式のWitness関数
- 逆実行による仕様分解
- 部分仕様の伝播

**受入基準**:
- [ ] Witness関数定義API
- [ ] 仕様分解メカニズム
- [ ] 合成性能 >100x（列挙比）

#### REQ-SYN-003: 例示合成 (PBE) [P1]

**EARS形式**:
```
WHEN given input-output examples,
THE ProgramSynthesizer SHALL synthesize a program
  that satisfies all given examples.
```

**詳細**:
- Programming by Example (PBE)
- 複数例からの一般化
- 曖昧性解決

**受入基準**:
- [ ] 入出力例からの合成
- [ ] 5例以下での合成成功率 >80%
- [ ] 合成時間 <5秒

#### REQ-SYN-004: 合成ルール学習 [P2]

**EARS形式**:
```
IF the system observes successful synthesis patterns,
THEN THE DSLFramework SHALL learn new synthesis rules
  to accelerate future synthesis tasks.
```

**詳細**:
- 成功パターンからのルール抽出
- メタ学習による合成高速化
- ドメイン特化ルールの自動生成

**受入基準**:
- [ ] ルール自動抽出
- [ ] 学習後の合成速度向上 >2x
- [ ] ルールライブラリの成長

### 4.2 非機能要件

| ID | 要件 | 目標値 |
|----|------|--------|
| NFR-SYN-001 | 合成時間 | <5秒 |
| NFR-SYN-002 | 成功率 | >80% |
| NFR-SYN-003 | DSL複雑度 | 50+演算子 |
| NFR-SYN-004 | 例数 | 5例以下 |

---

## 5. 統合要件

### 5.1 パッケージ間連携

#### REQ-INT-001: ライブラリ学習とNeural探索の統合

**EARS形式**:
```
WHEN the NeuralSearch explores synthesis options,
THE system SHALL use LibraryLearner's abstractions
  as primitives in the search space.
```

**受入基準**:
- [ ] 学習済みライブラリの探索空間への統合
- [ ] 抽象度に応じた優先度付け

#### REQ-INT-002: Neural探索とDSL合成の統合

**EARS形式**:
```
WHEN synthesizing DSL programs,
THE system SHALL use NeuralSearch
  to guide the synthesis process.
```

**受入基準**:
- [ ] DSL合成へのNeural誘導適用
- [ ] 分岐スコアリングのDSL演算子対応

#### REQ-INT-003: Phase 1パッケージとの連携

**EARS形式**:
```
THE Phase 2 packages SHALL integrate with
  musubix-dfg, musubix-lean, and yata-scale
  for data flow analysis, verification, and knowledge storage.
```

**受入基準**:
- [ ] DFGからのパターン抽出
- [ ] Lean 4による合成結果検証
- [ ] YATA Scaleへのパターン永続化

---

## 6. テスト要件

### 6.1 ユニットテスト

| パッケージ | 最低テスト数 | カバレッジ目標 |
|-----------|-------------|---------------|
| musubix-library-learner | 100 | 80% |
| musubix-neural-search | 80 | 80% |
| musubix-synthesis | 120 | 80% |

### 6.2 統合テスト

- E2Eシナリオ: 5以上
- パッケージ間連携テスト: 10以上

### 6.3 ベンチマーク

| ベンチマーク | 目標 |
|-------------|------|
| 探索削減率 | 10^6以上 |
| 合成成功率 | 80%以上 |
| 学習スループット | 100パターン/秒 |

---

## 7. 依存関係

### 7.1 内部依存

```
musubix-library-learner
  ├── @nahisaho/musubix-core
  ├── @nahisaho/musubix-pattern-mcp
  ├── @nahisaho/musubix-wake-sleep
  └── @nahisaho/yata-scale

musubix-neural-search
  ├── @nahisaho/musubix-core
  └── @nahisaho/musubix-dfg

musubix-synthesis
  ├── @nahisaho/musubix-core
  ├── @nahisaho/musubix-library-learner
  ├── @nahisaho/musubix-neural-search
  └── @nahisaho/musubix-lean
```

### 7.2 外部依存

| パッケージ | 用途 |
|-----------|------|
| `typescript` | AST解析・型情報 |
| `@xenova/transformers` | Embeddingモデル |
| `better-sqlite3` | ローカル永続化 |

---

## 8. マイルストーン

| マイルストーン | 期限 | 成果物 |
|--------------|------|--------|
| M1: 要件確定 | 2026-01-08 | 本ドキュメント |
| M2: 設計完了 | 2026-01-09 | 設計ドキュメント |
| M3: ライブラリ学習実装 | 2026-01-12 | musubix-library-learner |
| M4: Neural探索実装 | 2026-01-15 | musubix-neural-search |
| M5: DSL合成実装 | 2026-01-18 | musubix-synthesis |
| M6: 統合テスト完了 | 2026-01-20 | Phase 2 Complete |

---

## 9. リスクと軽減策

| リスク | 影響 | 軽減策 |
|--------|------|--------|
| Embeddingモデルの精度不足 | 探索効率低下 | 複数モデルの評価・選定 |
| ライブラリ肥大化 | メモリ問題 | 自動プルーニング・圧縮 |
| 合成複雑度爆発 | 性能問題 | DSLサイズ制限・タイムアウト |
| Phase 1との統合問題 | 開発遅延 | 早期統合テスト |

---

## 10. 参考文献

1. **DreamCoder**: Growing Generalizable, Interpretable Knowledge with Wake-Sleep Bayesian Program Learning (2021)
2. **DeepCoder**: Learning to Write Programs (2017)
3. **PROSE**: Program Synthesis Framework by Microsoft (2015)
4. **FlashMeta**: A Framework for Inductive Program Synthesis (2015)
5. **E-graphs**: E-Graphs Good: Equality Saturation for Program Optimization (2021)

---

**承認**:

- [ ] 要件レビュー完了
- [ ] ステークホルダー承認
- [ ] 開発開始承認

**次のステップ**: 設計ドキュメント作成 (DES-PHASE2-001.md)
