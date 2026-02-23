# ADR-0003: OWL 2 RL Implementation Strategy for advanced inference

- **Date**: 2026-01-05
- **Status**: accepted
- **Deciders**: Architecture Team
- **Categories**: Ontology, Inference

## Context

MUSUBIX v1.4.xではN3.jsによる基本的なRDF処理を実装済み。OWL 2 RLプロファイルの推論機能を追加する必要がある。

### 要件
- REQ-ONTO-010: OWL 2 RLプロファイル対応
- REQ-ONTO-011: 200ms以内の推論（10,000トリプルまで）
- REQ-ONTO-014: Datalogルール統合（最大100ルール）

### 検討した選択肢
1. **完全なOWL 2推論器（HermiT等）**: Javaベース、高機能だが重い
2. **N3.js + カスタムルール**: 既存実装を拡張
3. **RDFox / Stardog**: 商用推論エンジン

## Decision

**選択肢 2: N3.js + カスタムOWL 2 RLルール** を採用する。

### 理由
- 既存のN3Store実装を活用可能
- 軽量でNode.js環境に最適
- 必要なルールセットのみ実装（段階的拡張）

### 実装するOWL 2 RLルール（Phase 1）

| ルールID | 説明 | 優先度 |
|----------|------|--------|
| prp-dom | rdfs:domain推論 | P0 |
| prp-rng | rdfs:range推論 | P0 |
| prp-spo1 | rdfs:subPropertyOf推論 | P0 |
| cax-sco | rdfs:subClassOf推論 | P0 |
| prp-trp | owl:TransitiveProperty | P1 |
| prp-symp | owl:SymmetricProperty | P1 |
| prp-inv1/2 | owl:inverseOf | P1 |

### アーキテクチャ

```
QueryEngine
    │
    ▼
RuleEngine (OWL 2 RL)
    │
    ├── BuiltInRules (prp-*, cax-*)
    │
    └── DatalogIntegrator (最大100ルール)
           │
           ▼
    InferenceExecutor (200ms SLA)
           │
           ▼
    ExplanationGenerator
```

### パフォーマンス目標
| グラフサイズ | 目標レイテンシ |
|-------------|---------------|
| 1,000 triples | < 50ms |
| 5,000 triples | < 100ms |
| 10,000 triples | < 200ms |

## Consequences

### Positive
- 既存実装との統合が容易
- 軽量で高速
- 段階的な機能追加が可能

### Negative
- OWL 2 RL全機能のサポートには時間がかかる
- 複雑な推論には限界あり

### Risks
- 10,000トリプル超での性能劣化
- 軽減策: インデックス最適化、マテリアライズドビュー

## Related Requirements

- REQ-ONTO-010: OWL 2 RL support
- REQ-ONTO-011: 200ms inference latency
- REQ-ONTO-012: Progress feedback
- REQ-ONTO-013: Explanation generation
- REQ-ONTO-014: Datalog integration
