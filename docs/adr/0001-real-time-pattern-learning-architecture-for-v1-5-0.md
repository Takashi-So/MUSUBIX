# ADR-0001: Real-time Pattern Learning Architecture for v1.5.0

- **Date**: 2026-01-05
- **Status**: accepted
- **Deciders**: Architecture Team
- **Categories**: Learning, Performance

## Context

MUSUBIX v1.4.xではバッチ学習方式を採用しているが、ユーザーのコード変更をリアルタイムで学習する要求がある。

### 要件
- REQ-LEARN-011: ファイル変更時500ms以内に分析
- REQ-LEARN-013: フィードバック収集レイテンシ100ms以内
- REQ-LEARN-014: ストリーム処理1000 events/sec以上

### 検討した選択肢
1. **Polling方式**: 定期的にファイル変更をチェック
2. **fs.watch + EventEmitter**: Node.js標準のファイル監視
3. **chokidar + RxJS**: サードパーティライブラリによるリアクティブストリーム

## Decision

**選択肢 2: fs.watch + EventEmitter** を採用する。

### 理由
- 外部依存なしで実現可能
- Node.js標準APIで十分な性能
- メモリフットプリントが小さい

### アーキテクチャ

```
FileWatcher (fs.watch)
    │
    ▼
StreamProcessor (EventEmitter)
    │
    ├─▼ FeedbackQueue (Non-blocking)
    │
    └─▼ PatternExtractor (AST)
           │
           ▼
    IncrementalUpdater (Delta)
```

### パフォーマンス目標
| メトリクス | 目標 | 測定方法 |
|------------|------|----------|
| 分析レイテンシ | < 500ms | StreamProcessor.getLatency() |
| フィードバック収集 | < 100ms | FeedbackQueue timing |
| スループット | ≥ 1000/sec | EventStream.getThroughput() |

## Consequences

### Positive
- リアルタイム学習によるユーザー体験向上
- 外部依存なしで軽量
- 段階的な実装が可能

### Negative
- fs.watchのクロスプラットフォーム差異への対応が必要
- 大規模プロジェクトでのスケーラビリティ検証が必要

### Risks
- macOS/Linux/Windowsでのfs.watchの挙動差異
- 軽減策: chokidarへのフォールバック機構を用意

## Related Requirements

- REQ-LEARN-010: Real-time pattern learning
- REQ-LEARN-011: 500ms analysis latency
- REQ-LEARN-012: Incremental update
- REQ-LEARN-013: Non-blocking feedback
- REQ-LEARN-014: Stream processing
