# MUSUBIX v1.5.0 Test Plan

**Version**: 1.5.0
**Status**: Draft
**Created**: 2025-01-05
**Based On**: REQ-v1.5.0.md, DES-v1.5.0.md

---

## 1. Overview

### 1.1 目的
v1.5.0の全要件（24件）に対するテスト計画を定義し、品質ゲートの達成を保証する。

### 1.2 スコープ
| カテゴリ | 要件数 | テストケース数 |
|----------|--------|---------------|
| Real-time Learning | 5 | 15 |
| Pattern Sharing | 5 | 12 |
| Advanced Inference | 5 | 15 |
| Interactive CLI | 4 | 10 |
| Performance | 5 | 12 |
| **合計** | **24** | **64** |

### 1.3 品質目標
| メトリクス | 目標 |
|-----------|------|
| テストカバレッジ（P0機能） | ≥ 80% |
| テストカバレッジ（全体） | ≥ 40% |
| テスト合格率 | 100% |
| 性能テスト合格率 | 100% |

---

## 2. Feature 1: Real-time Pattern Learning

### 2.1 TST-LEARN-010: Real-time Learning基盤

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-LEARN-010-01 | FileWatcher初期化 | Unit | REQ-LEARN-010 |
| TST-LEARN-010-02 | ファイル変更検出 | Unit | REQ-LEARN-010 |
| TST-LEARN-010-03 | 複数ファイル監視 | Integration | REQ-LEARN-010 |

```typescript
// TST-LEARN-010-01
describe('FileWatcher', () => {
  it('should initialize with target paths', async () => {
    const watcher = new FileWatcher();
    await watcher.watch(['/src']);
    expect(watcher.isWatching()).toBe(true);
  });
});
```

### 2.2 TST-LEARN-011: 500ms分析レイテンシ

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-LEARN-011-01 | 分析レイテンシ < 500ms | Performance | REQ-LEARN-011 |
| TST-LEARN-011-02 | 小規模ファイル（< 1KB） | Performance | REQ-LEARN-011 |
| TST-LEARN-011-03 | 中規模ファイル（1-10KB） | Performance | REQ-LEARN-011 |
| TST-LEARN-011-04 | 大規模ファイル（> 10KB） | Performance | REQ-LEARN-011 |

```typescript
// TST-LEARN-011-01
describe('StreamProcessor', () => {
  it('should analyze changes within 500ms', async () => {
    const processor = new StreamProcessor();
    const event = createFileChangeEvent('/src/test.ts');
    
    const start = performance.now();
    await processor.process(event);
    const latency = performance.now() - start;
    
    expect(latency).toBeLessThan(500);
  });
});
```

### 2.3 TST-LEARN-012: 差分パターン更新

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-LEARN-012-01 | 新規パターン検出 | Unit | REQ-LEARN-012 |
| TST-LEARN-012-02 | インクリメンタル更新 | Unit | REQ-LEARN-012 |
| TST-LEARN-012-03 | 重複パターン検出 | Unit | REQ-LEARN-012 |

### 2.4 TST-LEARN-013: 非同期フィードバック

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-LEARN-013-01 | フィードバック収集 < 100ms | Performance | REQ-LEARN-013 |
| TST-LEARN-013-02 | 非ブロッキング動作 | Unit | REQ-LEARN-013 |
| TST-LEARN-013-03 | キュー容量管理 | Unit | REQ-LEARN-013 |

```typescript
// TST-LEARN-013-01
describe('FeedbackQueue', () => {
  it('should enqueue feedback within 100ms', () => {
    const queue = new FeedbackQueue();
    const feedback = createFeedback('accept', 'PAT-001');
    
    const start = performance.now();
    queue.enqueue(feedback);
    const latency = performance.now() - start;
    
    expect(latency).toBeLessThan(100);
  });
});
```

### 2.5 TST-LEARN-014: イベントストリーム

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-LEARN-014-01 | スループット ≥ 1000/sec | Performance | REQ-LEARN-014 |
| TST-LEARN-014-02 | ストリーム購読 | Unit | REQ-LEARN-014 |
| TST-LEARN-014-03 | バックプレッシャー | Integration | REQ-LEARN-014 |

```typescript
// TST-LEARN-014-01
describe('EventStream', () => {
  it('should process at least 1000 events per second', async () => {
    const stream = new EventStream();
    const events = generateEvents(2000);
    
    const start = performance.now();
    for (const event of events) {
      stream.emit(event);
    }
    const elapsed = performance.now() - start;
    
    const throughput = (2000 / elapsed) * 1000;
    expect(throughput).toBeGreaterThanOrEqual(1000);
  });
});
```

---

## 3. Feature 2: Pattern Sharing

### 3.1 TST-SHARE-001: JSONエクスポート

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-SHARE-001-01 | JSON形式出力 | Unit | REQ-SHARE-001 |
| TST-SHARE-001-02 | スキーマ準拠 | Unit | REQ-SHARE-001 |
| TST-SHARE-001-03 | チェックサム生成 | Unit | REQ-SHARE-001 |

### 3.2 TST-SHARE-002: パターンインポート

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-SHARE-002-01 | 有効なJSONインポート | Unit | REQ-SHARE-002 |
| TST-SHARE-002-02 | 無効なJSONエラー | Unit | REQ-SHARE-002 |
| TST-SHARE-002-03 | バージョン互換性 | Integration | REQ-SHARE-002 |

### 3.3 TST-SHARE-003: オントロジー検証

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-SHARE-003-01 | 有効なパターン検証 | Unit | REQ-SHARE-003 |
| TST-SHARE-003-02 | 無効なパターン拒否 | Unit | REQ-SHARE-003 |

### 3.4 TST-SHARE-004: プライバシー保護

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-SHARE-004-01 | 機密データ除去 | Unit | REQ-SHARE-004 |
| TST-SHARE-004-02 | 作者情報マスキング | Unit | REQ-SHARE-004 |

```typescript
// TST-SHARE-004-01
describe('DataSanitizer', () => {
  it('should remove sensitive data from patterns', () => {
    const pattern = createPatternWithSensitiveData();
    const sanitized = DataSanitizer.sanitize(pattern);
    
    expect(sanitized.metadata.author).toBe('[REDACTED]');
    expect(sanitized.template).not.toContain('password');
    expect(sanitized.template).not.toContain('secret');
  });
});
```

### 3.5 TST-SHARE-005: 競合解決

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-SHARE-005-01 | keep-local戦略 | Unit | REQ-SHARE-005 |
| TST-SHARE-005-02 | keep-remote戦略 | Unit | REQ-SHARE-005 |
| TST-SHARE-005-03 | merge戦略 | Unit | REQ-SHARE-005 |

---

## 4. Feature 3: Advanced Inference

### 4.1 TST-ONTO-010: OWL 2 RLサポート

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-ONTO-010-01 | rdfs:subClassOf推論 | Unit | REQ-ONTO-010 |
| TST-ONTO-010-02 | rdfs:domain推論 | Unit | REQ-ONTO-010 |
| TST-ONTO-010-03 | owl:TransitiveProperty | Unit | REQ-ONTO-010 |
| TST-ONTO-010-04 | owl:inverseOf | Unit | REQ-ONTO-010 |

### 4.2 TST-ONTO-011: 推論レイテンシ

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-ONTO-011-01 | 推論 < 200ms (10kトリプル) | Performance | REQ-ONTO-011 |
| TST-ONTO-011-02 | 推論 < 50ms (1kトリプル) | Performance | REQ-ONTO-011 |
| TST-ONTO-011-03 | 推論 < 100ms (5kトリプル) | Performance | REQ-ONTO-011 |

```typescript
// TST-ONTO-011-01
describe('InferenceExecutor', () => {
  it('should complete inference within 200ms for 10k triples', async () => {
    const executor = new InferenceExecutor();
    const graph = createKnowledgeGraph(10000);
    const query = createQuery('SELECT ?x WHERE { ?x a sdd:Pattern }');
    
    const start = performance.now();
    await executor.execute(query, graph);
    const latency = performance.now() - start;
    
    expect(latency).toBeLessThan(200);
  });
});
```

### 4.3 TST-ONTO-012: 進捗フィードバック

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-ONTO-012-01 | 進捗コールバック呼び出し | Unit | REQ-ONTO-012 |
| TST-ONTO-012-02 | 500ms間隔の遵守 | Unit | REQ-ONTO-012 |

### 4.4 TST-ONTO-013: 説明生成

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-ONTO-013-01 | 人間可読説明 | Unit | REQ-ONTO-013 |
| TST-ONTO-013-02 | 推論チェーン生成 | Unit | REQ-ONTO-013 |

### 4.5 TST-ONTO-014: Datalog統合

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-ONTO-014-01 | ルール読み込み (最大100) | Unit | REQ-ONTO-014 |
| TST-ONTO-014-02 | ルール超過エラー | Unit | REQ-ONTO-014 |
| TST-ONTO-014-03 | OWLルールとの統合 | Integration | REQ-ONTO-014 |

---

## 5. Feature 4: Interactive CLI Mode

### 5.1 TST-CLI-010: REPLモード

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-CLI-010-01 | REPL起動 < 1秒 | Performance | REQ-CLI-010 |
| TST-CLI-010-02 | --interactiveフラグ | Unit | REQ-CLI-010 |
| TST-CLI-010-03 | REPL終了 | Unit | REQ-CLI-010 |

```typescript
// TST-CLI-010-01
describe('REPLController', () => {
  it('should start REPL within 1 second', async () => {
    const repl = new REPLController();
    
    const start = performance.now();
    await repl.start();
    const latency = performance.now() - start;
    
    expect(latency).toBeLessThan(1000);
    expect(repl.isRunning()).toBe(true);
    
    repl.stop();
  });
});
```

### 5.2 TST-CLI-011: オートコンプリート

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-CLI-011-01 | 補完応答 < 50ms | Performance | REQ-CLI-011 |
| TST-CLI-011-02 | コマンド補完 | Unit | REQ-CLI-011 |

### 5.3 TST-CLI-012: コマンド履歴

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-CLI-012-01 | 履歴保存 (1000件) | Unit | REQ-CLI-012 |
| TST-CLI-012-02 | 履歴検索 | Unit | REQ-CLI-012 |

### 5.4 TST-CLI-013: Tab補完

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-CLI-013-01 | Tab補完 < 100ms | Performance | REQ-CLI-013 |
| TST-CLI-013-02 | 補完候補表示 | Unit | REQ-CLI-013 |

---

## 6. Feature 5: Performance Optimization

### 6.1 TST-PERF-001: 遅延読み込み

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-PERF-001-01 | 未使用時メモリ節約 | Performance | REQ-PERF-001 |
| TST-PERF-001-02 | 必要時読み込み | Unit | REQ-PERF-001 |

### 6.2 TST-PERF-002: キャッシュ

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-PERF-002-01 | キャッシュヒット | Unit | REQ-PERF-002 |
| TST-PERF-002-02 | キャッシュミス | Unit | REQ-PERF-002 |

### 6.3 TST-PERF-003: 並列処理

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-PERF-003-01 | 4+ワーカー (10k+ファイル) | Performance | REQ-PERF-003 |
| TST-PERF-003-02 | 並列処理高速化 | Performance | REQ-PERF-003 |

### 6.4 TST-PERF-004: メモリ制限

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-PERF-004-01 | メモリ < 500MB | Performance | REQ-PERF-004 |
| TST-PERF-004-02 | メモリ超過防止 | Unit | REQ-PERF-004 |

```typescript
// TST-PERF-004-01
describe('CacheManager', () => {
  it('should not exceed 500MB memory usage', () => {
    const cache = new CacheManager();
    
    // Fill cache with data
    for (let i = 0; i < 1000; i++) {
      cache.set(`key-${i}`, generateLargeData());
    }
    
    const memoryUsage = cache.getMemoryUsage();
    expect(memoryUsage).toBeLessThan(500 * 1024 * 1024); // 500MB
  });
});
```

### 6.5 TST-PERF-005: 非同期リフレッシュ

| テストID | テスト名 | 種別 | 要件 |
|----------|---------|------|------|
| TST-PERF-005-01 | 5分TTL動作 | Unit | REQ-PERF-005 |
| TST-PERF-005-02 | 非同期リフレッシュ | Unit | REQ-PERF-005 |

---

## 7. テスト実行計画

### 7.1 Phase 1: Foundation (Week 1-2)

| テスト種別 | 対象 | 実行頻度 |
|-----------|------|----------|
| Unit | インターフェース定義確認 | PR毎 |
| Lint | コード品質 | PR毎 |

### 7.2 Phase 2: Core Features (Week 3-4)

| テスト種別 | 対象 | 実行頻度 |
|-----------|------|----------|
| Unit | P0機能（Learning） | PR毎 |
| Performance | レイテンシ・スループット | Daily |
| Integration | コンポーネント連携 | Daily |

### 7.3 Phase 3: Integration (Week 5-6)

| テスト種別 | 対象 | 実行頻度 |
|-----------|------|----------|
| Unit | P1機能（Sharing, Inference） | PR毎 |
| E2E | CLI操作フロー | Daily |
| Regression | v1.4.x互換性 | Weekly |

### 7.4 Phase 4: Stabilization (Week 7-8)

| テスト種別 | 対象 | 実行頻度 |
|-----------|------|----------|
| Full Suite | 全テスト | PR毎 |
| Performance | 全NFR | Daily |
| Security | npm audit | Daily |
| Stress | 負荷テスト | Weekly |

---

## 8. テスト環境

### 8.1 必要環境

| 項目 | 要件 |
|------|------|
| Node.js | >= 20.0.0 |
| npm | >= 10.0.0 |
| OS | Linux, macOS, Windows |
| メモリ | >= 4GB |

### 8.2 テストフレームワーク

| ツール | 用途 |
|--------|------|
| Vitest | ユニットテスト、統合テスト |
| @vitest/coverage-v8 | カバレッジ測定 |
| Benchmark.js | パフォーマンステスト |
| memwatch-next | メモリ監視 |

### 8.3 CI/CD

```yaml
# .github/workflows/test.yml
name: Test v1.5.0
on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: '20'
      - run: npm ci
      - run: npm run build
      - run: npm run test:coverage
      - run: npm run test:performance
```

---

## 9. トレーサビリティマトリクス

| 要件ID | テストID | ステータス |
|--------|----------|-----------|
| REQ-LEARN-010 | TST-LEARN-010-01〜03 | ⏳ |
| REQ-LEARN-011 | TST-LEARN-011-01〜04 | ⏳ |
| REQ-LEARN-012 | TST-LEARN-012-01〜03 | ⏳ |
| REQ-LEARN-013 | TST-LEARN-013-01〜03 | ⏳ |
| REQ-LEARN-014 | TST-LEARN-014-01〜03 | ⏳ |
| REQ-SHARE-001 | TST-SHARE-001-01〜03 | ⏳ |
| REQ-SHARE-002 | TST-SHARE-002-01〜03 | ⏳ |
| REQ-SHARE-003 | TST-SHARE-003-01〜02 | ⏳ |
| REQ-SHARE-004 | TST-SHARE-004-01〜02 | ⏳ |
| REQ-SHARE-005 | TST-SHARE-005-01〜03 | ⏳ |
| REQ-ONTO-010 | TST-ONTO-010-01〜04 | ⏳ |
| REQ-ONTO-011 | TST-ONTO-011-01〜03 | ⏳ |
| REQ-ONTO-012 | TST-ONTO-012-01〜02 | ⏳ |
| REQ-ONTO-013 | TST-ONTO-013-01〜02 | ⏳ |
| REQ-ONTO-014 | TST-ONTO-014-01〜03 | ⏳ |
| REQ-CLI-010 | TST-CLI-010-01〜03 | ⏳ |
| REQ-CLI-011 | TST-CLI-011-01〜02 | ⏳ |
| REQ-CLI-012 | TST-CLI-012-01〜02 | ⏳ |
| REQ-CLI-013 | TST-CLI-013-01〜02 | ⏳ |
| REQ-PERF-001 | TST-PERF-001-01〜02 | ⏳ |
| REQ-PERF-002 | TST-PERF-002-01〜02 | ⏳ |
| REQ-PERF-003 | TST-PERF-003-01〜02 | ⏳ |
| REQ-PERF-004 | TST-PERF-004-01〜02 | ⏳ |
| REQ-PERF-005 | TST-PERF-005-01〜02 | ⏳ |

---

## 10. 承認

| 役割 | 名前 | 日付 | 承認 |
|------|------|------|------|
| Test Lead | - | - | ⏳ |
| Dev Lead | - | - | ⏳ |
| PM | - | - | ⏳ |

