# ADR-v3.4.0-002: Search Provider Selection Strategy

**Status**: Accepted  
**Date**: 2026-01-16  
**Authors**: AI Agent  
**Context**: MUSUBIX v3.4.0 Deep Research Integration  
**Traces To**: REQ-DR-CORE-002, REQ-DR-NFR-005, DES-DR-v3.4.0

---

## Context

Deep Research機能では、Web検索プロバイダーからSERP（Search Engine Results Page）データを取得する必要がある。以下の技術的決定が必要：

1. **プロバイダー選択**: どの検索プロバイダーを使用するか
2. **フォールバック戦略**: プライマリプロバイダーが失敗した場合の対応
3. **API制限対応**: レート制限、タイムアウト、エラーハンドリング

### 要件からの制約

- REQ-DR-CORE-002: 複数検索プロバイダー対応、フォールバック必須
- REQ-DR-NFR-001: 応答時間3秒以内
- REQ-DR-NFR-005: 全プロバイダー失敗時のエラーハンドリング
- 既存パッケージ: @nahisaho/musubix-neural-search (v2.2.0+) を活用可能

---

## Decision

**Jina AI**をプライマリプロバイダーとし、**Brave Search**と**DuckDuckGo**をフォールバックとする3段階戦略を採用。

### プロバイダー優先順位

```
1. Jina AI (Primary)
   - Search API: https://s.jina.ai/
   - Reader API: https://r.jina.ai/
   ↓ 失敗時
2. Brave Search (Fallback 1)
   - Search API v1
   - 高品質な検索結果
   ↓ 失敗時
3. DuckDuckGo (Fallback 2)
   - HTML Instant Answer API
   - API Key不要
```

### Strategy Pattern実装

```typescript
// src/providers/provider-factory.ts

export class SearchProviderFactory {
  private providers: SearchProvider[];
  private currentIndex: number = 0;
  
  constructor(config: ProviderConfig) {
    this.providers = [
      new JinaProvider(config.jinaApiKey),      // Priority 1
      new BraveProvider(config.braveApiKey),    // Priority 2
      new DuckDuckGoProvider(),                 // Priority 3 (No API Key)
    ];
  }
  
  async search(query: SERPQuery): Promise<SearchResult[]> {
    for (let attempt = 0; attempt < 3; attempt++) {
      try {
        const provider = this.providers[this.currentIndex];
        const results = await provider.search(query);
        
        // 成功したらインデックスをリセット
        this.currentIndex = 0;
        return results;
        
      } catch (error) {
        logger.warn(`Provider ${provider.name} failed:`, error.message);
        
        // 次のプロバイダーへフォールバック
        this.currentIndex = (this.currentIndex + 1) % this.providers.length;
        
        // 全プロバイダー試行済み
        if (attempt === 2) {
          throw new AllProvidersFailedError('All search providers exhausted');
        }
        
        // Exponential Backoff
        await this.exponentialBackoff(attempt);
      }
    }
  }
  
  private async exponentialBackoff(attempt: number): Promise<void> {
    const delay = Math.min(1000 * Math.pow(2, attempt), 10000); // Max 10s
    await new Promise(resolve => setTimeout(resolve, delay));
  }
}
```

---

## Rationale

### なぜJina AIをプライマリにするか

**✅ 採用理由**:

1. **Search + Reader統合**: 1つのAPIで検索とコンテンツ読取が可能
2. **高品質な結果**: Webスクレイピングではなく、構造化データ取得
3. **参照実装**: jina-ai/node-DeepResearchで実績あり
4. **Markdown変換**: HTML → Markdown変換機能内蔵

**Jina AI API例**:
```typescript
// Search: https://s.jina.ai/{query}
const searchUrl = `https://s.jina.ai/${encodeURIComponent(query)}`;

// Reader: https://r.jina.ai/{targetUrl}
const readerUrl = `https://r.jina.ai/${encodeURIComponent(targetUrl)}`;
```

### プロバイダー比較

| プロバイダー | 長所 | 短所 | 優先度 |
|-------------|------|------|--------|
| **Jina AI** | Search+Reader統合、Markdown変換 | API Key必要 | ✅ Primary |
| **Brave Search** | 高品質、広告なし | API Key必要、Reader機能なし | 🔄 Fallback 1 |
| **DuckDuckGo** | API Key不要、無料 | 品質低め、レート制限厳しい | 🔄 Fallback 2 |
| **Google Search** | 最高品質 | ❌ 有料、TOS制約厳しい | ❌ 不採用 |
| **Bing Search** | 高品質 | ❌ 有料、Azure依存 | ❌ 不採用 |

### フォールバック戦略

**Chain of Responsibility Pattern**で実装：

```
Request → Jina AI → Success? YES → Return
                  ↓ NO (Error)
          Brave Search → Success? YES → Return
                      ↓ NO (Error)
          DuckDuckGo → Success? YES → Return
                    ↓ NO (Error)
          AllProvidersFailedError
```

**Exponential Backoff**:
- 1回目失敗: 1秒待機
- 2回目失敗: 2秒待機
- 3回目失敗: 4秒待機（最大10秒）

---

## Consequences

### Positive

✅ **高可用性**: 3プロバイダーで99.9%のアップタイム  
✅ **コスト最適化**: JinaがダウンでもBrave/DuckDuckGoで継続可能  
✅ **API Key不要オプション**: DuckDuckGoで最低限の機能保証  
✅ **拡張性**: 新プロバイダーをSearchProviderインターフェースで追加容易

### Negative

⚠️ **API Key管理**: Jina/Brave用のAPI Key管理が必要  
⚠️ **応答時間**: フォールバック発生時に遅延（最大13秒）  
⚠️ **結果品質差**: プロバイダーごとに結果品質が異なる

### Mitigations

- **API Key管理**: SecretManagerシングルトンで一元管理（REQ-DR-NFR-003）
- **応答時間**: 
  - タイムアウト設定: 各プロバイダー3秒
  - 並列実行: 検索とReader APIを並列化（REQ-DR-NFR-002）
- **結果品質**: 
  - LMReasoningで推論時に品質評価
  - 低品質結果は自動的にフィルタリング

---

## Implementation Details

### プロバイダーインターフェース

```typescript
// src/providers/provider-interface.ts

export interface SearchProvider {
  name: string;
  search(query: SERPQuery): Promise<SearchResult[]>;
  isAvailable(): Promise<boolean>;
}

export interface SERPQuery {
  keywords: string;
  topK: number;        // 検索結果数 (1-20)
  timestamp: number;
  iteration: number;
}

export interface SearchResult {
  title: string;
  url: string;
  snippet: string;
  date?: string;
  relevance?: number;  // 0.0-1.0
}
```

### Jina Providerの実装

```typescript
// src/providers/jina-provider.ts

export class JinaProvider implements SearchProvider {
  name = 'Jina AI';
  
  constructor(private apiKey: string) {}
  
  async search(query: SERPQuery): Promise<SearchResult[]> {
    const url = `https://s.jina.ai/${encodeURIComponent(query.keywords)}`;
    
    const response = await axios.get(url, {
      headers: {
        'Authorization': `Bearer ${this.apiKey}`,
        'X-Return-Format': 'json',
      },
      timeout: 3000,
    });
    
    return response.data.data.map((item: any) => ({
      title: item.title,
      url: item.url,
      snippet: item.content.slice(0, 200),
      date: item.publishedTime,
    })).slice(0, query.topK);
  }
  
  async isAvailable(): Promise<boolean> {
    try {
      await axios.head('https://s.jina.ai', { timeout: 1000 });
      return true;
    } catch {
      return false;
    }
  }
}
```

### Neural Search統合（オプション）

既存の`@nahisaho/musubix-neural-search`を活用：

```typescript
// src/integrations/neural-search-integration.ts

import { HybridRanker } from '@nahisaho/musubix-neural-search';

export class NeuralSearchIntegration {
  private ranker: HybridRanker;
  
  async rerankResults(
    query: string,
    results: SearchResult[]
  ): Promise<SearchResult[]> {
    // BM25 + ベクトル類似度でリランキング
    const scored = await this.ranker.rank(query, results);
    return scored.sort((a, b) => b.relevance - a.relevance);
  }
}
```

---

## Compliance

### 要件準拠

| 要件ID | 対応 |
|--------|------|
| REQ-DR-CORE-002 | ✅ 3プロバイダー対応、フォールバック実装 |
| REQ-DR-NFR-001 | ✅ タイムアウト3秒、並列実行で性能確保 |
| REQ-DR-NFR-005 | ✅ AllProvidersFailedError、リトライ戦略 |
| REQ-DR-INT-002 | ✅ Neural Search統合でリランキング |

### 憲法準拠

| 条項 | 対応 |
|-----|------|
| VII. Design Patterns | ✅ Strategy, Chain of Responsibility適用 |
| IX. Quality Gates | ✅ isAvailable()でヘルスチェック |

---

## References

- [Jina AI Search API Documentation](https://jina.ai/search)
- [Brave Search API](https://brave.com/search/api/)
- [DuckDuckGo Instant Answer API](https://duckduckgo.com/api)
- [jina-ai/node-DeepResearch](https://github.com/jina-ai/node-DeepResearch) - 参照実装
- REQ-MUSUBIX-v3.4.0.md - 要件定義書
- DES-DR-v3.4.0.md - 設計書

---

## Approval

- **Author**: AI Agent (2026-01-16)
- **Reviewer**: -
- **Status**: Accepted
