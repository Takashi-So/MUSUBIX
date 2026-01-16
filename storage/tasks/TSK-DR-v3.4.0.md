# MUSUBIX v3.4.0 タスク分解書
# Deep Research Integration - Task Decomposition Document

**文書ID**: TSK-DR-v3.4.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.1  
**作成日**: 2026-01-16  
**更新日**: 2026-01-16  
**承認日**: 2026-01-16  
**ステータス**: Approved  
**参照文書**: 
- REQ-MUSUBIX-v3.4.0.md (要件定義書)
- DES-DR-v3.4.0.md (設計書)
- ADR-v3.4.0-001〜003 (Architecture Decision Records)

---

## 1. 文書概要

### 1.1 目的

本文書は、MUSUBIX v3.4.0 Deep Research機能の実装タスクを定義する。設計書（DES-DR-v3.4.0）で定義されたアーキテクチャを実装可能な単位に分解し、工数見積もり、依存関係、実装順序を明確化する。

### 1.2 タスク分類

| カテゴリ | タスク数 | 総工数見積 | 優先度 |
|---------|---------|-----------|--------|
| **Core Engine** | 6タスク | 19時間 | P0（必須） |
| **Providers** | 4タスク | 12時間 | P0（必須） |
| **Reasoning** | 3タスク | 10時間 | P0（必須） |
| **Security** | 3タスク | 8時間 | P0（必須） |
| **Performance** | 3タスク | 8時間 | P1（重要） |
| **Integration** | 7タスク | 18時間 | P1（重要） |
| **Testing** | 4タスク | 13時間 | P0（必須） |
| **Documentation** | 2タスク | 4時間 | P2（任意） |
| **合計** | **32タスク** | **92時間** | - |

### 1.3 実装フェーズ

```
Phase 4-1: Foundation（基盤）
  ├─ TSK-DR-001〜005: Core Engine
  ├─ TSK-DR-006〜009: Providers
  ├─ TSK-DR-010〜012: Reasoning
  └─ TSK-DR-028: Mock実装（テスト駆動開発のため）
  ↓ 依存: Phase 4-1完了
Phase 4-2: Enhancement（強化）
  ├─ TSK-DR-013〜015: Security
  ├─ TSK-DR-016〜018: Performance
  └─ TSK-DR-019〜025: Integration
  ↓ 依存: Phase 4-2完了
Phase 4-3: Quality Assurance（品質保証）
  ├─ TSK-DR-026〜027,029〜030: Testing
  └─ TSK-DR-031〜032: Documentation
```

---

## 2. Core Engine（基盤エンジン）

### TSK-DR-001: ResearchEngineクラス実装

**優先度**: P0  
**工数**: 4時間  
**担当者**: -  
**依存**: なし  
**トレーサビリティ**: REQ-DR-CORE-001, DES-DR-v3.4.0, ADR-v3.4.0-001

#### タスク詳細

Template Method Patternに基づくResearchEngineクラスを実装。

**実装ファイル**: `packages/deep-research/src/engine/research-engine.ts`

**実装内容**:
```typescript
export class ResearchEngine {
  private knowledge: KnowledgeBase;
  private iteration: number = 0;
  private tokenTracker: TokenTracker;
  private logger: TrajectoryLogger;
  
  constructor(config: ResearchConfig) { /* ... */ }
  
  // Template Method（メインフロー）
  async research(): Promise<ResearchReport> {
    this.initialize();
    
    while (!this.shouldStop()) {
      const questions = await this.generateQuestions();
      const searchResults = await this.search(questions);
      const contents = await this.read(searchResults);
      const knowledgeItems = await this.reason(contents);
      
      this.knowledge.addAll(knowledgeItems);
      this.iteration++;
      this.logger.logIteration({ /* ... */ });
      
      if (await this.isAnswerDefinitive()) {
        break;
      }
    }
    
    return this.generateReport();
  }
  
  // フックメソッド（実装対象）
  protected async generateQuestions(): Promise<ReflectiveQuestion[]> { /* TSK-DR-010 */ }
  protected async search(questions: ReflectiveQuestion[]): Promise<SearchResult[]> { /* TSK-DR-006 */ }
  protected async read(results: SearchResult[]): Promise<WebContent[]> { /* TSK-DR-007 */ }
  protected async reason(contents: WebContent[]): Promise<KnowledgeItem[]> { /* TSK-DR-011 */ }
  
  // ヘルパーメソッド
  private shouldStop(): boolean { /* ... */ }
  private async isAnswerDefinitive(): Promise<boolean> { /* ... */ }
  private initialize(): void { /* ... */ }
  private async generateReport(): Promise<ResearchReport> { /* TSK-DR-005 */ }
}
```

**テストケース**:
- ✅ research()が最大10イテレーションで停止
- ✅ トークン予算超過時に早期停止
- ✅ 確定回答が得られた時点で停止

**完了条件**:
- ResearchEngineクラスがビルド成功
- 3つのテストケースが合格
- DES-DR-v3.4.0のTemplate Method設計に準拠

---

### TSK-DR-002: KnowledgeBaseクラス実装

**優先度**: P0  
**工数**: 3時間  
**担当者**: -  
**依存**: なし  
**トレーサビリティ**: REQ-DR-CORE-008, DES-DR-v3.4.0

#### タスク詳細

調査中の知識アイテムを管理するKnowledgeBaseクラスを実装。

**実装ファイル**: `packages/deep-research/src/knowledge/knowledge-base.ts`

**実装内容**:
```typescript
export class KnowledgeBase {
  private items: Map<string, KnowledgeItem> = new Map();
  private iterationIndex: Map<number, string[]> = new Map();
  
  add(item: KnowledgeItem): void {
    const id = this.generateId();
    item.id = id;
    
    this.items.set(id, item);
    
    // Iteration indexing
    const iterationItems = this.iterationIndex.get(item.iteration) || [];
    iterationItems.push(id);
    this.iterationIndex.set(item.iteration, iterationItems);
  }
  
  addAll(items: KnowledgeItem[]): void {
    for (const item of items) {
      this.add(item);
    }
  }
  
  getFindings(): KnowledgeItem[] {
    return Array.from(this.items.values())
      .filter(item => item.type === 'fact')
      .sort((a, b) => b.relevance - a.relevance);
  }
  
  getByIteration(iteration: number): KnowledgeItem[] {
    const ids = this.iterationIndex.get(iteration) || [];
    return ids.map(id => this.items.get(id)!);
  }
  
  size(): number {
    return this.items.size;
  }
  
  getSummary(): string {
    return Array.from(this.items.values())
      .slice(0, 10)
      .map(item => `- ${item.content}`)
      .join('\n');
  }
  
  private generateId(): string {
    return `knowledge-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
  }
}
```

**テストケース**:
- ✅ add()で知識アイテムを追加
- ✅ getByIteration()でイテレーション別取得
- ✅ getFindings()で関連度順ソート

**完了条件**:
- KnowledgeBaseクラスがビルド成功
- 3つのテストケースが合格
- Repository Patternに準拠

---

### TSK-DR-003: TokenTrackerクラス実装

**優先度**: P0  
**工数**: 2時間  
**担当者**: -  
**依存**: なし  
**トレーサビリティ**: REQ-DR-CORE-006, DES-DR-v3.4.0

#### タスク詳細

API利用トークンの追跡・予算管理を行うTokenTrackerクラスを実装。

**実装ファイル**: `packages/deep-research/src/utils/token-tracker.ts`

**実装内容**:
```typescript
export class TokenTracker {
  private usages: TokenUsage[] = [];
  private budget: number;
  private warningEmitted = false;
  
  constructor(budget: number) {
    this.budget = budget;
  }
  
  trackUsage(operation: string, tokens: number): void {
    this.usages.push({
      operation,
      tokens,
      timestamp: Date.now(),
    });
    
    // 80%警告
    if (this.getUsed() >= this.budget * 0.8 && !this.warningEmitted) {
      console.warn(`⚠️  Token budget 80% consumed (${this.getUsed()}/${this.budget})`);
      this.warningEmitted = true;
    }
    
    // 100%エラー
    if (this.isExceeded()) {
      throw new TokenBudgetExceededError(this.getUsed(), this.budget);
    }
  }
  
  getUsed(): number {
    return this.usages.reduce((sum, u) => sum + u.tokens, 0);
  }
  
  getRemaining(): number {
    return Math.max(0, this.budget - this.getUsed());
  }
  
  isExceeded(): boolean {
    return this.getUsed() >= this.budget;
  }
  
  getBreakdown(): Record<string, number> {
    const breakdown: Record<string, number> = {};
    
    for (const usage of this.usages) {
      breakdown[usage.operation] = (breakdown[usage.operation] || 0) + usage.tokens;
    }
    
    return breakdown;
  }
}
```

**テストケース**:
- ✅ trackUsage()でトークン使用量を記録
- ✅ 80%消費時に警告が出力される
- ✅ 100%超過時にTokenBudgetExceededErrorが発生

**完了条件**:
- TokenTrackerクラスがビルド成功
- 3つのテストケースが合格

---

### TSK-DR-004: TrajectoryLoggerクラス実装

**優先度**: P0  
**工数**: 3時間  
**担当者**: -  
**依存**: なし  
**トレーサビリティ**: REQ-DR-CORE-010, DES-DR-v3.4.0

#### タスク詳細

イテレーション軌跡をログ記録するTrajectoryLoggerクラスを実装。

**実装ファイル**: `packages/deep-research/src/utils/trajectory-logger.ts`

**実装内容**:
```typescript
export class TrajectoryLogger {
  private logs: IterationLog[] = [];
  
  logIteration(log: IterationLog): void {
    this.logs.push(log);
    
    // コンソール出力
    console.log(`[Iteration ${log.iteration}] ${log.action.type} - +${log.knowledgeGained} knowledge items`);
  }
  
  getLogs(): IterationLog[] {
    return this.logs;
  }
  
  export(format: 'json' | 'parquet'): string | Buffer {
    if (format === 'json') {
      return JSON.stringify(this.logs, null, 2);
    } else if (format === 'parquet') {
      // TODO: Parquet変換（Neural Search統合時に実装）
      throw new Error('Parquet export not implemented yet');
    }
    
    throw new Error(`Unknown format: ${format}`);
  }
}
```

**テストケース**:
- ✅ logIteration()でログ記録
- ✅ getLogs()で全ログ取得
- ✅ export('json')でJSON出力

**完了条件**:
- TrajectoryLoggerクラスがビルド成功
- 3つのテストケースが合格

---

### TSK-DR-005: ReportGeneratorクラス実装

**優先度**: P0  
**工数**: 4時間  
**担当者**: -  
**依存**: TSK-DR-002（KnowledgeBase）  
**トレーサビリティ**: REQ-DR-CORE-005, DES-DR-v3.4.0

#### タスク詳細

Markdown/JSON形式のレポートを生成するReportGeneratorクラスを実装。

**実装ファイル**: 
- `packages/deep-research/src/reporters/report-generator.ts`
- `packages/deep-research/src/reporters/markdown-formatter.ts`

**実装内容**:
```typescript
// report-generator.ts
export class ReportGenerator {
  constructor(
    private markdownFormatter: MarkdownFormatter,
    private jsonExporter: JSONExporter
  ) {}
  
  async generate(
    query: string,
    knowledge: KnowledgeBase,
    trajectory: IterationLog[],
    metadata: ResearchMetadata
  ): Promise<ResearchReport> {
    const summary = this.generateSummary(query, knowledge);
    const findings = knowledge.getFindings().map(f => ({
      statement: f.content,
      citations: f.sources,
      confidence: f.relevance,
    }));
    
    const options = this.extractTechnicalOptions(knowledge);
    const recommendations = this.generateRecommendations(knowledge);
    const references = this.collectReferences(knowledge);
    
    return {
      query,
      summary,
      findings,
      options,
      recommendations,
      references,
      metadata: {
        iterations: trajectory.length,
        tokensUsed: metadata.totalTokens,
        duration: metadata.durationMs,
        confidence: this.calculateOverallConfidence(findings),
      },
    };
  }
  
  toMarkdown(report: ResearchReport): string {
    return this.markdownFormatter.format(report);
  }
  
  toJSON(report: ResearchReport): string {
    return this.jsonExporter.export(report);
  }
  
  private generateSummary(query: string, knowledge: KnowledgeBase): string { /* ... */ }
  private extractTechnicalOptions(knowledge: KnowledgeBase): TechnicalOption[] { /* ... */ }
  private generateRecommendations(knowledge: KnowledgeBase): Recommendation[] { /* ... */ }
  private collectReferences(knowledge: KnowledgeBase): Reference[] { /* ... */ }
  private calculateOverallConfidence(findings: Finding[]): number { /* ... */ }
}
```

**テストケース**:
- ✅ generate()でResearchReportを生成
- ✅ toMarkdown()でMarkdown出力
- ✅ toJSON()でJSON出力

**完了条件**:
- ReportGeneratorクラスがビルド成功
- 3つのテストケースが合格
- サンプルレポートがREQ-DR-CORE-005の仕様に準拠

---

## 3. Providers（検索プロバイダー）

### TSK-DR-006: SearchProviderFactoryクラス実装

**優先度**: P0  
**工数**: 4時間  
**担当者**: -  
**依存**: なし  
**トレーサビリティ**: REQ-DR-CORE-002, DES-DR-v3.4.0, ADR-v3.4.0-002

#### タスク詳細

検索プロバイダーの選択・フォールバックを行うSearchProviderFactoryクラスを実装。

**実装ファイル**: `packages/deep-research/src/providers/provider-factory.ts`

**実装内容**:
```typescript
export class SearchProviderFactory {
  private providers: SearchProvider[];
  private currentIndex: number = 0;
  
  constructor(config: ProviderConfig) {
    this.providers = [
      new JinaProvider(config.jinaApiKey),
      new BraveProvider(config.braveApiKey),
      new DuckDuckGoProvider(),
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
        logger.warn(`Provider ${this.currentIndex} failed:`, error);
        this.currentIndex = (this.currentIndex + 1) % this.providers.length;
        
        if (attempt === 2) {
          throw new AllProvidersFailedError('All search providers failed');
        }
        
        await this.exponentialBackoff(attempt);
      }
    }
  }
  
  private async exponentialBackoff(attempt: number): Promise<void> {
    const delay = Math.min(1000 * Math.pow(2, attempt), 10000);
    await new Promise(resolve => setTimeout(resolve, delay));
  }
}
```

**テストケース**:
- ✅ プライマリプロバイダーで検索成功
- ✅ プライマリ失敗時にフォールバック
- ✅ 全プロバイダー失敗時にAllProvidersFailedError

**完了条件**:
- SearchProviderFactoryクラスがビルド成功
- 3つのテストケースが合格
- ADR-v3.4.0-002の設計に準拠

---

### TSK-DR-007: JinaProviderクラス実装

**優先度**: P0  
**工数**: 3時間  
**担当者**: -  
**依存**: TSK-DR-006（SearchProviderFactory）  
**トレーサビリティ**: REQ-DR-CORE-002, REQ-DR-CORE-003, ADR-v3.4.0-002

#### タスク詳細

Jina AI Search/Reader APIを統合するJinaProviderクラスを実装。

**実装ファイル**: `packages/deep-research/src/providers/jina-provider.ts`

**実装内容**:
```typescript
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
  
  async read(url: string): Promise<WebContent> {
    const readerUrl = `https://r.jina.ai/${encodeURIComponent(url)}`;
    
    const response = await axios.get(readerUrl, {
      headers: {
        'Authorization': `Bearer ${this.apiKey}`,
        'X-Return-Format': 'markdown',
      },
      timeout: 5000,
    });
    
    return {
      url,
      title: response.data.title,
      content: response.data.content,
      extractedFacts: [], // TODO: LM推論で抽出
    };
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

**テストケース**:
- ✅ search()でSERP結果を取得（Mock）
- ✅ read()でWebコンテンツを取得（Mock）
- ✅ isAvailable()でヘルスチェック

**完了条件**:
- JinaProviderクラスがビルド成功
- 3つのテストケースが合格（Mock HTTP使用）

---

### TSK-DR-008: BraveProviderクラス実装

**優先度**: P1  
**工数**: 3時間  
**担当者**: -  
**依存**: TSK-DR-006（SearchProviderFactory）  
**トレーサビリティ**: REQ-DR-CORE-002, ADR-v3.4.0-002

#### タスク詳細

Brave Search APIを統合するBraveProviderクラスを実装。

**実装ファイル**: `packages/deep-research/src/providers/brave-provider.ts`

**実装内容**: （省略、JinaProviderと同様の構造）

**完了条件**:
- BraveProviderクラスがビルド成功
- テストケース合格

---

### TSK-DR-009: DuckDuckGoProviderクラス実装

**優先度**: P1  
**工数**: 2時間  
**担当者**: -  
**依存**: TSK-DR-006（SearchProviderFactory）  
**トレーサビリティ**: REQ-DR-CORE-002, ADR-v3.4.0-002

#### タスク詳細

DuckDuckGo Instant Answer APIを統合するDuckDuckGoProviderクラスを実装。

**実装ファイル**: `packages/deep-research/src/providers/duckduckgo-provider.ts`

**完了条件**:
- DuckDuckGoProviderクラスがビルド成功
- テストケース合格

---

## 3. Mock実装（テスト駆動開発）

### TSK-DR-028: Mock実装

**優先度**: P0  
**工数**: 3時間  
**担当者**: -  
**依存**: なし（Phase 4-1と並行実施）  
**トレーサビリティ**: 憲法Article III

#### タスク詳細

テスト用Mockクラスを実装。テスト駆動開発のため、Core Engine実装と並行して実施。

**実装ファイル**: `packages/deep-research/src/test/mocks/`

**Mock対象**:
- MockLMProvider: VS Code LM APIのMock
- MockSearchProvider: 検索プロバイダーのMock
- MockExpertDelegation: Expert DelegationのMock
- MockHTTPClient: HTTPクライアントのMock

**実装内容**:
```typescript
// mock-lm-provider.ts
export class MockLMProvider implements LMProvider {
  private responses: Map<string, string> = new Map();
  
  setResponse(prompt: string, response: string): void {
    this.responses.set(prompt, response);
  }
  
  async generateText(request: LMRequest): Promise<LMResponse> {
    const response = this.responses.get(request.messages[0].content) || 'Mock response';
    return {
      text: response,
      tokensUsed: response.length / 4,
      model: 'mock-model',
    };
  }
}

// mock-search-provider.ts
export class MockSearchProvider implements SearchProvider {
  name = 'Mock Provider';
  private results: SearchResult[] = [];
  
  setResults(results: SearchResult[]): void {
    this.results = results;
  }
  
  async search(query: SERPQuery): Promise<SearchResult[]> {
    return this.results.slice(0, query.topK);
  }
  
  async isAvailable(): Promise<boolean> {
    return true;
  }
}
```

**テストケース**:
- ✅ MockLMProviderが設定したレスポンスを返す
- ✅ MockSearchProviderが設定した結果を返す
- ✅ MockExpertDelegationが正常動作

**完了条件**:
- 4つのMockクラスがビルド成功
- 各Mockクラスのテストが合格

---

## 4. Reasoning（推論）

### TSK-DR-010: LMReasoningクラス実装

**優先度**: P0  
**工数**: 4時間  
**担当者**: -  
**依存**: なし  
**トレーサビリティ**: REQ-DR-CORE-004, REQ-DR-CORE-009, DES-DR-v3.4.0, ADR-v3.4.0-003

#### タスク詳細

VS Code LM APIによる推論を行うLMReasoningクラスを実装。

**実装ファイル**: `packages/deep-research/src/reasoning/lm-reasoning.ts`

**実装内容**:
```typescript
export class LMReasoning {
  constructor(
    private lmProvider: VSCodeLMProvider,
    private expertDelegation: DelegationEngine
  ) {}
  
  async generateQuestions(
    query: string,
    currentKnowledge: KnowledgeBase
  ): Promise<ReflectiveQuestion[]> {
    const prompt = `
Original query: ${query}

Current knowledge: ${currentKnowledge.getSummary()}

Generate 3-5 specific follow-up questions to fill knowledge gaps.
Format: JSON array of {question, reason, priority}
`;
    
    const response = await this.lmProvider.generateText({
      messages: [{ role: 'user', content: prompt }],
      maxTokens: 500,
    });
    
    return JSON.parse(response.text);
  }
  
  async evaluateAnswer(
    query: string,
    answer: AnswerAction,
    knowledge: KnowledgeBase
  ): Promise<EvaluationResult> {
    const prompt = `
Evaluate if this answer is definitive and complete:

Query: ${query}
Answer: ${answer.answer}
Knowledge base: ${knowledge.size()} items

Return JSON: {
  isDefinitive: boolean,
  confidence: number,
  missingAspects: string[],
  recommendations: string[]
}
`;
    
    const response = await this.lmProvider.generateText({
      messages: [{ role: 'user', content: prompt }],
      maxTokens: 300,
    });
    
    return JSON.parse(response.text);
  }
  
  async convertToEARS(finding: Finding): Promise<string> {
    const result = await this.expertDelegation.delegate({
      prompt: `Convert to EARS format: ${finding.statement}`,
      expertType: 'ears-analyst',
      mode: 'advisory',
    });
    
    return result.content;
  }
}
```

**テストケース**:
- ✅ generateQuestions()で反射的質問を生成（Mock LM）
- ✅ evaluateAnswer()で回答を評価（Mock LM）
- ✅ convertToEARS()でEARS変換（Mock Expert Delegation）

**完了条件**:
- LMReasoningクラスがビルド成功
- 3つのテストケースが合格
- ADR-v3.4.0-003の設計に準拠

---

### TSK-DR-011: VSCodeLMProviderラッパー実装

**優先度**: P0  
**工数**: 3時間  
**担当者**: -  
**依存**: なし  
**トレーサビリティ**: REQ-DR-CORE-004, ADR-v3.4.0-003

#### タスク詳細

VS Code LM APIをラップするVSCodeLMProviderクラスを実装。

**実装ファイル**: `packages/deep-research/src/providers/vscode-lm-provider.ts`

**実装内容**: （ADR-v3.4.0-003のコード参照）

**完了条件**:
- VSCodeLMProviderクラスがビルド成功
- Mock実装でテストケース合格

---

### TSK-DR-012: ExpertIntegrationクラス実装

**優先度**: P0  
**工数**: 3時間  
**担当者**: -  
**依存**: なし  
**トレーサビリティ**: REQ-DR-INT-001, DES-DR-v3.4.0

#### タスク詳細

Expert Delegationパッケージを統合するExpertIntegrationクラスを実装。

**実装ファイル**: `packages/deep-research/src/integrations/expert-integration.ts`

**実装内容**: （DES-DR-v3.4.0のコード参照）

**完了条件**:
- ExpertIntegrationクラスがビルド成功
- @nahisaho/musubix-expert-delegation v3.2.0+との型互換性確認

---

## 5. Security（セキュリティ）

### TSK-DR-013: SecretManagerシングルトン実装

**優先度**: P0  
**工数**: 3時間  
**担当者**: -  
**依存**: なし  
**トレーサビリティ**: REQ-DR-NFR-003, DES-DR-v3.4.0

#### タスク詳細

API Keyをメモリ管理するSecretManagerシングルトンを実装。

**実装ファイル**: `packages/deep-research/src/security/secret-manager.ts`

**実装内容**: （DES-DR-v3.4.0のコード参照）

**完了条件**:
- SecretManagerクラスがビルド成功
- シングルトンパターン検証
- ログ出力時のマスキング検証

---

### TSK-DR-014: ContentSanitizerクラス実装

**優先度**: P0  
**工数**: 3時間  
**担当者**: -  
**依存**: なし  
**トレーサビリティ**: REQ-DR-NFR-004, DES-DR-v3.4.0

#### タスク詳細

HTMLサニタイズとURL検証を行うContentSanitizerクラスを実装。

**実装ファイル**: `packages/deep-research/src/security/content-sanitizer.ts`

**実装内容**: （DES-DR-v3.4.0のコード参照）

**テストケース**:
- ✅ sanitizeHTML()でXSSペイロード除去
- ✅ validateURL()でHTTPS検証
- ✅ validateURL()でプライベートIP拒否

**完了条件**:
- ContentSanitizerクラスがビルド成功
- 3つのテストケースが合格
- DOMPurify統合確認

---

### TSK-DR-015: カスタムエラークラス実装

**優先度**: P0  
**工数**: 2時間  
**担当者**: -  
**依存**: なし  
**トレーサビリティ**: REQ-DR-NFR-005, DES-DR-v3.4.0

#### タスク詳細

Deep Research専用のエラークラスを実装。

**実装ファイル**: `packages/deep-research/src/types/errors.ts`

**実装内容**: （DES-DR-v3.4.0のコード参照）

**完了条件**:
- 5つのエラークラスがビルド成功
- エラーコンテキスト保持検証

---

## 6. Performance（パフォーマンス）

### TSK-DR-016: ParallelExecutorクラス実装

**優先度**: P1  
**工数**: 3時間  
**担当者**: -  
**依存**: なし  
**トレーサビリティ**: REQ-DR-NFR-002, DES-DR-v3.4.0

#### タスク詳細

並列実行エンジンを実装。

**実装ファイル**: `packages/deep-research/src/performance/parallel-executor.ts`

**実装内容**: （DES-DR-v3.4.0のコード参照）

**完了条件**:
- ParallelExecutorクラスがビルド成功
- 最大3並列実行検証

---

### TSK-DR-017: LRUCacheクラス実装

**優先度**: P1  
**工数**: 3時間  
**担当者**: -  
**依存**: なし  
**トレーサビリティ**: REQ-DR-NFR-001, DES-DR-v3.4.0

#### タスク詳細

TTL対応LRUキャッシュを実装。

**実装ファイル**: `packages/deep-research/src/utils/cache.ts`

**実装内容**: （DES-DR-v3.4.0のコード参照、v0.1.1修正版）

**テストケース**:
- ✅ LRUアルゴリズム動作検証
- ✅ TTL期限切れ検証
- ✅ purgeExpired()動作検証

**完了条件**:
- LRUCacheクラスがビルド成功
- 3つのテストケースが合格

---

### TSK-DR-018: 性能プロファイリング実装

**優先度**: P2  
**工数**: 2時間  
**担当者**: -  
**依存**: TSK-DR-001（ResearchEngine）  
**トレーサビリティ**: REQ-DR-NFR-001

#### タスク詳細

各フェーズの実行時間を計測するプロファイラーを実装。

**実装ファイル**: `packages/deep-research/src/utils/profiler.ts`

**完了条件**:
- Profilerクラスがビルド成功
- ResearchEngineに統合

---

## 7. Integration（統合）

### TSK-DR-019: KnowledgeStore統合

**優先度**: P1  
**工数**: 3時間  
**担当者**: -  
**依存**: TSK-DR-002（KnowledgeBase）  
**トレーサビリティ**: REQ-DR-INT-004, DES-DR-v3.4.0

#### タスク詳細

@musubix/knowledge v3.0.0+と統合するKnowledgeStoreIntegrationクラスを実装。

**実装ファイル**: `packages/deep-research/src/integrations/knowledge-store-integration.ts`

**実装内容**: （DES-DR-v3.4.0のコード参照）

**完了条件**:
- KnowledgeStoreIntegrationクラスがビルド成功
- @musubix/knowledge v3.0.0+との型互換性確認

---

### TSK-DR-020: Neural Search統合

**優先度**: P1  
**工数**: 2時間  
**担当者**: -  
**依存**: TSK-DR-006（SearchProviderFactory）  
**トレーサビリティ**: REQ-DR-INT-002, DES-DR-v3.4.0

#### タスク詳細

@nahisaho/musubix-neural-search v2.2.0+と統合。

**実装ファイル**: `packages/deep-research/src/integrations/neural-search-integration.ts`

**完了条件**:
- NeuralSearchIntegrationクラスがビルド成功

---

### TSK-DR-021: Agent Orchestrator統合

**優先度**: P1  
**工数**: 2時間  
**担当者**: -  
**依存**: TSK-DR-001（ResearchEngine）  
**トレーサビリティ**: REQ-DR-INT-003, DES-DR-v3.4.0

#### タスク詳細

@nahisaho/musubix-agent-orchestrator v2.4.0+と統合。

**実装ファイル**: `packages/deep-research/src/integrations/orchestrator-integration.ts`

**完了条件**:
- AgentOrchestratorIntegrationクラスがビルド成功

---

### TSK-DR-022: Workflow Engine統合

**優先度**: P1  
**工数**: 3時間  
**担当者**: -  
**依存**: TSK-DR-005（ReportGenerator）  
**トレーサビリティ**: REQ-DR-INT-008, DES-DR-v3.4.0

#### タスク詳細

@nahisaho/musubix-workflow-engine v2.4.0+と統合。

**実装ファイル**: `packages/deep-research/src/integrations/workflow-integration.ts`

**実装内容**: （DES-DR-v3.4.0のコード参照）

**完了条件**:
- WorkflowIntegrationクラスがビルド成功
- Phase 1への結果注入検証

---

### TSK-DR-023: CLI コマンド実装

**優先度**: P0  
**工数**: 3時間  
**担当者**: -  
**依存**: TSK-DR-001（ResearchEngine）  
**トレーサビリティ**: REQ-DR-INT-006, DES-DR-v3.4.0

#### タスク詳細

`npx musubix deep-research <query>`コマンドを実装。

**実装ファイル**: 
- `packages/deep-research/src/cli/deep-research-command.ts`
- `packages/core/src/cli/commands/deep-research.ts`（登録）

**実装内容**: （DES-DR-v3.4.0のコード参照）

**完了条件**:
- CLIコマンドが実行可能
- --help, --version, --output オプション動作確認

---

### TSK-DR-024: MCP Tools実装（8ツール）

**優先度**: P1  
**工数**: 4時間  
**担当者**: -  
**依存**: TSK-DR-001（ResearchEngine）  
**トレーサビリティ**: REQ-DR-INT-005, DES-DR-v3.4.0

#### タスク詳細

既存mcp-serverパッケージに8つのDeep Researchツールを追加。

**実装ファイル**: `packages/mcp-server/src/tools/deep-research-tools.ts`

**実装内容**:
```typescript
export const deepResearchTools = [
  {
    name: 'deep_research_start',
    description: 'Start a deep research investigation',
    inputSchema: z.object({
      query: z.string(),
      maxIterations: z.number().optional(),
      tokenBudget: z.number().optional(),
    }),
    handler: async (input) => { /* ... */ },
  },
  {
    name: 'deep_research_get_report',
    description: 'Get research report by ID',
    inputSchema: z.object({
      reportId: z.string(),
      format: z.enum(['markdown', 'json']).optional(),
    }),
    handler: async (input) => { /* ... */ },
  },
  // 残り6ツール...
];
```

**完了条件**:
- 8ツールがmcp-serverに登録
- MCPクライアントから呼び出し可能

---

### TSK-DR-025: 憲法準拠検証

**優先度**: P1  
**工数**: 1時間  
**担当者**: -  
**依存**: TSK-DR-023（CLI）  
**トレーサビリティ**: REQ-DR-INT-009, DES-DR-v3.4.0

#### タスク詳細

10憲法条項への準拠を自動検証。

**実装ファイル**: `packages/deep-research/src/compliance/constitution-validator.ts`

**完了条件**:
- ConstitutionValidatorクラスがビルド成功
- 10条項チェック実装

---

## 8. Testing（テスト）

### TSK-DR-026: ユニットテスト実装

**優先度**: P0  
**工数**: 6時間  
**担当者**: -  
**依存**: TSK-DR-001〜025  
**トレーサビリティ**: 憲法Article III

#### タスク詳細

全モジュールのユニットテストを実装。

**テスト対象**:
- Core Engine: ResearchEngine, KnowledgeBase, TokenTracker, TrajectoryLogger, ReportGenerator
- Providers: SearchProviderFactory, JinaProvider, BraveProvider, DuckDuckGoProvider
- Reasoning: LMReasoning, VSCodeLMProvider, ExpertIntegration
- Security: SecretManager, ContentSanitizer, ErrorClasses
- Performance: ParallelExecutor, LRUCache
- Integration: 全統合クラス

**カバレッジ目標**: 85%以上

**完了条件**:
- 全テストが合格
- カバレッジ85%達成

---

### TSK-DR-027: 統合テスト実装

**優先度**: P0  
**工数**: 4時間  
**担当者**: -  
**依存**: TSK-DR-026  
**トレーサビリティ**: 憲法Article III

#### タスク詳細

E2E風の統合テストを実装。

**テストシナリオ**:
1. ResearchEngine.research()が完全に動作
2. 検索プロバイダーのフォールバック
3. トークン予算超過の早期停止
4. レポート生成（Markdown/JSON）

**完了条件**:
- 4シナリオが合格

---

### TSK-DR-029: セキュリティテスト実装

**優先度**: P0  
**工数**: 2時間  
**担当者**: -  
**依存**: TSK-DR-013, TSK-DR-014  
**トレーサビリティ**: REQ-DR-NFR-003, REQ-DR-NFR-004

#### タスク詳細

セキュリティ関連の専用テストを実装。

**テストケース**:
- ✅ XSSペイロード除去（20種類）
- ✅ API Keyマスキング
- ✅ プライベートIP拒否
- ✅ HTTPS検証

**完了条件**:
- 全セキュリティテストが合格

---

### TSK-DR-030: パフォーマンステスト実装

**優先度**: P1  
**工数**: 1時間  
**担当者**: -  
**依存**: TSK-DR-001  
**トレーサビリティ**: REQ-DR-NFR-001

#### タスク詳細

パフォーマンス要件の検証テストを実装。

**テストケース**:
- ✅ 応答時間3秒以内（モック環境）
- ✅ 並列実行3並列動作確認
- ✅ LRUキャッシュヒット率測定

**完了条件**:
- 全パフォーマンステストが合格

---

## 9. Documentation（ドキュメント）

### TSK-DR-031: READMEとAPI Docs作成

**優先度**: P2  
**工数**: 3時間  
**担当者**: -  
**依存**: TSK-DR-023（CLI）  
**トレーサビリティ**: 憲法Article II

#### タスク詳細

パッケージREADMEとAPI Docsを作成。

**実装ファイル**: 
- `packages/deep-research/README.md`
- `docs/packages/deep-research.md`

**内容**:
- インストール方法
- CLI使用例
- API Reference
- 設定オプション

**完了条件**:
- README作成完了
- API Docs作成完了

---

### TSK-DR-032: CHANGELOG更新

**優先度**: P2  
**工数**: 1時間  
**担当者**: -  
**依存**: TSK-DR-001〜030  
**トレーサビリティ**: なし

#### タスク詳細

CHANGELOG.mdにv3.4.0エントリを追加。

**実装ファイル**: `CHANGELOG.md`

**内容**:
```markdown
## [3.4.0] - 2026-01-XX

### Added
- Deep Research機能追加（packages/deep-research）
- 反復的search-read-reasonサイクル
- 3段階検索プロバイダー（Jina/Brave/DuckDuckGo）
- VS Code LM API統合
- 8つのMCPツール追加
- Expert Delegation統合

### Changed
- なし

### Fixed
- なし
```

**完了条件**:
- CHANGELOG.md更新完了

---

## 10. タスク実行計画

### Phase 4-1: Foundation（基盤） - 41時間

```
Week 1 (Day 1-2):
  TSK-DR-001: ResearchEngine実装 (4h)
  TSK-DR-002: KnowledgeBase実装 (3h)
  TSK-DR-003: TokenTracker実装 (2h)
  TSK-DR-004: TrajectoryLogger実装 (3h)
  TSK-DR-005: ReportGenerator実装 (4h)
  TSK-DR-028: Mock実装 (3h) ← Phase 4-1に移動

Week 1 (Day 3-4):
  TSK-DR-006: SearchProviderFactory実装 (4h)
  TSK-DR-007: JinaProvider実装 (3h)
  TSK-DR-008: BraveProvider実装 (3h)
  TSK-DR-009: DuckDuckGoProvider実装 (2h)

Week 1 (Day 5):
  TSK-DR-010: LMReasoning実装 (4h)
  TSK-DR-011: VSCodeLMProvider実装 (3h)
  TSK-DR-012: ExpertIntegration実装 (3h)
```

### Phase 4-2: Enhancement（強化） - 34時間

```
Week 2 (Day 1):
  TSK-DR-013: SecretManager実装 (3h)
  TSK-DR-014: ContentSanitizer実装 (3h)
  TSK-DR-015: カスタムエラー実装 (2h)

Week 2 (Day 2):
  TSK-DR-016: ParallelExecutor実装 (3h)
  TSK-DR-017: LRUCache実装 (3h)
  TSK-DR-018: 性能プロファイリング実装 (2h)

Week 2 (Day 3-5):
  TSK-DR-019: KnowledgeStore統合 (3h)
  TSK-DR-020: Neural Search統合 (2h)
  TSK-DR-021: Agent Orchestrator統合 (2h)
  TSK-DR-022: Workflow Engine統合 (3h)
  TSK-DR-023: CLI コマンド実装 (3h)
  TSK-DR-024: MCP Tools実装 (4h)
  TSK-DR-025: 憲法準拠検証 (1h)
```

### Phase 4-3: Quality Assurance（品質保証） - 17時間

```
Week 3 (Day 1-2):
  TSK-DR-026: ユニットテスト実装 (6h)
  TSK-DR-027: 統合テスト実装 (4h)
  TSK-DR-029: セキュリティテスト実装 (2h)
  TSK-DR-030: パフォーマンステスト実装 (1h)

Week 3 (Day 3):
  TSK-DR-031: READMEとAPI Docs作成 (3h)
  TSK-DR-032: CHANGELOG更新 (1h)
```

---

## 11. リスク管理

| リスク | 発生確率 | 影響度 | 対策 |
|--------|---------|--------|------|
| VS Code LM API変更 | 低 | 高 | Adapterパターンで抽象化済み |
| Jina AI API障害 | 中 | 中 | 3段階フォールバック実装 |
| Expert Delegation互換性 | 低 | 高 | v3.2.0+の型定義確認済み |
| トークン予算不足 | 中 | 低 | TokenTrackerで制御 |
| テストカバレッジ不足 | 中 | 中 | Phase 4-3で集中実施 |

---

## 12. 完了条件

### Phase 4-1完了条件
- [ ] TSK-DR-001〜012が完了
- [ ] ユニットテストが85%以上合格
- [ ] ResearchEngine.research()が動作

### Phase 4-2完了条件
- [ ] TSK-DR-013〜025が完了
- [ ] CLIコマンドが実行可能
- [ ] MCPツールが登録済み

### Phase 4-3完了条件
- [ ] TSK-DR-026〜032が完了
- [ ] 全テストが合格
- [ ] カバレッジ85%達成

### v3.4.0リリース条件
- [ ] Phase 4-1, 4-2, 4-3が完了
- [ ] ADR-v3.4.0-001〜003が承認
- [ ] 憲法10条項準拠確認
- [ ] READMEとCHANGELOG更新

---

## 13. 変更履歴

| 日付 | バージョン | 変更内容 | 著者 |
|------|-----------|---------|------|
| 2026-01-16 | 1.0 | 初版作成（32タスク定義） | AI Agent |

---

**タスク分解書終了**
