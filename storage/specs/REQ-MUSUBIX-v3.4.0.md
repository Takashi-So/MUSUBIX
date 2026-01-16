# MUSUBIX v3.4.0 要件定義書
# Deep Research Integration - AI Agent Research Enhancement

**文書ID**: REQ-MUSUBIX-v3.4.0  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.3  
**作成日**: 2026-01-16  
**更新日**: 2026-01-16  
**承認日**: 2026-01-16  
**ステータス**: ✅ Approved  
**準拠規格**: EARS（Easy Approach to Requirements Syntax）  
**参照文書**: 
- REQ-MUSUBIX-v3.3.0.md
- https://github.com/jina-ai/node-DeepResearch
- packages/expert-delegation/README.md
- packages/neural-search/README.md
- packages/agent-orchestrator/README.md

---

## 1. 文書概要

### 1.1 目的

本文書は、MUSUBIX v3.4.0のDeep Research機能要件をEARS形式で正式に定義する。要件定義・設計時のAIエージェントによる技術調査を自動化し、より詳細な情報に基づいた意思決定を可能にする。

### 1.2 背景

**課題認識**:
1. **要件定義時の技術調査不足**: AIエージェントが要件定義・設計時に必要な技術情報を十分に収集できていない
2. **調査の網羅性不足**: 単発的な検索では関連情報を見落とし、不完全な要件定義につながる
3. **ファクトチェック不在**: 情報の正確性を検証せずに要件・設計に反映されるリスク
4. **既存機能の未活用**: expert-delegation、neural-search、agent-orchestratorが調査プロセスと統合されていない

**解決アプローチ**:
- **反復的調査サイクル**: 検索 → 読取 → 推論 → 再検索のループで深い調査を実現
- **VS Code LM API統合**: GitHub Copilotを活用した推論・分析
- **既存機能統合**: expert-delegation（専門家委譲）、neural-search（意味的検索）、agent-orchestrator（複雑度分析）の活用
- **トークン予算管理**: 無制限な調査を防ぎ、コスト管理を実現

**参照実装**: jina-ai/node-DeepResearch
- 反復的search-read-reasonサイクル
- 複数検索プロバイダー対応（Jina、Brave、DuckDuckGo）
- LLMによる多段階推論（search → reflect → answer）
- トークン予算とコスト追跡

### 1.3 EARS パターン定義

| パターン | キーワード | 用途 | 構文 |
|----------|-----------|------|------|
| **Ubiquitous** | SHALL | システムが常に満たすべき要件 | THE \<system\> SHALL \<requirement\> |
| **Event-Driven** | WHEN...SHALL | イベント発生時の要件 | WHEN \<trigger\>, THE \<system\> SHALL \<response\> |
| **State-Driven** | WHILE...SHALL | 特定状態における要件 | WHILE \<state\>, THE \<system\> SHALL \<response\> |
| **Unwanted** | SHALL NOT | 禁止事項 | THE \<system\> SHALL NOT \<behavior\> |
| **Optional** | IF...THEN SHALL | 条件付き要件 | IF \<condition\>, THEN THE \<system\> SHALL \<response\> |

### 1.4 優先度定義

| 優先度 | 説明 | 対象バージョン |
|--------|------|---------------|
| **P0** | 必須 - リリースブロッカー | v3.4.0 |
| **P1** | 重要 - 可能な限り実装 | v3.4.0 |
| **P2** | 任意 - 時間があれば | v3.5.0+ |

### 1.5 要件ID体系

```
REQ-DR-<カテゴリ>-<連番>
```

| カテゴリ | 説明 |
|---------|------|
| CORE | コア機能（検索・読取・推論サイクル） |
| INT | 統合（既存機能との統合） |
| NFR | 非機能要件（パフォーマンス、セキュリティ） |

### 1.6 スコープサマリー

| カテゴリ | P0 | P1 | P2 | 合計 |
|---------|----|----|----|----- |
| CORE (コア機能) | 5 | 3 | 2 | 10 |
| INT (統合) | 3 | 4 | 2 | 9 |
| NFR (非機能) | 2 | 3 | 1 | 6 |
| **合計** | **10** | **10** | **5** | **25** |

### 1.7 ユースケース概要

```
AIエージェント（要件定義・設計フェーズ）
    ↓
    1. Deep Research起動（npx musubix deep-research <query>）
    ↓
    2. 反復調査サイクル
       - 検索（Jina/Brave/DuckDuckGo）
       - Web読取（Jina Reader）
       - LM API推論（GitHub Copilot）
       - 不足情報の特定 → 再検索
    ↓
    3. 調査レポート生成
       - 発見事実（引用付き）
       - 技術選択肢
       - 推奨事項
       - 注意事項
    ↓
    4. 要件定義書・設計書への反映
       - 技術的根拠の明記
       - トレーサビリティリンク（REQ-DR-xxx）
```

---

## 2. コア機能要件（CORE）

### 2.1 反復検索機能

#### REQ-DR-CORE-001: 反復検索サイクル
**優先度**: P0  
**パターン**: Ubiquitous

THE system SHALL implement an iterative search-read-reason cycle that continues until:
- A definitive answer is found with citations
- The token budget is exceeded
- Maximum iteration count is reached (default: 10)

**受入基準**:
```typescript
interface ResearchCycle {
  maxIterations: number;        // Default: 10
  tokenBudget: number;           // Default: 100,000
  confidence: number;            // Min: 0.8 for completion
  
  phases: ['search', 'read', 'reason', 'evaluate'];
  stopConditions: ['answer_found', 'budget_exceeded', 'max_iterations'];
}

// 使用例
const result = await deepResearch(query, {
  maxIterations: 10,
  tokenBudget: 100000,
  minConfidence: 0.8,
});

expect(result.completed).toBe(true);
expect(result.citations.length).toBeGreaterThan(0);
```

**実装パッケージ**: `packages/deep-research/`  
**トレーサビリティ**: DES-DR-001, TSK-DR-001

---

#### REQ-DR-CORE-002: 検索プロバイダー統合
**優先度**: P0  
**パターン**: Ubiquitous

THE system SHALL support multiple search providers with fallback mechanism:
- Jina Search API (primary)
- Brave Search API (fallback 1)
- DuckDuckGo Search (fallback 2)

**受入基準**:
```typescript
interface SearchProvider {
  name: 'jina' | 'brave' | 'duckduckgo';
  apiKey?: string;
  rateLimit: number;  // requests per minute
  timeout: number;    // milliseconds
}

// 環境変数設定
process.env.JINA_API_KEY = 'jina_xxx';
process.env.BRAVE_API_KEY = 'BSA_xxx';
process.env.SEARCH_PROVIDER = 'jina';  // 優先プロバイダー

// フォールバック動作
const results = await search(query);
// Jina失敗 → Brave試行 → DuckDuckGo試行
```

**実装パッケージ**: `packages/deep-research/src/providers/`  
**トレーサビリティ**: DES-DR-002, TSK-DR-002

---

#### REQ-DR-CORE-003: Web コンテンツ読取
**優先度**: P0  
**パターン**: Event-Driven

WHEN the system identifies relevant URLs from search results, THE system SHALL read and extract content using Jina Reader API with:
- Markdown format extraction
- Image URLs extraction (optional)
- Link extraction for further exploration
- Token usage tracking

**受入基準**:
```typescript
interface ReadResult {
  url: string;
  title: string;
  content: string;        // Markdown format
  images?: string[];      // Image URLs
  links?: Array<{ anchor: string; url: string }>;
  tokens: number;         // Token usage
  timestamp: string;
}

const readResult = await readUrl('https://example.com');
expect(readResult.content).toContain('# Title');
expect(readResult.tokens).toBeGreaterThan(0);
```

**実装パッケージ**: `packages/deep-research/src/readers/`  
**トレーサビリティ**: DES-DR-003, TSK-DR-003

---

#### REQ-DR-CORE-004: LM API推論統合
**優先度**: P0  
**パターン**: Ubiquitous

THE system SHALL integrate with VS Code Language Model API for reasoning tasks:
- Question generation (identify knowledge gaps)
- Answer evaluation (assess completeness and accuracy)
- Citation extraction (link findings to sources)
- Research direction determination (what to search next)

**受入基準**:
```typescript
interface LMReasoningRequest {
  task: 'question' | 'evaluate' | 'extract' | 'direction';
  context: string[];           // Previous findings
  query: string;               // Original query
  knowledge: KnowledgeItem[];  // Accumulated knowledge
}

interface LMReasoningResponse {
  action: 'search' | 'read' | 'reflect' | 'answer';
  confidence: number;          // 0.0-1.0
  content: string;
  references?: Reference[];
  nextSteps?: string[];        // Suggested actions
}

// VS Code LM API経由で推論
const reasoning = await lmReasoning({
  task: 'evaluate',
  context: findings,
  query: originalQuery,
  knowledge: accumulatedKnowledge,
});

expect(reasoning.action).toBeOneOf(['search', 'read', 'reflect', 'answer']);
expect(reasoning.confidence).toBeGreaterThanOrEqual(0);
```

**実装パッケージ**: `packages/deep-research/src/reasoning/`  
**トレーサビリティ**: DES-DR-004, TSK-DR-004

---

#### REQ-DR-CORE-005: 調査レポート生成
**優先度**: P0  
**パターン**: Event-Driven

WHEN the research cycle completes, THE system SHALL generate a comprehensive research report containing:
- Executive summary (2-3 paragraphs)
- Key findings (bullet points with citations)
- Technical options (comparison table)
- Recommendations (prioritized list)
- References (all cited sources)

**受入基準**:
```typescript
interface ResearchReport {
  query: string;
  summary: string;              // Executive summary
  findings: Finding[];          // Key discoveries
  options: TechnicalOption[];   // Technology choices
  recommendations: Recommendation[];
  references: Reference[];      // All citations
  metadata: {
    iterations: number;
    tokensUsed: number;
    duration: number;           // milliseconds
    confidence: number;
  };
}

interface Finding {
  statement: string;
  citations: Reference[];
  confidence: number;
}

interface TechnicalOption {
  name: string;
  description: string;
  pros: string[];
  cons: string[];
  citations: Reference[];
}

const report = await generateReport(researchResult);
expect(report.findings.length).toBeGreaterThan(0);
expect(report.references.length).toBeGreaterThan(0);
expect(report.summary.length).toBeGreaterThan(100);
```

**実装パッケージ**: `packages/deep-research/src/reporters/`  
**トレーサビリティ**: DES-DR-005, TSK-DR-005

---

#### REQ-DR-CORE-006: トークン予算管理
**優先度**: P1  
**パターン**: State-Driven

WHILE the research cycle is active, THE system SHALL track token usage across all API calls and:
- Accumulate tokens from search, read, and reasoning operations
- Emit warnings at 80% budget consumption
- Stop research when budget is exceeded
- Provide detailed usage breakdown in the report

**受入基準**:
```typescript
interface TokenTracker {
  budget: number;
  used: number;
  breakdown: Record<string, number>;  // by operation type
  
  trackUsage(operation: string, tokens: number): void;
  getRemaining(): number;
  isExceeded(): boolean;
  emitWarning(): boolean;  // true if ≥80% used
}

const tracker = new TokenTracker(100000);
tracker.trackUsage('search', 500);
tracker.trackUsage('read', 2000);
tracker.trackUsage('reasoning', 1500);

expect(tracker.used).toBe(4000);
expect(tracker.getRemaining()).toBe(96000);
expect(tracker.isExceeded()).toBe(false);
```

**実装パッケージ**: `packages/deep-research/src/utils/token-tracker.ts`  
**トレーサビリティ**: DES-DR-006, TSK-DR-006

---

#### REQ-DR-CORE-007: 引用管理
**優先度**: P1  
**パターン**: Ubiquitous

THE system SHALL maintain citations for all findings with:
- Source URL
- Exact quote (excerpt)
- Timestamp of access
- Relevance score (0.0-1.0)
- Position in answer (for inline citations)

**受入基準**:
```typescript
interface Reference {
  url: string;
  title: string;
  exactQuote: string;          // Original text from source
  timestamp: string;            // ISO 8601
  relevanceScore: number;       // 0.0-1.0
  answerChunk?: string;         // Part of answer this supports
  answerChunkPosition?: [number, number];  // [start, end] indices
}

const citation = createReference({
  url: 'https://example.com/article',
  quote: 'TypeScript is a strongly typed language',
  relevance: 0.95,
});

expect(citation.exactQuote).toBe('TypeScript is a strongly typed language');
expect(citation.relevanceScore).toBe(0.95);
expect(citation.timestamp).toMatch(/^\d{4}-\d{2}-\d{2}T/);
```

**実装パッケージ**: `packages/deep-research/src/citations/`  
**トレーサビリティ**: DES-DR-007, TSK-DR-007

---

#### REQ-DR-CORE-008: 知識蓄積機構
**優先度**: P1  
**パターン**: Event-Driven

WHEN new information is discovered during research, THE system SHALL accumulate knowledge items with:
- Content (extracted facts)
- Source references
- Discovery iteration number
- Relevance to original query

**受入基準**:
```typescript
interface KnowledgeItem {
  id: string;
  content: string;              // Extracted fact or insight
  sources: Reference[];         // Supporting citations
  iteration: number;            // When discovered (1-based)
  relevance: number;            // To original query (0.0-1.0)
  type: 'fact' | 'opinion' | 'recommendation' | 'example';
}

const knowledge = new KnowledgeBase();
knowledge.add({
  content: 'EARS format has 5 patterns',
  sources: [ref1, ref2],
  iteration: 2,
  relevance: 0.9,
  type: 'fact',
});

expect(knowledge.size()).toBe(1);
expect(knowledge.getByIteration(2).length).toBe(1);
```

**実装パッケージ**: `packages/deep-research/src/knowledge/`  
**トレーサビリティ**: DES-DR-008, TSK-DR-008

---

#### REQ-DR-CORE-009: 反射的質問生成
**優先度**: P2  
**パターン**: Event-Driven

WHEN the system evaluates current knowledge and finds gaps, THE system SHALL generate follow-up questions to guide further research:
- Identify missing information
- Generate 3-5 specific questions
- Prioritize questions by importance
- Avoid duplicate questions

**受入基準**:
```typescript
interface ReflectiveQuestion {
  question: string;
  reason: string;               // Why this question matters
  priority: number;             // 1 (high) to 5 (low)
  relatedFindings: string[];    // IDs of related knowledge items
}

const questions = await generateQuestions(currentKnowledge, originalQuery);
expect(questions.length).toBeGreaterThanOrEqual(1);
expect(questions.length).toBeLessThanOrEqual(5);
expect(questions[0].priority).toBe(1);  // Highest priority first
```

**実装パッケージ**: `packages/deep-research/src/reflection/`  
**トレーサビリティ**: DES-DR-009, TSK-DR-009

---

#### REQ-DR-CORE-010: 調査軌跡ログ
**優先度**: P2  
**パターン**: Ubiquitous

THE system SHALL log the complete research trajectory including:
- Each iteration's actions (search query, URLs visited, reasoning steps)
- Token consumption per operation
- Time spent per iteration
- Confidence scores over time

**受入基準**:
```typescript
interface ResearchTrajectory {
  iterations: IterationLog[];
  totalDuration: number;
  totalTokens: number;
  finalConfidence: number;
}

interface IterationLog {
  iteration: number;
  action: 'search' | 'read' | 'reflect' | 'answer';
  input: string;                // Query or URL
  output: string;               // Summary of result
  tokens: number;
  duration: number;
  confidence: number;
}

const trajectory = tracker.getTrajectory();
expect(trajectory.iterations.length).toBeGreaterThan(0);
expect(trajectory.totalTokens).toBeGreaterThan(0);
```

**実装パッケージ**: `packages/deep-research/src/utils/trajectory-logger.ts`  
**トレーサビリティ**: DES-DR-010, TSK-DR-010

---

## 3. 統合要件（INT）

### 3.1 Expert Delegation統合

#### REQ-DR-INT-001: 専門家委譲統合
**優先度**: P0  
**パターン**: Event-Driven

WHEN the research requires specialized analysis, THE system SHALL delegate to appropriate experts via `@nahisaho/musubix-expert-delegation`:
- EARS Analyst: Requirements format conversion
- Architect: Architecture design recommendations
- Security Analyst: Security implications review

**受入基準**:
```typescript
import { createDelegationEngine } from '@nahisaho/musubix-expert-delegation';

const delegationEngine = createDelegationEngine(lmProvider);

// Research中に専門家へ委譲
if (requiresEARSConversion(finding)) {
  const earsResult = await delegationEngine.analyze(
    `Convert to EARS format: ${finding}`,
    'ears-analyst'
  );
  knowledge.add({ content: earsResult.content, type: 'recommendation' });
}

expect(earsResult.content).toMatch(/THE .* SHALL/);
```

**実装パッケージ**: `packages/deep-research/src/integrations/expert-integration.ts`  
**トレーサビリティ**: DES-DR-INT-001, TSK-DR-INT-001

---

#### REQ-DR-INT-002: Neural Search統合
**優先度**: P0  
**パターン**: Event-Driven

WHEN the system needs to find semantically similar content, THE system SHALL use `@nahisaho/musubix-neural-search` for:
- Code example search in local workspace
- Similar pattern detection
- Relevance ranking of findings

**受入基準**:
```typescript
import { createSemanticSearcher } from '@nahisaho/musubix-neural-search';

const searcher = createSemanticSearcher();

// 既存コードから類似パターン検索
const similarPatterns = await searcher.search(
  'authentication implementation examples',
  { workspaceRoot: process.cwd(), maxResults: 5 }
);

expect(similarPatterns.length).toBeGreaterThan(0);
expect(similarPatterns[0].relevance).toBeGreaterThan(0.7);
```

**実装パッケージ**: `packages/deep-research/src/integrations/search-integration.ts`  
**トレーサビリティ**: DES-DR-INT-002, TSK-DR-INT-002

---

#### REQ-DR-INT-003: Agent Orchestrator統合
**優先度**: P0  
**パターン**: Event-Driven

WHEN the research query complexity exceeds threshold, THE system SHALL use `@nahisaho/musubix-agent-orchestrator` to:
- Analyze query complexity
- Decompose into sub-research tasks
- Dispatch to parallel research agents
- Aggregate results

**受入基準**:
```typescript
import { createOrchestrator } from '@nahisaho/musubix-agent-orchestrator';

const orchestrator = createOrchestrator();

const complexity = await orchestrator.analyzeComplexity(query);

if (complexity.score > 0.7) {
  const subTasks = await orchestrator.decompose(query);
  const results = await Promise.all(
    subTasks.map(task => deepResearch(task.query))
  );
  const aggregated = await orchestrator.aggregate(results);
}

expect(aggregated.findings.length).toBeGreaterThan(0);
```

**実装パッケージ**: `packages/deep-research/src/integrations/orchestrator-integration.ts`  
**トレーサビリティ**: DES-DR-INT-003, TSK-DR-INT-003

---

#### REQ-DR-INT-004: Knowledge Store統合
**優先度**: P1  
**パターン**: Event-Driven

WHEN research completes, THE system SHALL store findings in `@musubix/knowledge` for:
- Future reference and retrieval
- Cross-project knowledge sharing
- Traceability to requirements/design

**受入基準**:
```typescript
import { createKnowledgeStore } from '@musubix/knowledge';

const store = createKnowledgeStore('.knowledge');

// 調査結果を知識グラフに保存
await store.putEntity({
  id: `research:DR-${Date.now()}`,
  type: 'research',
  name: query,
  properties: {
    findings: report.findings,
    references: report.references,
    timestamp: new Date().toISOString(),
  },
  tags: ['deep-research', 'v3.4.0'],
});

// 要件とのリレーション追加
await store.addRelation({
  source: `research:DR-${Date.now()}`,
  target: 'requirement:REQ-001',
  type: 'supports',
  properties: { confidence: 0.9 },
});
```

**実装パッケージ**: `packages/deep-research/src/integrations/knowledge-integration.ts`  
**トレーサビリティ**: DES-DR-INT-004, TSK-DR-INT-004

---

#### REQ-DR-INT-005: MCPツール提供
**優先度**: P1  
**パターン**: Ubiquitous

THE system SHALL provide MCP tools for deep research operations:
- `deep_research_start`: Start research with query and options
- `deep_research_status`: Check progress and current state
- `deep_research_report`: Get research report

**受入基準**:
```typescript
// MCP Tools実装（@nahisaho/musubix-deep-research/mcp）
import { DeepResearchMCPHandler, DEEP_RESEARCH_TOOLS } from '@nahisaho/musubix-deep-research';

const handler = new DeepResearchMCPHandler();

// deep_research_start: 調査開始
const startResult = await handler.handleStart({
  query: 'What are the best practices for EARS requirements?',
  maxIterations: 10,
  tokenBudget: 50000,
});

expect(startResult.researchId).toBeDefined();
expect(startResult.status).toBe('running');

// deep_research_status: 進捗確認
const statusResult = await handler.handleStatus({
  researchId: startResult.researchId,
});

expect(statusResult.id).toBe(startResult.researchId);
expect(statusResult.status).toMatch(/running|completed|failed/);

// deep_research_report: レポート取得
const reportResult = await handler.handleReport({
  researchId: startResult.researchId,
  format: 'markdown',
});

expect(typeof reportResult).toBe('string');
```

**実装パッケージ**: `packages/deep-research/src/mcp/` (MCPツール本体)  
**トレーサビリティ**: DES-DR-INT-005, TSK-DR-020

---

#### REQ-DR-INT-006: CLIコマンド提供
**優先度**: P1  
**パターン**: Event-Driven

WHEN the user executes `npx musubix deep-research <query>`, THE system SHALL start deep research and:
- Display progress in real-time
- Show iteration count and token usage
- Save report to `storage/research/`
- Output markdown report to stdout

**受入基準**:
```bash
# 基本的な調査
npx musubix deep-research "What are EARS requirements patterns?"

# オプション指定
npx musubix deep-research "TypeScript best practices" \
  --max-iterations 15 \
  --token-budget 100000 \
  --output research-report.md

# 出力確認
cat storage/research/research-*.md
```

**実装パッケージ**: `packages/core/src/cli/commands/deep-research.ts`  
**トレーサビリティ**: DES-DR-INT-006, TSK-DR-019

---

#### REQ-DR-INT-007: 要件定義書自動挿入
**優先度**: P2  
**パターン**: Optional

IF the user enables `--inject-requirements` flag, THEN THE system SHALL automatically insert research findings into requirements document with:
- Citation references (REQ-DR-xxx)
- Technical background section
- References section with URLs

**受入基準**:
```bash
# 調査結果を要件定義書に自動挿入
npx musubix deep-research "OAuth 2.0 security considerations" \
  --inject-requirements storage/specs/REQ-AUTH-001.md

# 要件定義書に追記される内容:
# ## Technical Background (from Deep Research DR-2026-01-16-001)
# ...
# ## References
# [^1]: https://oauth.net/2/security-best-practices/
```

**実装パッケージ**: `packages/core/src/cli/commands/research.ts`  
**トレーサビリティ**: DES-DR-INT-007, TSK-DR-INT-007

---

#### REQ-DR-INT-008: Workflow Engine統合
**優先度**: P2  
**パターン**: State-Driven

WHILE in Phase 1 (Requirements) or Phase 2 (Design), THE system SHALL suggest deep research for:
- Ambiguous requirements
- Technology selection decisions
- Security/performance considerations

**受入基準**:
```typescript
import { createWorkflowEngine } from '@nahisaho/musubix-workflow-engine';

const workflow = createWorkflowEngine();

// Phase 1でDeep Researchを推奨
if (workflow.getCurrentPhase() === 'requirements') {
  const suggestions = await workflow.getSuggestions();
  
  const researchSuggestion = suggestions.find(
    s => s.type === 'deep-research'
  );
  
  if (researchSuggestion) {
    console.log(`💡 Consider researching: ${researchSuggestion.query}`);
  }
}
```

**実装パッケージ**: `packages/workflow-engine/src/quality-gates/research-recommender.ts`  
**トレーサビリティ**: DES-DR-INT-008, TSK-DR-INT-008

---

#### REQ-DR-INT-009: Constitution遵守チェック
**優先度**: P1  
**パターン**: Unwanted

THE system SHALL NOT bypass constitutional articles during research:
- Article IV: Research findings SHALL be converted to EARS format
- Article V: Research results SHALL maintain traceability (REQ-DR-xxx IDs)
- Article VIII: Technology decisions SHALL be recorded as ADRs

**受入基準**:
```typescript
// 調査結果のEARS変換チェック
const earsFindings = await convertToEARS(report.findings);
expect(earsFindings.every(f => isValidEARS(f))).toBe(true);

// トレーサビリティID付与チェック
expect(report.metadata.researchId).toMatch(/^REQ-DR-\d{4}-\d{2}-\d{2}-\d{3}$/);

// ADR生成推奨
if (report.recommendations.some(r => r.type === 'technology-choice')) {
  console.warn('⚠️ Technology decisions detected. Create ADR with:');
  console.warn('   npx musubix design adr <decision>');
}
```

**実装パッケージ**: `packages/deep-research/src/compliance/constitution-checker.ts`  
**トレーサビリティ**: DES-DR-INT-009, TSK-DR-INT-009

---

## 4. 非機能要件（NFR）

### 4.1 パフォーマンス

#### REQ-DR-NFR-001: レスポンス時間
**優先度**: P0  
**パターン**: Ubiquitous

THE system SHALL complete simple research queries (1-3 iterations) within:
- 30 seconds for single-page research
- 2 minutes for multi-page research (≤5 URLs)
- 5 minutes for complex research (≤10 URLs)

**受入基準**:
```typescript
const startTime = Date.now();
const result = await deepResearch('What is TypeScript?', {
  maxIterations: 3,
});
const duration = Date.now() - startTime;

expect(duration).toBeLessThan(120_000);  // 2 minutes
expect(result.metadata.iterations).toBeLessThanOrEqual(3);
```

**実装パッケージ**: `packages/deep-research/src/performance/`  
**トレーサビリティ**: DES-DR-NFR-001, TSK-DR-NFR-001

---

#### REQ-DR-NFR-002: 並列処理
**優先度**: P1  
**パターン**: Ubiquitous

THE system SHALL support parallel operations for:
- Multiple URL readings (up to 5 concurrent)
- Batch search queries (when using orchestrator)
- Citation extraction (parallel processing)

**受入基準**:
```typescript
// 複数URLの並列読取
const urls = ['url1', 'url2', 'url3', 'url4', 'url5'];
const startTime = Date.now();
const results = await Promise.all(
  urls.map(url => readUrl(url))
);
const duration = Date.now() - startTime;

// 並列実行により高速化されている
expect(duration).toBeLessThan(urls.length * 5000);  // 5秒/URL以下
```

**実装パッケージ**: `packages/deep-research/src/performance/parallel-executor.ts`  
**トレーサビリティ**: DES-DR-NFR-002, TSK-DR-NFR-002

---

### 4.2 セキュリティ

#### REQ-DR-NFR-003: APIキー管理
**優先度**: P0  
**パターン**: Unwanted

THE system SHALL NOT expose API keys in:
- Log output
- Error messages
- Research reports
- Trajectory logs

**受入基準**:
```typescript
// APIキーがログに出力されないことを確認
process.env.JINA_API_KEY = 'jina_secret123';

const result = await deepResearch('test query');
const logs = captureLogs();

expect(logs).not.toContain('jina_secret123');
expect(result.report.toString()).not.toContain('jina_secret123');

// エラー時も漏洩しない
try {
  await searchWithInvalidKey();
} catch (error) {
  expect(error.message).not.toContain(process.env.JINA_API_KEY);
}
```

**実装パッケージ**: `packages/deep-research/src/security/api-key-sanitizer.ts`  
**トレーサビリティ**: DES-DR-NFR-003, TSK-DR-NFR-003

---

#### REQ-DR-NFR-004: コンテンツサニタイゼーション
**優先度**: P1  
**パターン**: Ubiquitous

THE system SHALL sanitize web content before processing:
- Remove malicious scripts
- Validate URL schemes (http/https only)
- Filter sensitive patterns (API keys, passwords, tokens)

**受入基準**:
```typescript
const maliciousContent = '<script>alert("XSS")</script><p>Safe content</p>';
const sanitized = sanitizeContent(maliciousContent);

expect(sanitized).not.toContain('<script>');
expect(sanitized).toContain('Safe content');

// URLスキーム検証
expect(() => readUrl('javascript:alert(1)')).toThrow();
expect(() => readUrl('file:///etc/passwd')).toThrow();
```

**実装パッケージ**: `packages/deep-research/src/security/content-sanitizer.ts`  
**トレーサビリティ**: DES-DR-NFR-004, TSK-DR-NFR-004

---

### 4.3 信頼性

#### REQ-DR-NFR-005: エラーハンドリング
**優先度**: P0  
**パターン**: Event-Driven

WHEN API calls fail, THE system SHALL:
- Retry with exponential backoff (3 attempts max)
- Fall back to alternative provider
- Log detailed error information
- Continue research with partial results

**受入基準**:
```typescript
// API失敗時のリトライ
const mockAPI = jest.fn()
  .mockRejectedValueOnce(new Error('Timeout'))
  .mockRejectedValueOnce(new Error('Rate limit'))
  .mockResolvedValueOnce({ results: [] });

const result = await searchWithRetry('query', mockAPI);

expect(mockAPI).toHaveBeenCalledTimes(3);
expect(result).toBeDefined();

// フォールバック動作
process.env.SEARCH_PROVIDER = 'jina';
jinaAPI.mockRejectedValue(new Error('Jina down'));

const fallbackResult = await search('query');
// Braveにフォールバック
expect(fallbackResult.provider).toBe('brave');
```

**実装パッケージ**: `packages/deep-research/src/reliability/error-handler.ts`  
**トレーサビリティ**: DES-DR-NFR-005, TSK-DR-NFR-005

---

#### REQ-DR-NFR-006: 進捗永続化
**優先度**: P2  
**パターン**: State-Driven

WHILE research is running, THE system SHALL persist progress to allow:
- Resume after interruption
- Incremental result viewing
- Cancellation without losing partial results

**受入基準**:
```typescript
const research = await deepResearch.start('complex query');

// 進捗保存確認
const checkpoint = await research.getCheckpoint();
expect(checkpoint.iteration).toBeGreaterThan(0);
expect(checkpoint.findings.length).toBeGreaterThan(0);

// 中断して再開
research.interrupt();
const resumed = await deepResearch.resume(checkpoint.id);

expect(resumed.iteration).toBe(checkpoint.iteration);
expect(resumed.findings).toEqual(checkpoint.findings);
```

**実装パッケージ**: `packages/deep-research/src/persistence/checkpoint-manager.ts`  
**トレーサビリティ**: DES-DR-NFR-006, TSK-DR-NFR-006

---

## 5. トレーサビリティマトリクス

### 5.1 要件マトリクス

| 要件ID | 優先度 | 設計ID | タスクID | テストID | ステータス |
|--------|--------|--------|----------|----------|-----------|
| REQ-DR-CORE-001 | P0 | DES-DR-001 | TSK-DR-001 | TST-DR-001 | Draft |
| REQ-DR-CORE-002 | P0 | DES-DR-002 | TSK-DR-002 | TST-DR-002 | Draft |
| REQ-DR-CORE-003 | P0 | DES-DR-003 | TSK-DR-003 | TST-DR-003 | Draft |
| REQ-DR-CORE-004 | P0 | DES-DR-004 | TSK-DR-004 | TST-DR-004 | Draft |
| REQ-DR-CORE-005 | P0 | DES-DR-005 | TSK-DR-005 | TST-DR-005 | Draft |
| REQ-DR-CORE-006 | P1 | DES-DR-006 | TSK-DR-006 | TST-DR-006 | Draft |
| REQ-DR-CORE-007 | P1 | DES-DR-007 | TSK-DR-007 | TST-DR-007 | Draft |
| REQ-DR-CORE-008 | P1 | DES-DR-008 | TSK-DR-008 | TST-DR-008 | Draft |
| REQ-DR-CORE-009 | P2 | DES-DR-009 | TSK-DR-009 | TST-DR-009 | Draft |
| REQ-DR-CORE-010 | P2 | DES-DR-010 | TSK-DR-010 | TST-DR-010 | Draft |
| REQ-DR-INT-001 | P0 | DES-DR-INT-001 | TSK-DR-INT-001 | TST-DR-INT-001 | Draft |
| REQ-DR-INT-002 | P0 | DES-DR-INT-002 | TSK-DR-INT-002 | TST-DR-INT-002 | Draft |
| REQ-DR-INT-003 | P0 | DES-DR-INT-003 | TSK-DR-INT-003 | TST-DR-INT-003 | Draft |
| REQ-DR-INT-004 | P1 | DES-DR-INT-004 | TSK-DR-INT-004 | TST-DR-INT-004 | Draft |
| REQ-DR-INT-005 | P1 | DES-DR-INT-005 | TSK-DR-020 | TST-DR-INT-005 | Implemented |
| REQ-DR-INT-006 | P1 | DES-DR-INT-006 | TSK-DR-019 | TST-DR-INT-006 | Implemented |
| REQ-DR-INT-007 | P2 | DES-DR-INT-007 | TSK-DR-INT-007 | TST-DR-INT-007 | Draft |
| REQ-DR-INT-008 | P2 | DES-DR-INT-008 | TSK-DR-INT-008 | TST-DR-INT-008 | Draft |
| REQ-DR-INT-009 | P1 | DES-DR-INT-009 | TSK-DR-INT-009 | TST-DR-INT-009 | Draft |
| REQ-DR-NFR-001 | P0 | DES-DR-NFR-001 | TSK-DR-NFR-001 | TST-DR-NFR-001 | Draft |
| REQ-DR-NFR-002 | P1 | DES-DR-NFR-002 | TSK-DR-NFR-002 | TST-DR-NFR-002 | Draft |
| REQ-DR-NFR-003 | P0 | DES-DR-NFR-003 | TSK-DR-NFR-003 | TST-DR-NFR-003 | Draft |
| REQ-DR-NFR-004 | P1 | DES-DR-NFR-004 | TSK-DR-NFR-004 | TST-DR-NFR-004 | Draft |
| REQ-DR-NFR-005 | P0 | DES-DR-NFR-005 | TSK-DR-NFR-005 | TST-DR-NFR-005 | Draft |
| REQ-DR-NFR-006 | P2 | DES-DR-NFR-006 | TSK-DR-NFR-006 | TST-DR-NFR-006 | Draft |

### 5.2 憲法条項準拠

| 憲法条項 | 該当要件 | 遵守内容 |
|---------|---------|---------|
| Article I: Library-First | REQ-DR-CORE-001〜010 | deep-researchパッケージとして独立実装 |
| Article II: CLI Interface | REQ-DR-INT-006 | `npx musubix deep-research` コマンド提供 |
| Article III: Test-First | 全要件 | 各要件に受入基準テストを定義 |
| Article IV: EARS Format | 全要件 | すべてEARS形式で記述 |
| Article V: Traceability | 全要件 | REQ→DES→TSK→TSTの完全追跡 |
| Article VI: Project Memory | REQ-DR-INT-004 | Knowledge Storeへの保存 |
| Article VII: Design Patterns | DES-DR-xxx | 設計書で明示 |
| Article VIII: Decision Records | REQ-DR-INT-009 | ADR生成推奨 |
| Article IX: Quality Gates | REQ-DR-INT-008 | Workflow Engine統合 |
| Article X: Prerequisites | - | 本要件定義承認後に設計開始 |

### 5.3 既存機能との統合

| 既存パッケージ | 統合要件 | 統合ポイント |
|--------------|---------|------------|
| @nahisaho/musubix-expert-delegation | REQ-DR-INT-001 | 専門家分析への委譲 |
| @nahisaho/musubix-neural-search | REQ-DR-INT-002 | 意味的コード検索 |
| @nahisaho/musubix-agent-orchestrator | REQ-DR-INT-003 | 複雑度分析・タスク分解 |
| @musubix/knowledge | REQ-DR-INT-004 | 調査結果の永続化 |
| @nahisaho/musubix-mcp-server | REQ-DR-INT-005 | MCPツール提供 |
| @nahisaho/musubix-core | REQ-DR-INT-006 | CLIコマンド |
| @nahisaho/musubix-workflow-engine | REQ-DR-INT-008 | フェーズ連携 |

---

## 6. 受入基準サマリー

### 6.1 機能受入基準

✅ **コア機能**:
- [ ] 反復検索サイクルが正常動作（最大10回）
- [ ] 3つの検索プロバイダー（Jina/Brave/DuckDuckGo）が利用可能
- [ ] Web コンテンツ読取（Jina Reader）が正常動作
- [ ] VS Code LM API経由の推論が成功
- [ ] 調査レポートが生成される（引用付き）

✅ **統合機能**:
- [ ] expert-delegation統合（EARS分析等）
- [ ] neural-search統合（ローカル検索）
- [ ] agent-orchestrator統合（複雑度分析）
- [ ] knowledge store統合（結果保存）
- [ ] MCPツール3種が利用可能

✅ **CLI**:
- [ ] `npx musubix deep-research <query>` が動作
- [ ] `--max-iterations`, `--token-budget` オプションが有効
- [ ] 進捗がリアルタイム表示される
- [ ] レポートが `storage/research/` に保存される

### 6.2 非機能受入基準

✅ **パフォーマンス**:
- [ ] 単純クエリ: 30秒以内
- [ ] 中規模クエリ: 2分以内
- [ ] 複雑クエリ: 5分以内
- [ ] 並列URL読取（5並列）が動作

✅ **セキュリティ**:
- [ ] APIキーがログに出力されない
- [ ] コンテンツサニタイゼーションが動作
- [ ] 不正なURLスキームが拒否される

✅ **信頼性**:
- [ ] API失敗時のリトライが動作（3回）
- [ ] フォールバック機能が動作
- [ ] 進捗チェックポイントが保存される

### 6.3 テストカバレッジ目標

| カテゴリ | 目標カバレッジ | 最小テスト数 |
|---------|---------------|-------------|
| CORE機能 | 90% | 50+ |
| INT統合 | 85% | 30+ |
| NFR非機能 | 80% | 20+ |
| **合計** | **85%** | **100+** |

---

## 7. 要件サマリー

### 7.1 優先度別カウント

| 優先度 | CORE | INT | NFR | 合計 |
|--------|------|-----|-----|------|
| P0 | 5 | 3 | 3 | **11** |
| P1 | 3 | 5 | 2 | **10** |
| P2 | 2 | 1 | 1 | **4** |
| **合計** | **10** | **9** | **6** | **25** |

### 7.2 EARS パターン分布

| パターン | 使用回数 | 比率 |
|----------|---------|------|
| Ubiquitous | 10 | 40% |
| Event-Driven | 11 | 44% |
| State-Driven | 3 | 12% |
| Unwanted | 1 | 4% |
| Optional | 0 | 0% |
| **合計** | **25** | **100%** |

### 7.3 実装パッケージ一覧

**新規作成**:
- `packages/deep-research/` (メインパッケージ)
  - `src/engine/` - コアエンジン
  - `src/providers/` - 検索プロバイダー
  - `src/readers/` - Web読取
  - `src/reasoning/` - LM推論
  - `src/reporters/` - レポート生成
  - `src/citations/` - 引用管理
  - `src/knowledge/` - 知識蓄積
  - `src/integrations/` - 既存機能統合
  - `src/security/` - セキュリティ
  - `src/performance/` - パフォーマンス
  - `src/utils/` - ユーティリティ

**拡張**:
- `packages/core/src/cli/commands/deep-research.ts` - CLIコマンド（TSK-DR-019実装済み）
- `packages/deep-research/src/mcp/` - MCPツール本体（TSK-DR-020実装済み）
- `packages/mcp-server/src/tools/` - MCPツール登録（将来実装）
- `packages/workflow-engine/src/quality-gates/research-recommender.ts` - 推奨機能

### 7.4 依存関係

```
packages/deep-research/
  ├─ @nahisaho/musubix-expert-delegation (v3.2.0+)
  ├─ @nahisaho/musubix-neural-search (v2.2.0+)
  ├─ @nahisaho/musubix-agent-orchestrator (v2.4.0+)
  ├─ @musubix/knowledge (v3.0.0+)
  ├─ @ai-sdk/core (for VS Code LM API)
  ├─ axios (HTTP client)
  └─ marked (Markdown parsing)
```

---

## 8. 次ステップ

### 8.1 Phase 1完了条件

- [x] 要件定義書作成（本文書）
- [x] セルフレビュー実施（2回完了）
- [x] ユーザー承認取得 ✅ **2026-01-16承認**

### 8.2 Phase 2: 設計

承認後に以下を実施:
1. C4モデル設計書作成（DES-DR-v3.4.0.md）
2. APIインターフェース設計
3. データモデル設計
4. アーキテクチャ図作成

### 8.3 Phase 3: タスク分解

設計承認後に以下を実施:
1. 実装タスク分解（TSK-DR-001〜xxx）
2. テストケース定義（TST-DR-001〜xxx）
3. 工数見積もり
4. スプリント計画

### 8.4 Phase 4: 実装

タスク分解承認後に実施（Article X遵守）

---

## 9. 変更履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 1.0 | 2026-01-16 | 初版作成（25要件定義） | GitHub Copilot |
| 1.1 | 2026-01-16 | CLIコマンド名・MCPツール定義修正 | GitHub Copilot |
| 1.2 | 2026-01-16 | トレーサビリティ・実装ステータス更新 | GitHub Copilot |
| 1.3 | 2026-01-16 | ✅ **ユーザー承認取得・Phase 1完了** | User + GitHub Copilot |

---

**レビュー待ち** ✋  
次のアクション: セルフレビュー実施

