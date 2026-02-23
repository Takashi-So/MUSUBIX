# ADR-v3.4.0-003: LM API Integration Strategy

**Status**: Accepted  
**Date**: 2026-01-16  
**Authors**: AI Agent  
**Context**: MUSUBIX v3.4.0 Deep Research Integration  
**Traces To**: REQ-DR-CORE-004, REQ-DR-INT-001, DES-DR-v3.4.0

---

## Context

Deep Research機能では、Web検索結果を推論・分析してナレッジを抽出する必要がある。以下の技術的決定が必要：

1. **LM API選択**: どのLLM APIを使用するか
2. **統合方法**: VS Code Extension APIとの統合方法
3. **Expert Delegation統合**: 既存の@nahisaho/musubix-expert-delegation (v3.2.0+) の活用

### 要件からの制約

- REQ-DR-CORE-004: LM APIによる推論・評価・質問生成
- REQ-DR-INT-001: Expert Delegation統合（EARS変換、設計レビュー等）
- 憲法Article II: CLI Interface必須
- VS Code環境: GitHub Copilot via LM API使用

---

## Decision

**VS Code LM API**（Language Model API）を直接使用し、**Expert Delegation**をラッパーとして活用する2層構造を採用。

### アーキテクチャ

```
┌─────────────────────────────────────────────────────┐
│ Deep Research (Application Layer)                   │
│ - LMReasoning                                       │
│ - QuestionGenerator                                 │
│ - AnswerEvaluator                                   │
└────────────────┬────────────────────────────────────┘
                 │
                 ↓
┌─────────────────────────────────────────────────────┐
│ Expert Delegation (Middleware Layer)                │
│ - DelegationEngine.delegate()                       │
│ - ExpertManager (7 specialists)                     │
│ - VSCodeLMProvider                                  │
└────────────────┬────────────────────────────────────┘
                 │
                 ↓
┌─────────────────────────────────────────────────────┐
│ VS Code LM API (Platform Layer)                     │
│ - vscode.lm.selectChatModels()                      │
│ - model.sendRequest()                               │
└─────────────────────────────────────────────────────┘
```

### 実装戦略

```typescript
// src/reasoning/lm-reasoning.ts

import { DelegationEngine } from '@nahisaho/musubix-expert-delegation';
import * as vscode from 'vscode';

export class LMReasoning {
  constructor(
    private lmProvider: VSCodeLMProvider,
    private expertDelegation: DelegationEngine
  ) {}
  
  /**
   * 反射的質問生成
   * REQ-DR-CORE-009
   */
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
    
    // 直接LM APIを使用
    const response = await this.lmProvider.generateText({
      messages: [{ role: 'user', content: prompt }],
      maxTokens: 500,
    });
    
    return JSON.parse(response.text);
  }
  
  /**
   * 回答評価
   * REQ-DR-CORE-004
   */
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
    
    // 直接LM APIを使用
    const response = await this.lmProvider.generateText({
      messages: [{ role: 'user', content: prompt }],
      maxTokens: 300,
    });
    
    return JSON.parse(response.text);
  }
  
  /**
   * EARS変換（Expert Delegation経由）
   * REQ-DR-INT-001, REQ-DR-INT-009
   */
  async convertToEARS(finding: Finding): Promise<string> {
    // Expert Delegationを使用
    const result = await this.expertDelegation.delegate({
      prompt: `Convert to EARS format: ${finding.statement}`,
      expertType: 'ears-analyst',
      mode: 'advisory',
    });
    
    return result.content;
  }
}
```

---

## Rationale

### なぜVS Code LM APIを直接使用するか

**✅ 採用理由**:

1. **GitHub Copilot統合**: VS Code環境でCopilotを直接利用可能
2. **ゼロコスト**: 追加のAPI Key不要（Copilotライセンス内）
3. **既存インフラ活用**: Expert Delegationが既にVS Code LM APIをラップ済み
4. **モデル選択柔軟性**: `selectChatModels()`でモデル切り替え可能

**VS Code LM API例**:
```typescript
import * as vscode from 'vscode';

const models = await vscode.lm.selectChatModels({
  vendor: 'copilot',
  family: 'gpt-4',
});

const model = models[0];
const response = await model.sendRequest(
  [{ role: vscode.LanguageModelChatMessageRole.User, content: prompt }],
  { maxTokens: 500 },
  token
);
```

### LM Provider比較

| プロバイダー | 長所 | 短所 | 判定 |
|-------------|------|------|------|
| **VS Code LM API** | Copilot統合、API Key不要 | VS Code環境依存 | ✅ 採用 |
| **OpenAI API** | 高品質、独立動作 | ❌ 有料、API Key管理必要 | ❌ 不採用 |
| **Azure OpenAI** | エンタープライズ対応 | ❌ 有料、Azure依存 | ❌ 不採用 |
| **Anthropic Claude** | 長文対応 | ❌ 有料、API Key管理必要 | ❌ 不採用 |
| **Ollama (Local)** | プライバシー、無料 | ❌ GPU必要、品質低い | ❌ 不採用 |

### Expert Delegationの役割

**既存パッケージを活用**して以下の機能を委譲：

| 機能 | Expert Type | 用途 |
|------|------------|------|
| **EARS変換** | `ears-analyst` | 調査結果をEARS形式要件に変換 |
| **設計レビュー** | `design-reviewer` | 生成した設計のSOLID準拠チェック |
| **セキュリティ分析** | `security-analyst` | 調査結果からセキュリティリスク検出 |
| **アーキテクチャ分析** | `architect` | 技術選択肢の評価 |

**Adapter Pattern**で統合：

```typescript
// src/integrations/expert-integration.ts

export class ExpertIntegration {
  constructor(private delegation: DelegationEngine) {}
  
  async convertToEARS(finding: string): Promise<string> {
    const result = await this.delegation.delegate({
      prompt: `Convert to EARS format: ${finding}`,
      expertType: 'ears-analyst',
      mode: 'advisory',
    });
    return result.content;
  }
  
  async reviewDesign(designDoc: string): Promise<string> {
    const result = await this.delegation.delegate({
      prompt: `Review this design for SOLID principles: ${designDoc}`,
      expertType: 'design-reviewer',
      mode: 'advisory',
    });
    return result.content;
  }
  
  async analyzeSecurityRisks(findings: Finding[]): Promise<SecurityAnalysis> {
    const result = await this.delegation.delegate({
      prompt: `Analyze security risks: ${JSON.stringify(findings)}`,
      expertType: 'security-analyst',
      mode: 'advisory',
    });
    return JSON.parse(result.content);
  }
}
```

---

## Consequences

### Positive

✅ **ゼロコスト**: GitHub Copilotライセンス内で動作  
✅ **既存資産活用**: Expert Delegation (v3.2.0+) をそのまま利用  
✅ **テスト容易性**: VSCodeLMProviderをMockして単体テスト可能  
✅ **専門知識**: 7種のExpertタイプで高品質な分析

### Negative

⚠️ **VS Code依存**: CLI実行時もVS Code環境が必要  
⚠️ **モデル制限**: Copilotが提供するモデルに限定  
⚠️ **トークン制限**: Copilotの利用制限に準拠

### Mitigations

- **VS Code依存**:
  - CLIは`npx`でVS Code Extension Hostから実行
  - 将来的にはOpenAI APIへのフォールバック実装
- **モデル制限**:
  - `selectChatModels()`でGPT-4を優先選択
  - 利用不可時はGPT-3.5へフォールバック
- **トークン制限**:
  - TokenTrackerで予算管理（REQ-DR-CORE-006）
  - 予算80%消費時に警告

---

## Implementation Details

### VSCodeLMProviderラッパー

```typescript
// src/providers/vscode-lm-provider.ts

import * as vscode from 'vscode';

export interface LMProvider {
  generateText(request: LMRequest): Promise<LMResponse>;
}

export interface LMRequest {
  messages: { role: string; content: string }[];
  maxTokens: number;
  temperature?: number;
}

export interface LMResponse {
  text: string;
  tokensUsed: number;
  model: string;
}

export class VSCodeLMProvider implements LMProvider {
  private modelSelector: { vendor: string; family: string };
  
  constructor(modelSelector = { vendor: 'copilot', family: 'gpt-4' }) {
    this.modelSelector = modelSelector;
  }
  
  async generateText(request: LMRequest): Promise<LMResponse> {
    // モデル選択
    const models = await vscode.lm.selectChatModels(this.modelSelector);
    
    if (models.length === 0) {
      throw new Error('No LM models available');
    }
    
    const model = models[0];
    
    // メッセージ変換
    const messages = request.messages.map(msg => 
      new vscode.LanguageModelChatMessage(
        msg.role === 'user' 
          ? vscode.LanguageModelChatMessageRole.User 
          : vscode.LanguageModelChatMessageRole.Assistant,
        msg.content
      )
    );
    
    // リクエスト送信
    const response = await model.sendRequest(
      messages,
      { maxTokens: request.maxTokens, temperature: request.temperature },
      new vscode.CancellationTokenSource().token
    );
    
    // レスポンス収集
    let text = '';
    for await (const chunk of response.text) {
      text += chunk;
    }
    
    return {
      text,
      tokensUsed: this.estimateTokens(text),
      model: model.name,
    };
  }
  
  private estimateTokens(text: string): number {
    // 簡易推定: 4文字 = 1トークン
    return Math.ceil(text.length / 4);
  }
}
```

### トークン予算管理

```typescript
// src/utils/token-tracker.ts

export class TokenTracker {
  private usages: TokenUsage[] = [];
  private budget: number;
  private warningEmitted = false;
  
  constructor(budget: number) {
    this.budget = budget;
  }
  
  trackUsage(operation: string, tokens: number): void {
    this.usages.push({ operation, tokens, timestamp: Date.now() });
    
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
}
```

---

## Compliance

### 要件準拠

| 要件ID | 対応 |
|--------|------|
| REQ-DR-CORE-004 | ✅ LM APIで推論・評価実装 |
| REQ-DR-CORE-006 | ✅ TokenTrackerで予算管理 |
| REQ-DR-INT-001 | ✅ Expert Delegation統合 |

### 憲法準拠

| 条項 | 対応 |
|-----|------|
| II. CLI Interface | ✅ CLIから実行可能 |
| VII. Design Patterns | ✅ Adapter, Strategy適用 |

---

## Testing Strategy

### Mock LM Provider

```typescript
// src/test/mocks/mock-lm-provider.ts

export class MockLMProvider implements LMProvider {
  private responses: Map<string, string> = new Map();
  
  setResponse(prompt: string, response: string): void {
    this.responses.set(prompt, response);
  }
  
  async generateText(request: LMRequest): Promise<LMResponse> {
    const prompt = request.messages[0].content;
    const text = this.responses.get(prompt) || '{"default": "response"}';
    
    return {
      text,
      tokensUsed: Math.ceil(text.length / 4),
      model: 'mock-model',
    };
  }
}
```

### テストケース

```typescript
describe('LMReasoning', () => {
  it('should generate reflective questions', async () => {
    const mockProvider = new MockLMProvider();
    mockProvider.setResponse(
      'Original query: ...',
      JSON.stringify([
        { question: 'What is X?', reason: '...', priority: 10 }
      ])
    );
    
    const reasoning = new LMReasoning(mockProvider, expertDelegation);
    const questions = await reasoning.generateQuestions('test', knowledge);
    
    expect(questions).toHaveLength(1);
    expect(questions[0].question).toBe('What is X?');
  });
});
```

---

## References

- [VS Code Language Model API](https://code.visualstudio.com/api/extension-guides/language-model)
- [GitHub Copilot Extensions](https://github.com/features/copilot)
- [@nahisaho/musubix-expert-delegation](../../packages/expert-delegation/README.md)
- REQ-MUSUBIX-v3.4.0.md - 要件定義書
- DES-DR-v3.4.0.md - 設計書

---

## Approval

- **Author**: AI Agent (2026-01-16)
- **Reviewer**: -
- **Status**: Accepted
