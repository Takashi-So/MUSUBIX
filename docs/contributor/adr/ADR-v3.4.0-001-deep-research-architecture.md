# ADR-v3.4.0-001: Deep Research Architecture Decision

**Status**: Accepted  
**Date**: 2026-01-16  
**Authors**: AI Agent  
**Context**: MUSUBIX v3.4.0 Deep Research Integration  
**Traces To**: REQ-DR-CORE-001, DES-DR-v3.4.0

---

## Context

MUSUBIX v3.4.0でDeep Research機能を追加するにあたり、以下の技術的決定が必要となった：

1. **アーキテクチャパターン**: どのように反復的調査サイクルを実現するか
2. **既存システム統合**: 7つの既存パッケージとどのように統合するか
3. **状態管理**: イテレーション間の知識をどのように蓄積・管理するか

### 要件からの制約

- REQ-DR-CORE-001: 最大10イテレーションの反復サイクル
- REQ-DR-INT-001〜009: 7パッケージとのシームレス統合必須
- 憲法Article I: Library-First（独立パッケージとして実装）
- 憲法Article V: 完全なトレーサビリティ

---

## Decision

**Template Method Pattern**を中心としたアーキテクチャを採用する。

### 採用パターン

```typescript
// ResearchEngine: Template Method Pattern
class ResearchEngine {
  async research(): Promise<ResearchReport> {
    this.initialize();
    
    while (!this.shouldStop()) {
      // 固定フロー（Template Method）
      const questions = await this.generateQuestions();
      const searchResults = await this.search(questions);
      const contents = await this.read(searchResults);
      const knowledge = await this.reason(contents);
      
      this.knowledge.addAll(knowledge);
      this.iteration++;
      
      if (await this.isAnswerDefinitive()) {
        break;
      }
    }
    
    return this.generateReport();
  }
  
  // フックメソッド（拡張可能）
  protected async generateQuestions(): Promise<ReflectiveQuestion[]> { /* ... */ }
  protected async search(questions: ReflectiveQuestion[]): Promise<SearchResult[]> { /* ... */ }
  protected async read(results: SearchResult[]): Promise<WebContent[]> { /* ... */ }
  protected async reason(contents: WebContent[]): Promise<KnowledgeItem[]> { /* ... */ }
}
```

### アーキテクチャレイヤー

```
┌─────────────────────────────────────────────────────┐
│ CLI / MCP Tools (Interface Layer)                  │
│ - deepResearchCommand()                             │
│ - deep_research_start tool                          │
├─────────────────────────────────────────────────────┤
│ ResearchEngine (Application Layer)                  │
│ - Template Method: research()                       │
│ - State Management: KnowledgeBase                   │
├─────────────────────────────────────────────────────┤
│ Core Services (Domain Layer)                        │
│ - SearchProviderFactory (Strategy)                  │
│ - LMReasoning (Adapter)                             │
│ - ReportGenerator (Builder)                         │
├─────────────────────────────────────────────────────┤
│ Integrations (Infrastructure Layer)                 │
│ - ExpertIntegration                                 │
│ - KnowledgeStoreIntegration                         │
│ - WorkflowIntegration                               │
└─────────────────────────────────────────────────────┘
```

---

## Rationale

### なぜTemplate Method Patternか

**✅ 採用理由**:

1. **固定フローの明確化**: search → read → reason → evaluateの順序が不変
2. **拡張性**: 各ステップをフックメソッドとして実装し、サブクラスで拡張可能
3. **トレーサビリティ**: 各ステップが明示的で、ログ・デバッグが容易
4. **テスト容易性**: 各フックメソッドを独立してテスト可能

**比較した代替案**:

| パターン | メリット | デメリット | 判定 |
|---------|---------|-----------|------|
| **Template Method** | フロー固定、拡張可能 | 継承ベース | ✅ 採用 |
| **Strategy Pattern** | 柔軟な切り替え | フロー全体を切り替える必要 | ❌ 不適 |
| **Pipeline Pattern** | 関数型、シンプル | エラーハンドリングが複雑 | ❌ 不適 |
| **State Machine** | 状態遷移明確 | オーバーエンジニアリング | ❌ 不適 |

### 既存システム統合戦略

**Adapter + Bridge Pattern**で統合：

```typescript
// Adapter Pattern: 外部システムの抽象化
class ExpertIntegration {
  constructor(private delegation: DelegationEngine) {}
  
  async convertToEARS(finding: string): Promise<string> {
    return (await this.delegation.delegate({ ... })).content;
  }
}

// Bridge Pattern: 実装の切り替え
interface KnowledgePersistence {
  save(item: KnowledgeItem): Promise<void>;
}

class InMemoryPersistence implements KnowledgePersistence { /* ... */ }
class KnowledgeStorePersistence implements KnowledgePersistence { /* ... */ }
```

### 状態管理: KnowledgeBase

**Repository Pattern**でデータアクセスを抽象化：

```typescript
class KnowledgeBase {
  private items: Map<string, KnowledgeItem> = new Map();
  private iterationIndex: Map<number, string[]> = new Map();
  
  add(item: KnowledgeItem): void { /* ... */ }
  getFindings(): KnowledgeItem[] { /* ... */ }
  getByIteration(iteration: number): KnowledgeItem[] { /* ... */ }
}
```

**将来の永続化移行が容易**:
- 現在: In-Memory (Map)
- 将来: @musubix/knowledge統合 → JSON永続化
- 将来: Database統合 → PostgreSQL/MongoDB

---

## Consequences

### Positive

✅ **明確なフロー**: research()メソッドでイテレーションロジックが一目瞭然  
✅ **拡張性**: 各フックメソッドをオーバーライドして特定ドメインに特化可能  
✅ **テスト容易性**: 各ステップを独立してMock/Stubでテスト  
✅ **トレーサビリティ**: 各イテレーションでログ出力、デバッグ容易  
✅ **憲法準拠**: Library-First、Design Patterns適用

### Negative

⚠️ **継承の制約**: Template Methodは継承ベースなので、多重継承不可  
⚠️ **フック数**: フックメソッドが増えすぎると保守性低下  
⚠️ **状態管理**: KnowledgeBaseが肥大化する可能性

### Mitigations

- **Composition over Inheritance**: 必要に応じてStrategyパターンと組み合わせ
- **フック数制限**: 5フックメソッド（generate, search, read, reason, evaluate）に限定
- **KnowledgeBase分割**: イテレーション数が50を超える場合は永続化層に移行

---

## Compliance

### 憲法準拠

| 条項 | 準拠状況 |
|-----|---------|
| I. Library-First | ✅ packages/deep-research/ |
| V. Traceability | ✅ 各コンポーネントにREQ-ID紐付け |
| VII. Design Patterns | ✅ Template Method, Strategy, Adapter等適用 |

### SOLID原則

| 原則 | 適用 |
|------|------|
| **S**RP | ✅ ResearchEngine（調整）、KnowledgeBase（データ）、ReportGenerator（出力）で分離 |
| **O**CP | ✅ フックメソッドで拡張、Template Method本体は変更不要 |
| **L**SP | ✅ サブクラスでフックメソッドをオーバーライド可能 |
| **I**SP | ✅ 各インターフェースは単一責任（SearchProvider、LMProvider等） |
| **D**IP | ✅ 抽象（インターフェース）に依存、具象クラスに依存しない |

---

## References

- [Design Patterns: Elements of Reusable Object-Oriented Software](https://en.wikipedia.org/wiki/Design_Patterns) - Template Method Pattern
- [jina-ai/node-DeepResearch](https://github.com/jina-ai/node-DeepResearch) - 参照実装
- REQ-MUSUBIX-v3.4.0.md - 要件定義書
- DES-DR-v3.4.0.md - 設計書
- steering/structure.ja.md - プロジェクト構造

---

## Approval

- **Author**: AI Agent (2026-01-16)
- **Reviewer**: -
- **Status**: Accepted
