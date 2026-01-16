# @nahisaho/musubix-deep-research

Deep Research Integration for MUSUBIX - Iterative search-read-reason cycle for AI agents during requirements and design phases.

## Features

- 🔄 **Iterative Research Cycle**: Search → Read → Reason → Reflect loop
- 🔍 **Multi-Provider Search**: Jina AI (primary), Brave (fallback 1), DuckDuckGo (fallback 2)
- 🧠 **LM API Integration**: VS Code LM API (GitHub Copilot) for reasoning
- 📚 **Knowledge Accumulation**: Persistent knowledge base across iterations
- 💰 **Token Budget Management**: Automatic tracking and limits
- 📊 **Research Reports**: Markdown/JSON formatted reports with citations

## Installation

```bash
npm install @nahisaho/musubix-deep-research
```

## Usage

### CLI

```bash
# Start deep research
npx musubix deep-research "How to implement authentication in TypeScript?"

# With options
npx musubix deep-research "TypeScript decorators" \
  --max-iterations 5 \
  --token-budget 10000 \
  --output report.md
```

### Programmatic API

```typescript
import { ResearchEngine, ResearchConfig } from '@nahisaho/musubix-deep-research';

const config: ResearchConfig = {
  query: 'How to implement authentication in TypeScript?',
  maxIterations: 10,
  tokenBudget: 15000,
  providers: {
    jinaApiKey: process.env.JINA_API_KEY,
    braveApiKey: process.env.BRAVE_API_KEY,
  },
};

const engine = new ResearchEngine(config);
const report = await engine.research();

console.log(report.summary);
console.log(`Found ${report.findings.length} findings`);
```

## Architecture

Based on **Template Method Pattern** (ADR-v3.4.0-001):

```
ResearchEngine (Template Method)
  ├─ initialize()
  ├─ while (!shouldStop())
  │   ├─ generateQuestions()  → LMReasoning
  │   ├─ search()             → SearchProviderFactory
  │   ├─ read()               → JinaProvider.read()
  │   ├─ reason()             → LMReasoning
  │   └─ logIteration()       → TrajectoryLogger
  └─ generateReport()         → ReportGenerator
```

## Requirements

- Node.js >= 20.0.0
- npm >= 10.0.0
- VS Code with GitHub Copilot (for LM API)
- Jina AI API Key (recommended)

## License

MIT

## Documentation

- [Requirements](../../storage/specs/REQ-MUSUBIX-v3.4.0.md)
- [Design](../../storage/design/DES-DR-v3.4.0.md)
- [ADRs](../../docs/adr/)
- [Tasks](../../storage/tasks/TSK-DR-v3.4.0.md)
