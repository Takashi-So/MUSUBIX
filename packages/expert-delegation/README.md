# @nahisaho/musubix-expert-delegation

Expert Delegation System for MUSUBIX - VS Code Language Model API based AI expert delegation.

## Overview

This package provides an intelligent expert delegation system that routes AI tasks to specialized experts based on context detection. It integrates with VS Code's Language Model API (GitHub Copilot) to provide high-quality AI assistance.

## Features

- **7 Specialized Experts**
  - Architect: System design, patterns, architecture decisions
  - Security Analyst: Vulnerability detection, security review
  - Code Reviewer: Code quality, best practices, refactoring
  - Plan Reviewer: Design validation, constitution compliance
  - EARS Analyst: Requirements analysis, EARS format conversion (MUSUBIX)
  - Formal Verifier: Z3/Lean4 verification, Hoare logic (MUSUBIX)
  - Ontology Reasoner: Knowledge graph, inference (MUSUBIX)

- **Semantic Routing**: Automatic expert detection based on message content
- **Proactive Delegation**: Auto-suggest security reviews, EARS conversion
- **11 MCP Tools**: Full Model Context Protocol integration
- **Advisory & Implementation Modes**: Read-only analysis or code generation
- **Retry & Escalation**: Exponential backoff, expert escalation

## Installation

```bash
npm install @nahisaho/musubix-expert-delegation
```

## Quick Start

```typescript
import {
  createDelegationEngine,
  createVSCodeLMProvider,
} from '@nahisaho/musubix-expert-delegation';

// Create provider (VS Code extension context)
const provider = createVSCodeLMProvider(vscodeContext);

// Create delegation engine
const engine = createDelegationEngine(provider);

// Simple delegation (auto-detect expert)
const result = await engine.delegateSimple(
  'How should I structure my authentication system?'
);
console.log(result.content);
// → Architect expert provides design recommendations

// Explicit expert delegation
const securityResult = await engine.analyze(
  'Check this code for vulnerabilities',
  'security-analyst'
);
```

## MCP Tools

| Tool | Description |
|------|-------------|
| `expert_delegate` | Generic delegation with auto/explicit expert |
| `expert_architect` | Architecture design delegation |
| `expert_security` | Security analysis delegation |
| `expert_review` | Code review delegation |
| `expert_plan` | Plan review with constitution check |
| `expert_ears` | EARS requirements conversion |
| `expert_formal` | Formal verification (Z3/Lean4) |
| `expert_ontology` | Ontology reasoning |
| `trigger_detect` | Detect matching expert |
| `delegation_retry` | Retry failed delegation |
| `provider_select` | Select/configure LLM provider |

## Execution Modes

### Advisory Mode (Default)
Read-only analysis without code generation:
```typescript
const result = await engine.analyze('Review this architecture');
// Returns analysis, recommendations, risks
```

### Implementation Mode
Code generation with traceability:
```typescript
const result = await engine.generate(
  'Create a user authentication service',
  'architect'
);
// Returns code with // Traces to: REQ-XXX comments
```

## Expert Selection

### Automatic (Semantic Routing)
```typescript
// Message analyzed for trigger patterns
const result = await engine.delegateSimple('Check security vulnerabilities');
// → Routed to security-analyst (detected "security", "vulnerabilities")
```

### Explicit
```typescript
const result = await engine.delegateSimple('Do something', {
  expertType: 'formal-verifier',
  mode: 'advisory',
});
```

## Proactive Delegation

```typescript
import { createProactiveDelegation } from '@nahisaho/musubix-expert-delegation';

const proactive = createProactiveDelegation();

// Detect security patterns in code
const patterns = proactive.detectSecurityPattern(code);
// → [{ pattern: 'SQL Injection', severity: 'high' }]

// Detect non-EARS requirements
const nonEars = proactive.detectNonEarsRequirement('The system must...');
// → { suggestedPattern: 'ubiquitous', confidence: 0.7 }

// Get delegation suggestions
const suggestions = proactive.suggestDelegation(code, requirements);
// → [{ expert: 'security-analyst', reason: '...', priority: 90 }]
```

## Retry & Escalation

```typescript
import { createRetryHandler } from '@nahisaho/musubix-expert-delegation';

const handler = createRetryHandler({
  maxRetries: 3,
  initialDelayMs: 1000,
  backoffMultiplier: 2,
});

// Execute with automatic retry
const result = await handler.executeWithRetry(
  () => engine.delegate(task),
  'task-123'
);

// Check escalation path
const escalation = handler.getEscalationTarget('security-analyst');
// → { shouldEscalate: true, targetExpert: 'architect' }
```

## Constitution Compliance

The engine validates tasks against MUSUBIX 10 Constitutional Articles:

```typescript
const engine = createDelegationEngine(provider, undefined, {
  enableConstitutionCheck: true,
  enforceTraceability: true,
});

// Implementation without requirements → Blocked (Article X)
const result = await engine.delegate({
  mode: 'implementation',
  context: { userMessage: 'Generate code' }, // No requirements!
});
// → success: false, constitutionViolations: [Article X]
```

## Testing

```typescript
import {
  MockVSCodeLMProvider,
  createTestTask,
  createTestContext,
} from '@nahisaho/musubix-expert-delegation/test';

const mockProvider = new MockVSCodeLMProvider();
mockProvider.setDefaultResponse({
  content: 'Mock analysis result',
  finishReason: 'stop',
});

const engine = createDelegationEngine(mockProvider);
const result = await engine.analyze('Test message');
```

## API Reference

See [API Documentation](./docs/api.md) for detailed API reference.

## Requirements

- Node.js >= 20.0.0
- VS Code with GitHub Copilot (for VS Code LM API)

## License

MIT

## Related Packages

- `@nahisaho/musubix-core` - Core MUSUBIX functionality
- `@nahisaho/musubix-formal-verify` - Formal verification (Z3, Lean4)
- `@nahisaho/musubix-ontology-mcp` - Ontology reasoning
