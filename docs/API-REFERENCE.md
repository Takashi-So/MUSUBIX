# MUSUBIX API Reference

> Auto-generated API documentation for MUSUBIX Core Package

## Table of Contents

- [Overview](#overview)
- [Installation](#installation)
- [Quick Start](#quick-start)
- [Core Modules](#core-modules)
  - [Requirements](#requirements)
  - [Design](#design)
  - [Codegen](#codegen)
  - [Validation](#validation)
  - [Utils](#utils)
- [MCP Server](#mcp-server)
- [YATA Client](#yata-client)
- [Types Reference](#types-reference)

---

## Overview

MUSUBIX is a neuro-symbolic AI system combining:
- **MUSUBI**: LLM-powered specification-driven development
- **YATA**: Knowledge graph for contextual reasoning

### Architecture

```
┌─────────────────────────────────────────────┐
│                MUSUBIX Core                  │
├─────────────────────────────────────────────┤
│  Requirements → Design → Tasks → Validation  │
├─────────────────────────────────────────────┤
│         MCP Server (stdio/SSE)               │
├─────────────────────────────────────────────┤
│            YATA Knowledge Graph              │
└─────────────────────────────────────────────┘
```

---

## Installation

```bash
npm install @nahisaho/musubix-core
# or
pnpm add @nahisaho/musubix-core
```

---

## Quick Start

```typescript
import { 
  createRequirementsAnalyzer,
  createC4ModelGenerator,
  createTaskGenerator,
  createConstitutionalValidator
} from '@nahisaho/musubix-core';

// 1. Analyze requirements
const analyzer = createRequirementsAnalyzer();
const analysis = analyzer.analyze(requirementText);

// 2. Generate design
const c4Generator = createC4ModelGenerator();
const diagram = c4Generator.generateContext(systemSpec);

// 3. Create tasks
const taskGenerator = createTaskGenerator();
const tasks = taskGenerator.generate(requirements);

// 4. Validate
const validator = createConstitutionalValidator();
const result = validator.validate(artifact);
```

---

## Core Modules

### Requirements

#### RequirementsAnalyzer

Analyzes and structures requirement specifications.

```typescript
import { createRequirementsAnalyzer } from '@nahisaho/musubix-core';

const analyzer = createRequirementsAnalyzer({
  strictMode: true,
  validateEARS: true
});

// Analyze requirement text
const result = analyzer.analyze(requirementText);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `analyze(text)` | `text: string` | `AnalysisResult` | Analyzes requirement text |
| `validateEARS(req)` | `req: Requirement` | `ValidationResult` | Validates EARS compliance |
| `extractRequirements(text)` | `text: string` | `Requirement[]` | Extracts requirements from text |

**Configuration:**

```typescript
interface AnalyzerConfig {
  strictMode?: boolean;      // Enable strict validation
  validateEARS?: boolean;    // Validate EARS format
  autoClassify?: boolean;    // Auto-classify requirement types
}
```

---

#### RequirementsDecomposer

Decomposes complex requirements into smaller units.

```typescript
import { createRequirementsDecomposer } from '@nahisaho/musubix-core';

const decomposer = createRequirementsDecomposer({
  maxDepth: 4,
  targetUnitSize: 4
});

const result = decomposer.decompose(requirement, 'functional');
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `decompose(req, strategy)` | `req: Requirement, strategy?: DecompositionStrategy` | `DecompositionResult` | Decomposes requirement |
| `analyzeComplexity(req)` | `req: Requirement` | `ComplexityLevel` | Analyzes requirement complexity |
| `exportMarkdown(result)` | `result: DecompositionResult` | `string` | Exports as Markdown |

**Decomposition Strategies:**

- `functional` - By function/feature
- `behavioral` - By behavior/scenario
- `structural` - By component/module
- `temporal` - By phase/timeline
- `stakeholder` - By stakeholder needs
- `risk-based` - By risk priority

---

#### RelatedRequirementsFinder

Finds related requirements using semantic similarity.

```typescript
import { createRelatedRequirementsFinder } from '@nahisaho/musubix-core';

const finder = createRelatedRequirementsFinder({
  similarityThreshold: 0.7,
  maxResults: 10
});

const related = finder.findRelated(requirement, allRequirements);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `findRelated(req, all)` | `req: Requirement, all: Requirement[]` | `RelatedResult[]` | Finds related requirements |
| `clusterRequirements(reqs)` | `reqs: Requirement[]` | `Cluster[]` | Clusters requirements |
| `findGaps(reqs)` | `reqs: Requirement[]` | `Gap[]` | Identifies coverage gaps |

---

### Design

#### C4ModelGenerator

Generates C4 architecture diagrams.

```typescript
import { createC4ModelGenerator } from '@nahisaho/musubix-core';

const generator = createC4ModelGenerator({
  defaultFormat: 'mermaid'
});

const contextDiagram = generator.generateContext(systemSpec);
const containerDiagram = generator.generateContainer(systemSpec);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `generateContext(spec)` | `spec: SystemSpec` | `C4Diagram` | Generates Context diagram |
| `generateContainer(spec)` | `spec: SystemSpec` | `C4Diagram` | Generates Container diagram |
| `generateComponent(container)` | `container: Container` | `C4Diagram` | Generates Component diagram |
| `export(diagram, format)` | `diagram: C4Diagram, format: ExportFormat` | `string` | Exports to format |

**Export Formats:**

- `structurizr` - Structurizr DSL
- `plantuml` - PlantUML syntax
- `mermaid` - Mermaid diagram
- `json` - JSON structure

---

#### ADRGenerator

Generates Architecture Decision Records.

```typescript
import { createADRGenerator } from '@nahisaho/musubix-core';

const generator = createADRGenerator({
  template: 'madr',
  outputFormat: 'markdown'
});

const adr = generator.generate(decision);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `generate(decision)` | `decision: ADRInput` | `ADR` | Generates ADR |
| `listAll()` | - | `ADR[]` | Lists all ADRs |
| `export(adr, format)` | `adr: ADR, format: OutputFormat` | `string` | Exports ADR |

---

### Codegen

#### TaskGenerator

Generates implementation tasks from requirements.

```typescript
import { createTaskGenerator } from '@nahisaho/musubix-core';

const generator = createTaskGenerator({
  estimateEffort: true,
  includeTests: true
});

const tasks = generator.generate(requirements);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `generate(reqs)` | `reqs: Requirement[]` | `Task[]` | Generates tasks |
| `estimateEffort(task)` | `task: Task` | `number` | Estimates hours |
| `prioritize(tasks)` | `tasks: Task[]` | `Task[]` | Prioritizes tasks |

---

#### CodingStandardsChecker

Validates code against coding standards.

```typescript
import { createCodingStandardsChecker } from '@nahisaho/musubix-core';

const checker = createCodingStandardsChecker({
  rules: ['naming', 'formatting', 'documentation']
});

const violations = checker.check(code, 'typescript');
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `check(code, lang)` | `code: string, lang: Language` | `Violation[]` | Checks code |
| `fix(code, violations)` | `code: string, violations: Violation[]` | `string` | Auto-fixes violations |
| `report(violations)` | `violations: Violation[]` | `Report` | Generates report |

---

### Validation

#### ConstitutionalValidator

Validates artifacts against 9 Constitutional Articles.

```typescript
import { createConstitutionalValidator } from '@nahisaho/musubix-core';

const validator = createConstitutionalValidator({
  strictMode: true,
  articles: ['all']
});

const result = validator.validate(artifact);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `validate(artifact)` | `artifact: Artifact` | `ValidationResult` | Validates artifact |
| `checkArticle(artifact, article)` | `artifact: Artifact, article: Article` | `ArticleResult` | Checks specific article |
| `generateReport(results)` | `results: ValidationResult[]` | `Report` | Generates validation report |

**Constitutional Articles:**

| Article | Name | Description |
|---------|------|-------------|
| I | Project Memory | Maintain consistent project context |
| II | Requirements | Complete EARS specification |
| III | Design | C4 + ADR documentation |
| IV | Task Breakdown | Traceable task decomposition |
| V | Traceability | Bidirectional traceability |
| VI | Explainability | Transparent AI decisions |
| VII | Integration | Seamless workflow integration |
| VIII | Adaptability | Flexible methodologies |
| IX | Quality | Continuous quality assurance |

---

### Utils

#### I18nManager

Manages internationalization and localization.

```typescript
import { createI18nManager, t } from '@nahisaho/musubix-core';

const i18n = createI18nManager({
  defaultLocale: 'en',
  fallbackLocale: 'en'
});

i18n.setLocale('ja');
console.log(t('common.save')); // 保存
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `t(key, options)` | `key: string, options?: object` | `string` | Translate key |
| `tp(key, count)` | `key: string, count: number` | `string` | Translate with plural |
| `setLocale(locale)` | `locale: Locale` | `void` | Set current locale |
| `formatDate(date)` | `date: Date` | `string` | Format date |
| `formatNumber(num)` | `num: number` | `string` | Format number |

**Supported Locales:**

`en`, `ja`, `zh`, `ko`, `de`, `fr`, `es`, `pt`

---

#### StructuredLogger

Provides structured logging with multiple transports.

```typescript
import { createLogger } from '@nahisaho/musubix-core';

const logger = createLogger({
  level: 'info',
  format: 'json'
});

logger.info('Operation completed', { duration: 150 });
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `debug(msg, meta)` | `msg: string, meta?: object` | `void` | Debug log |
| `info(msg, meta)` | `msg: string, meta?: object` | `void` | Info log |
| `warn(msg, meta)` | `msg: string, meta?: object` | `void` | Warning log |
| `error(msg, meta)` | `msg: string, meta?: object` | `void` | Error log |
| `child(context)` | `context: object` | `Logger` | Create child logger |

---

#### PerformanceProfiler

Profiles and measures performance.

```typescript
import { createPerformanceProfiler } from '@nahisaho/musubix-core';

const profiler = createPerformanceProfiler();

profiler.start('operation');
// ... operation ...
const result = profiler.end('operation');
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `start(name)` | `name: string` | `void` | Start measurement |
| `end(name)` | `name: string` | `ProfileResult` | End measurement |
| `measure(name, fn)` | `name: string, fn: Function` | `ProfileResult` | Measure function |
| `getStats(name)` | `name: string` | `Statistics` | Get statistics |

---

## MCP Server

### Starting the Server

```typescript
import { createMCPServer } from '@nahisaho/musubix-mcp-server';

const server = createMCPServer({
  transport: 'stdio', // or 'sse'
  capabilities: ['requirements', 'design', 'tasks', 'validation']
});

await server.start();
```

### Available Tools

| Tool | Description |
|------|-------------|
| `analyze_requirements` | Analyze requirement text |
| `generate_c4` | Generate C4 diagrams |
| `generate_adr` | Generate ADR documents |
| `generate_tasks` | Generate implementation tasks |
| `validate_artifact` | Validate against constitution |
| `query_knowledge` | Query YATA knowledge graph |

### Example Tool Call

```json
{
  "tool": "analyze_requirements",
  "arguments": {
    "text": "The system shall...",
    "options": {
      "validateEARS": true
    }
  }
}
```

---

## YATA Client

### Connecting to YATA

```typescript
import { createYATAClient } from '@nahisaho/musubix-yata-client';

const client = createYATAClient({
  endpoint: 'http://localhost:8000',
  apiKey: process.env.YATA_API_KEY
});

await client.connect();
```

### Operations

#### Query Knowledge

```typescript
const results = await client.query({
  type: 'requirement',
  filters: {
    priority: 'must',
    status: 'approved'
  }
});
```

#### Store Knowledge

```typescript
await client.store({
  type: 'design',
  data: designDocument,
  relations: [
    { type: 'implements', target: 'REQ-001' }
  ]
});
```

#### Link Entities

```typescript
await client.link({
  source: 'TSK-001',
  target: 'REQ-001',
  type: 'implements'
});
```

---

## Types Reference

### Requirement

```typescript
interface Requirement {
  id: string;
  title: string;
  description: string;
  type: 'functional' | 'non-functional' | 'constraint';
  priority: 'must' | 'should' | 'could' | 'wont';
  status: 'draft' | 'approved' | 'implemented' | 'verified';
  acceptanceCriteria: string[];
  traceability: {
    designRefs: string[];
    taskRefs: string[];
    testRefs: string[];
  };
}
```

### Task

```typescript
interface Task {
  id: string;
  title: string;
  description: string;
  status: 'pending' | 'in-progress' | 'completed' | 'blocked';
  requirementRef: string;
  designRef?: string;
  estimatedHours: number;
  actualHours?: number;
  assignee?: string;
  tags: string[];
}
```

### ValidationResult

```typescript
interface ValidationResult {
  valid: boolean;
  score: number;
  errors: ValidationError[];
  warnings: ValidationWarning[];
  coverage: {
    requirements: number;
    design: number;
    tasks: number;
    tests: number;
  };
}
```

### C4Diagram

```typescript
interface C4Diagram {
  id: string;
  type: 'context' | 'container' | 'component' | 'code';
  title: string;
  elements: C4Element[];
  relationships: C4Relationship[];
}
```

---

## Error Handling

All MUSUBIX functions follow a consistent error handling pattern:

```typescript
import { MUSUBIXError, ErrorCode } from '@nahisaho/musubix-core';

try {
  const result = analyzer.analyze(text);
} catch (error) {
  if (error instanceof MUSUBIXError) {
    console.error(`Error ${error.code}: ${error.message}`);
    // Handle specific error codes
    switch (error.code) {
      case ErrorCode.INVALID_REQUIREMENT:
        // Handle invalid requirement
        break;
      case ErrorCode.VALIDATION_FAILED:
        // Handle validation failure
        break;
    }
  }
}
```

### Error Codes

| Code | Description |
|------|-------------|
| `INVALID_REQUIREMENT` | Requirement format is invalid |
| `VALIDATION_FAILED` | Validation did not pass |
| `TRACEABILITY_BROKEN` | Traceability link is broken |
| `YATA_CONNECTION_ERROR` | Cannot connect to YATA |
| `MCP_TRANSPORT_ERROR` | MCP transport error |

---

## Contributing

See [CONTRIBUTING.md](./CONTRIBUTING.md) for contribution guidelines.

## License

MIT License - see [LICENSE](./LICENSE) for details.

---

**Version:** 1.0.12  
**Generated:** 2026-01-03  
**MUSUBIX Core Package**
