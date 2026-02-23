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
  - [Symbolic](#symbolic)
  - [Inference](#inference) *(v1.4.5)*
  - [REPL](#repl) *(v1.5.0)*
  - [YATA Local](#yata-local) *(v1.6.3)*
  - [YATA Global](#yata-global) *(v1.6.3)*
  - [KGPR](#kgpr) *(v1.6.4)*
  - [YATA Platform](#yata-platform) *(v1.7.0)*
  - [Formal Verification](#formal-verification) *(v1.7.5)*
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

### REPL

*(New in v1.5.0, Enhanced in v1.6.0)*

Interactive command-line interface components.

#### ReplEngine

Main REPL controller.

```typescript
import { createReplEngine } from '@nahisaho/musubix-core';

const engine = createReplEngine({
  history: { maxSize: 1000 },
  prompt: { showProject: true, showPhase: true },
  completion: { maxSuggestions: 10 },
  output: { defaultFormat: 'auto' }
});

await engine.start();
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `start()` | - | `Promise<void>` | Starts REPL session |
| `stop()` | - | `Promise<void>` | Stops REPL session |
| `execute(command)` | `command: string` | `Promise<CommandResult>` | Executes command |
| `isRunning()` | - | `boolean` | Returns running state |
| `on(event, handler)` | `event: string, handler: Function` | `void` | Registers event handler |

#### CommandCompleter

TAB completion provider.

```typescript
import { createCommandCompleter } from '@nahisaho/musubix-core';

const completer = createCommandCompleter({ maxSuggestions: 10 });
completer.registerCommands(commandDefinitions);

const result = completer.complete('req', 3);
// { completions: ['requirements'], prefix: 'req' }
```

#### HistoryManager

Command history persistence.

```typescript
import { createHistoryManager } from '@nahisaho/musubix-core';

const history = createHistoryManager({
  maxSize: 1000,
  filePath: '~/.musubix_history'
});

await history.load();
history.add('requirements analyze input.md');
await history.save();
```

#### SessionState

Session variable storage.

```typescript
import { createSessionState } from '@nahisaho/musubix-core';

const session = createSessionState();
session.set('project', 'my-app');
const value = session.get('project'); // 'my-app'
const expanded = session.expand('design $project'); // 'design my-app'
```

#### OutputFormatter

Output formatting (JSON/YAML/Table).

```typescript
import { createOutputFormatter } from '@nahisaho/musubix-core';

const formatter = createOutputFormatter({ defaultFormat: 'auto' });
console.log(formatter.format(data));
console.log(formatter.formatTable(arrayOfObjects));
console.log(formatter.formatJson(object));
console.log(formatter.formatYaml(object));
```

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

### Symbolic (v1.2.0)

The symbolic reasoning module provides formal verification and quality assurance capabilities.

#### SemanticCodeFilterPipeline

Filters and validates LLM-generated code semantically.

```typescript
import { createSemanticCodeFilterPipeline } from '@nahisaho/musubix-core';

const filter = createSemanticCodeFilterPipeline({
  hallucinationDetector: new HallucinationDetector(),
  constitutionRegistry: new ConstitutionRuleRegistry(),
});

const result = await filter.filter({
  candidates: [{ code: 'function example() {}', language: 'typescript' }],
  projectContext: { projectRoot: '/path/to/project' },
});
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `filter(input)` | `input: FilterInput` | `Promise<FilterOutput>` | Filters code candidates |

---

#### HallucinationDetector

Detects hallucinations (undefined symbols, invalid imports) in generated code.

```typescript
import { createHallucinationDetector } from '@nahisaho/musubix-core';

const detector = createHallucinationDetector();
const result = detector.detect(code, projectContext);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `detect(code, context)` | `code: string, context: ProjectContext` | `HallucinationResult` | Detects hallucinations |

---

#### EarsToFormalSpecConverter

Converts EARS requirements to SMT-LIB format.

```typescript
import { createEarsToFormalSpecConverter, parseEarsRequirement } from '@nahisaho/musubix-core';

const converter = createEarsToFormalSpecConverter();
const ast = parseEarsRequirement('THE system SHALL validate input');
const smtLib = converter.convert([ast]);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `convert(requirements)` | `requirements: EarsAstNode[]` | `SmtLibOutput` | Converts EARS to SMT-LIB |

---

#### Z3Adapter

Integrates with Z3 SMT solver for formal verification.

```typescript
import { createZ3Adapter } from '@nahisaho/musubix-core';

const z3 = createZ3Adapter({ timeoutMs: 5000 });
const result = await z3.verify(verificationConditions, smtLib);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `verify(vcs, smtLib)` | `vcs: VerificationCondition[], smtLib: string` | `Promise<FormalVerificationResult>` | Verifies conditions |
| `isAvailable()` | - | `Promise<boolean>` | Checks if Z3 is installed |

---

#### QualityGateValidator

Validates quality gates before phase transitions.

```typescript
import { QualityGateValidator, createComponentValidation } from '@nahisaho/musubix-core';

const validator = new QualityGateValidator();
const components = createComponentValidation({
  performanceBudgetDefined: true,
  auditLoggingDefined: true,
  traceabilityCompliant: true,
});

const result = validator.validate(traceabilityData, components);
const report = validator.generateApprovalReport(result);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `validate(traceability, components)` | `traceability: TraceabilityCoverage[], components: ComponentValidation` | `QualityGateResult` | Validates quality gate |
| `generateApprovalReport(result)` | `result: QualityGateResult` | `string` | Generates Markdown report |

**Quality Gate Checks:**

| Category | Checks |
|----------|--------|
| Traceability | Design coverage, Task decomposition, Coverage gaps |
| Non-Functional | Performance budget, Extensibility, Explainability |
| Security | Sensitive data masking, Audit logging |
| Constitution | All 9 articles compliance |

---

### Inference (v1.4.5)

The inference module provides OWL 2 RL reasoning and Datalog evaluation capabilities.

#### OWL2RLReasoner

Performs OWL 2 RL profile reasoning with 20+ built-in entailment rules.

```typescript
import { OWL2RLReasoner } from '@nahisaho/musubix-ontology-mcp';

const reasoner = new OWL2RLReasoner({
  maxIterations: 100,
  enablePropertyChains: true,
  enableInverseProperties: true
});

const result = await reasoner.reason(store, {
  onProgress: (progress) => console.log(`Iteration ${progress.iteration}`)
});
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `reason(store, options)` | `store: N3Store, options?: ReasonerOptions` | `Promise<ReasoningResult>` | Execute reasoning |
| `getProvenanceLog()` | - | `ProvenanceLog` | Get inference provenance |
| `getRulesApplied()` | - | `string[]` | Get list of applied rules |

**Built-in Rules:**

| Rule | Description |
|------|-------------|
| `prp-dom` | Property domain inference |
| `prp-rng` | Property range inference |
| `prp-inv1/2` | Inverse property inference |
| `prp-trp` | Transitive property chaining |
| `prp-symp` | Symmetric property inference |
| `cax-sco` | SubClassOf propagation |
| `scm-spo` | SubPropertyOf inference |
| `eq-rep-s/p/o` | SameAs replacement |

---

#### DatalogEngine

Evaluates Datalog rules with stratified negation support.

```typescript
import { DatalogEngine } from '@nahisaho/musubix-ontology-mcp';

const engine = new DatalogEngine();

const rules = [
  {
    head: { predicate: 'ancestor', args: ['?x', '?y'] },
    body: [{ predicate: 'parent', args: ['?x', '?y'] }]
  }
];

const result = await engine.evaluate(rules, facts);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `evaluate(rules, facts, options)` | `rules: Rule[], facts: Fact[], options?: EvalOptions` | `Promise<EvaluationResult>` | Evaluate rules |
| `stratify(rules)` | `rules: Rule[]` | `Rule[][]` | Stratify rules by dependency |

---

#### InferenceExplainer

Generates human-readable explanations for inferred facts.

```typescript
import { InferenceExplainer, ExplanationFormat } from '@nahisaho/musubix-ontology-mcp';

const explainer = new InferenceExplainer(provenanceLog);

const explanation = explainer.explain(
  subject, predicate, object,
  ExplanationFormat.TEXT
);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `explain(s, p, o, format)` | `s: string, p: string, o: string, format: ExplanationFormat` | `string` | Generate explanation |
| `getInferenceChain(s, p, o)` | `s: string, p: string, o: string` | `InferenceStep[]` | Get inference chain |

**Explanation Formats:**

| Format | Description |
|--------|-------------|
| `TEXT` | Plain text explanation |
| `MARKDOWN` | Markdown formatted |
| `HTML` | HTML with styling |

---

#### ProgressReporter

Reports real-time inference progress.

```typescript
import { createProgressReporter } from '@nahisaho/musubix-ontology-mcp';

const reporter = createProgressReporter({
  onProgress: (info) => console.log(`${info.phase}: ${info.newInferences} new`),
  throttleMs: 500
});

await reasoner.reason(store, { progressReporter: reporter });
```

**Configuration:**

| Option | Type | Description |
|--------|------|-------------|
| `onProgress` | `(info: ProgressInfo) => void` | Progress callback |
| `throttleMs` | `number` | Throttle interval (default: 500ms) |

---

### YATA Platform (v1.7.0)

Version 1.7.0 introduces enhanced YATA platform APIs.

#### IndexOptimizer

Optimizes database indexes for improved query performance.

```typescript
import { IndexOptimizer } from '@nahisaho/yata-local';

const optimizer = new IndexOptimizer(database);

// Analyze query patterns
const analysis = await optimizer.analyzeQueryPatterns();

// Create optimal indexes
const created = await optimizer.createOptimalIndexes();

// Check index health
const health = await optimizer.checkIndexHealth();
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `analyzeQueryPatterns()` | - | `QueryAnalysis` | Analyze query patterns |
| `createOptimalIndexes()` | - | `IndexCreationResult` | Create composite indexes |
| `checkIndexHealth()` | - | `IndexHealthReport` | Check fragmentation |
| `rebuildIndex(name)` | `name: string` | `void` | Rebuild specific index |

---

#### ExportPipeline

Exports knowledge graph data with transformation support.

```typescript
import { ExportPipeline } from '@nahisaho/yata-local';

const pipeline = new ExportPipeline(database);

// Full export
const data = await pipeline.exportFull({ namespace: 'myproject' });

// Incremental export
const changes = await pipeline.exportIncremental({
  since: lastExportTime,
  format: 'json'
});
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `exportFull(options)` | `ExportOptions` | `ExportData` | Full data export |
| `exportIncremental(options)` | `IncrementalOptions` | `ExportData` | Export changes since timestamp |
| `exportWithTransform(options)` | `TransformOptions` | `ExportData` | Export with format transformation |

**Export Formats:**

| Format | Description |
|--------|-------------|
| `json` | JSON format (default) |
| `rdf` | RDF/Turtle format |
| `ntriples` | N-Triples format |

---

#### GlobalSyncClient

Synchronizes local knowledge graph with YATA Global.

```typescript
import { GlobalSyncClient } from '@nahisaho/yata-global';

const client = new GlobalSyncClient({
  endpoint: 'https://yata-global.example.com',
  offlineMode: true
});

await client.initialize();

const result = await client.sync({
  namespace: 'myproject',
  direction: 'push'
});
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `initialize()` | - | `Promise<void>` | Initialize client |
| `sync(options)` | `SyncOptions` | `SyncResult` | Synchronize data |
| `getStatus()` | - | `SyncStatus` | Get sync status |
| `resolveConflict(id, resolution)` | `id: string, resolution: Resolution` | `void` | Resolve conflict |

---

#### SyncEngine

Core synchronization engine with conflict resolution.

```typescript
import { SyncEngine } from '@nahisaho/yata-global';

const engine = new SyncEngine({
  conflictStrategy: 'server-wins',
  batchSize: 100
});

const result = await engine.sync(localData, remoteData);
```

**Conflict Strategies:**

| Strategy | Description |
|----------|-------------|
| `server-wins` | Server data takes precedence |
| `client-wins` | Client data takes precedence |
| `merge` | Attempt automatic merge |
| `manual` | Require manual resolution |

---

#### CacheManager

Manages local caching for offline support.

```typescript
import { CacheManager } from '@nahisaho/yata-global';

const cache = new CacheManager({
  maxSize: 100 * 1024 * 1024, // 100MB
  ttl: 24 * 60 * 60 * 1000    // 24 hours
});

await cache.set('key', data);
const cached = await cache.get('key');
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `get(key)` | `key: string` | `T \| undefined` | Get cached item |
| `set(key, value)` | `key: string, value: T` | `void` | Cache item |
| `has(key)` | `key: string` | `boolean` | Check if exists |
| `clearAll()` | - | `void` | Clear all cache |
| `getStats()` | - | `CacheStats` | Get cache statistics |

---

#### YataUIServer

Web-based visualization server for knowledge graphs.

```typescript
import { YataUIServer, createYataUIServer } from '@nahisaho/yata-ui';

const server = createYataUIServer({
  port: 3000,
  host: 'localhost',
  cors: true,
  enableRealtime: true
});

server.setDataProvider(async () => ({
  nodes: await getEntities(),
  edges: await getRelationships()
}));

await server.start();
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `start()` | - | `Promise<void>` | Start server |
| `stop()` | - | `Promise<void>` | Stop server |
| `isRunning()` | - | `boolean` | Check if running |
| `getUrl()` | - | `string` | Get server URL |
| `setDataProvider(fn)` | `DataProvider` | `void` | Set data provider |
| `broadcastUpdate(event, data)` | `event: string, data: any` | `void` | Broadcast to clients |

**Configuration:**

| Option | Type | Default | Description |
|--------|------|---------|-------------|
| `port` | `number` | `3000` | Server port |
| `host` | `string` | `localhost` | Server host |
| `cors` | `boolean` | `true` | Enable CORS |
| `enableRealtime` | `boolean` | `true` | Enable WebSocket |

---

### Formal Verification (v1.7.5)

The formal verification module provides Z3 SMT solver integration for verifying code correctness.

#### Z3Adapter

Unified interface for Z3 backends (WASM or Process).

```typescript
import { Z3Adapter } from '@nahisaho/musubix-formal-verify';

// Create adapter (auto-selects best backend)
const z3 = await Z3Adapter.create();

// Check satisfiability
const result = await z3.checkSat('(declare-const x Int) (assert (> x 0))');
console.log(result); // 'sat' | 'unsat' | 'unknown'
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `create()` | - | `Promise<Z3Adapter>` | Create adapter instance |
| `checkSat(smtLib2)` | `smtLib2: string` | `Promise<string>` | Check satisfiability |
| `dispose()` | - | `Promise<void>` | Cleanup resources |

---

#### PreconditionVerifier

Verifies preconditions for functions and methods.

```typescript
import { PreconditionVerifier } from '@nahisaho/musubix-formal-verify';

const verifier = new PreconditionVerifier(z3Adapter);

const result = await verifier.verify({
  condition: { expression: 'amount > 0 && balance >= amount', format: 'javascript' },
  variables: [
    { name: 'amount', type: 'Int' },
    { name: 'balance', type: 'Int' }
  ]
});

console.log(result.status); // 'valid' | 'invalid' | 'unknown' | 'error'
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `verify(spec)` | `PreconditionSpec` | `Promise<VerificationResult>` | Verify precondition |

**PreconditionSpec:**

| Property | Type | Description |
|----------|------|-------------|
| `condition` | `Condition` | The precondition to verify |
| `variables` | `Variable[]` | Variables with types |

**VerificationResult:**

| Property | Type | Description |
|----------|------|-------------|
| `status` | `'valid' \| 'invalid' \| 'unknown' \| 'error'` | Verification status |
| `counterexample?` | `Record<string, any>` | Counterexample if invalid |
| `message?` | `string` | Additional message |

---

#### PostconditionVerifier

Verifies Hoare triples {P} C {Q}.

```typescript
import { PostconditionVerifier } from '@nahisaho/musubix-formal-verify';

const verifier = new PostconditionVerifier(z3Adapter);

const result = await verifier.verify({
  precondition: { expression: 'balance >= amount', format: 'javascript' },
  postcondition: { expression: 'balance_new == balance - amount', format: 'javascript' },
  preVariables: [
    { name: 'balance', type: 'Int' },
    { name: 'amount', type: 'Int' }
  ],
  postVariables: [
    { name: 'balance_new', type: 'Int' }
  ],
  transition: 'balance_new == balance - amount'
});
```

**PostconditionSpec:**

| Property | Type | Description |
|----------|------|-------------|
| `precondition` | `Condition` | Pre-state condition |
| `postcondition` | `Condition` | Post-state condition |
| `preVariables` | `Variable[]` | Pre-state variables |
| `postVariables` | `Variable[]` | Post-state variables |
| `transition` | `string` | State transition expression |

---

#### EarsToSmtConverter

Converts EARS requirements to SMT-LIB2 formulas.

```typescript
import { EarsToSmtConverter } from '@nahisaho/musubix-formal-verify';

const converter = new EarsToSmtConverter();

// Single conversion
const result = converter.convert('THE system SHALL validate inputs');

// Multiple conversions
const results = converter.convertMultiple([
  'THE system SHALL validate inputs',           // ubiquitous
  'WHEN error, THE system SHALL notify user',   // event-driven
  'WHILE busy, THE system SHALL queue requests', // state-driven
  'THE system SHALL NOT expose secrets',        // unwanted
  'IF admin, THEN THE system SHALL allow edit'  // optional
]);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `convert(ears)` | `ears: string` | `ConversionResult` | Convert single requirement |
| `convertMultiple(ears[])` | `ears: string[]` | `ConversionResult[]` | Convert multiple requirements |

**EARS Patterns:**

| Pattern | Syntax | SMT Encoding |
|---------|--------|--------------|
| Ubiquitous | `THE system SHALL [action]` | `(assert action)` |
| Event-driven | `WHEN [event], THE system SHALL [response]` | `(assert (=> event response))` |
| State-driven | `WHILE [state], THE system SHALL [response]` | `(assert (=> state response))` |
| Unwanted | `THE system SHALL NOT [behavior]` | `(assert (not behavior))` |
| Optional | `IF [condition], THEN THE system SHALL [response]` | `(assert (=> condition response))` |

---

#### TraceabilityDB

SQLite-based traceability database.

```typescript
import { TraceabilityDB } from '@nahisaho/musubix-formal-verify';

const db = new TraceabilityDB('./trace.db');

// Add nodes
await db.addNode({ id: 'REQ-001', type: 'requirement', title: 'User Auth' });
await db.addNode({ id: 'DES-001', type: 'design', title: 'AuthService' });
await db.addNode({ id: 'CODE-001', type: 'code', title: 'auth.ts' });

// Add links
await db.addLink({ source: 'DES-001', target: 'REQ-001', type: 'satisfies' });
await db.addLink({ source: 'CODE-001', target: 'DES-001', type: 'implements' });

// Query
const node = await db.getNode('REQ-001');
const stats = await db.getStatistics();
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `addNode(node)` | `TraceNode` | `Promise<void>` | Add traceability node |
| `getNode(id)` | `id: string` | `Promise<TraceNode \| undefined>` | Get node by ID |
| `addLink(link)` | `TraceLink` | `Promise<void>` | Add traceability link |
| `getStatistics()` | - | `Promise<TraceStats>` | Get database statistics |
| `query(nodeId, options?)` | `nodeId: string, QueryOptions` | `Promise<QueryResult>` | Query related nodes |
| `close()` | - | `void` | Close database |

**Node Types:**

| Type | Description |
|------|-------------|
| `requirement` | Requirements (REQ-*) |
| `design` | Design artifacts (DES-*) |
| `code` | Code files |
| `test` | Test cases |

**Link Types:**

| Type | Description |
|------|-------------|
| `satisfies` | Design satisfies requirement |
| `implements` | Code implements design |
| `verifies` | Test verifies requirement |
| `traces-to` | Generic traceability |

---

#### ImpactAnalyzer

Analyzes change impact across traceability graph.

```typescript
import { ImpactAnalyzer } from '@nahisaho/musubix-formal-verify';

const analyzer = new ImpactAnalyzer(traceabilityDB);

// Analyze impact of changing REQ-001
const impact = await analyzer.analyze('REQ-001');

console.log(`Total impacted: ${impact.totalImpacted}`);
console.log(`Direct: ${impact.directImpact.length}`);
console.log(`Indirect: ${impact.indirectImpact.length}`);
```

**Methods:**

| Method | Parameters | Returns | Description |
|--------|------------|---------|-------------|
| `analyze(nodeId)` | `nodeId: string` | `Promise<ImpactResult>` | Analyze change impact |

**ImpactResult:**

| Property | Type | Description |
|----------|------|-------------|
| `sourceId` | `string` | Source node ID |
| `directImpact` | `ImpactedNode[]` | Directly impacted nodes |
| `indirectImpact` | `ImpactedNode[]` | Transitively impacted nodes |
| `totalImpacted` | `number` | Total number of impacted nodes |
| `maxDepth` | `number` | Maximum impact depth |

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

**Version:** 1.7.0  
**Generated:** 2026-01-06  
**MUSUBIX Core Package**
