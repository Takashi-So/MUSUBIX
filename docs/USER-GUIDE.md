# MUSUBIX User Guide

> Neuro-Symbolic AI Coding with Ultimate Specification Driven Development

---

## Table of Contents

1. [Introduction](#introduction)
2. [Installation](#installation)
3. [CLI Usage](#cli-usage)
4. [Quick Start](#quick-start)
5. [SDD Workflow](#sdd-workflow)
6. [Self-Learning System](#self-learning-system)
7. [C4 Code Generation](#c4-code-generation)
8. [Symbolic Reasoning](#symbolic-reasoning) *(v1.2.0)*
9. [Consistency Validation](#consistency-validation) *(v1.4.1)*
10. [Advanced Inference](#advanced-inference) *(v1.4.5)*
11. [Interactive REPL Mode](#interactive-repl-mode) *(v1.5.0)*
12. [YATA Local](#yata-local) *(v1.6.3)*
13. [YATA Global](#yata-global) *(v1.6.3)*
14. [KGPR - Knowledge Graph Pull Request](#kgpr---knowledge-graph-pull-request) *(v1.6.4)*
15. [YATA Platform Enhancements](#yata-platform-enhancements) *(v1.7.0)*
16. [Formal Verification](#formal-verification) *(v1.7.5)*
17. [Security Analysis](#security-analysis) *(v1.8.0)*
18. [DFG/CFG Extraction](#dfgcfg-extraction) *(v2.0.0-alpha.1)*
19. [Lean 4 Integration](#lean-4-integration) *(v2.0.0-alpha.1)*
20. [YATA Scale](#yata-scale) *(v2.0.0-alpha.1)*
21. [MCP Server Integration](#mcp-server-integration)
22. [YATA Integration](#yata-integration)
23. [Best Practices](#best-practices)
24. [Troubleshooting](#troubleshooting)

---

## Introduction

### What is MUSUBIX?

**MUSUBIX** is an Ultimate Specification Driven Development (SDD) platform based on Neuro-Symbolic AI. By integrating MUSUBI (SDD Engine) with YATA (Knowledge Graph), it provides an AI-assisted development environment that maintains requirements, design, and implementation consistency.

### 9 Constitutional Articles

MUSUBIX development follows 9 Articles:

| Article | Description |
|---------|-------------|
| Article 1 | EARS-format requirements |
| Article 2 | C4 architecture design |
| Article 3 | ADR-based technical decisions |
| Article 4 | Test-first development (TDD) |
| Article 5 | Full requirement traceability |
| Article 6 | CI/CD automation |
| Article 7 | Knowledge graph management |
| Article 8 | AI-assisted code review |
| Article 9 | Continuous quality improvement |

---

## Installation

### System Requirements

- Node.js: >= 20.0.0
- npm: >= 10.0.0
- TypeScript: >= 5.3

### Method 1: Global Installation (Recommended)

```bash
# Global installation
npm install -g musubix

# Verify installation
musubix --version
```

### Method 2: Using npx

```bash
# Initialize project without installation
npx musubix init my-project

# Project templates
npx musubix init my-app --template typescript
npx musubix init my-api --template node
npx musubix init my-web --template react
```

### Method 3: Project Dependency

```bash
# Add to existing project
npm install musubix

# Use with npx
npx musubix --help
```

### Method 4: From Source

```bash
# Clone repository
git clone https://github.com/nahisaho/MUSUBIX.git
cd MUSUBIX

# Install dependencies
npm install

# Build
npm run build

# Global link
npm link
```

### YATA Installation (Optional)

If you want to use knowledge graph features, install YATA separately:

```bash
# Install uv (if not installed)
curl -LsSf https://astral.sh/uv/install.sh | sh

# Clone YATA
git clone https://github.com/nahisaho/YATA.git
cd YATA

# Create Python environment
uv venv
source .venv/bin/activate  # Linux/macOS
# or .venv\Scripts\activate  # Windows

# Install dependencies
uv pip install -e ".[dev]"
```

---

## CLI Usage

### musubix Command

Main command for project management:

```bash
# Initialize project
musubix init <project-name>

# Available templates
musubix init my-project --template typescript
musubix init my-project --template node
musubix init my-project --template react

# Help
musubix --help

# Version
musubix --version
```

### musubix-mcp Command

Start MCP server for AI platform integration:

```bash
# Start with stdio transport (default)
musubix-mcp

# Start with SSE transport
musubix-mcp --transport sse --port 3000

# Help
musubix-mcp --help

# Version
musubix-mcp --version
```

---

## Quick Start

### Basic TypeScript Usage

```typescript
import { 
  createRequirementsService,
  createDesignService,
  createValidationService 
} from 'musubix';

// Create services
const requirements = createRequirementsService();
const design = createDesignService();
const validation = createValidationService();

// Add requirement (EARS format)
const req = requirements.addRequirement({
  id: 'REQ-001',
  text: 'When a user logs in, the system shall authenticate the user',
  priority: 'high',
  acceptanceCriteria: [
    'JWT token shall be returned on successful login',
    'Error message shall be displayed on failure'
  ]
});

// Create design
const des = design.createComponent({
  id: 'DES-001',
  name: 'AuthModule',
  type: 'component',
  requirements: ['REQ-001'],
  decisions: ['Use JWT authentication']
});

// Validate
const result = validation.validate({
  requirements: [req],
  designs: [des]
});

console.log(result.compliant); // true or false
```

### SDD Workflow Overview

```
┌─────────────────┐
│   Requirements  │ EARS format requirements
└────────┬────────┘
         ↓
┌─────────────────┐
│     Design      │ C4 Architecture + ADR
└────────┬────────┘
         ↓
┌─────────────────┐
│     Tasks       │ Traceable implementation tasks
└────────┬────────┘
         ↓
┌─────────────────┐
│   Validation    │ 9 Articles compliance check
└─────────────────┘
```

---

## SDD Workflow

### Phase 1: Requirements (EARS Format)

Use EARS (Easy Approach to Requirements Syntax) format for requirements:

```typescript
const requirements = createRequirementsService();

// Pattern: "When <trigger>, the system shall <response>"
const loginReq = requirements.addRequirement({
  id: 'REQ-001',
  text: 'When a user enters valid credentials, the system shall issue an authentication token',
  priority: 'high',
  acceptanceCriteria: [
    'Token shall be valid for 24 hours',
    'Token shall include user information'
  ]
});

// Pattern: "While <state>, the system shall <behavior>"
const sessionReq = requirements.addRequirement({
  id: 'REQ-002',
  text: 'While a session is active, the system shall maintain user state',
  priority: 'medium'
});

// Get all requirements
const allReqs = requirements.getAllRequirements();
console.log(`Total requirements: ${allReqs.length}`);
```

### Phase 2: Design (C4 + ADR)

#### C4 Model

Design at 4 levels:

```typescript
const design = createDesignService();

// Level 1: Context
const system = design.createContainer({
  id: 'SYS-001',
  name: 'MUSUBIX System',
  type: 'system',
  description: 'Neuro-Symbolic AI-based SDD platform'
});

// Level 2: Container
const apiServer = design.createContainer({
  id: 'CON-001',
  name: 'API Server',
  type: 'container',
  parent: 'SYS-001',
  technology: 'Node.js + Express'
});

// Level 3: Component
const authModule = design.createComponent({
  id: 'COMP-001',
  name: 'Authentication Module',
  type: 'component',
  parent: 'CON-001',
  requirements: ['REQ-001']
});
```

#### ADR (Architecture Decision Record)

Document technical decisions:

```typescript
const adr = design.createADR({
  id: 'ADR-001',
  title: 'JWT for Authentication',
  context: 'Need to select stateless authentication method',
  decision: 'Use JWT',
  status: 'accepted',
  consequences: [
    'Positive: Stateless, scalable',
    'Negative: Token revocation requires additional implementation'
  ],
  relatedRequirements: ['REQ-001']
});
```

### Phase 3: Tasks

Break down requirements and designs into implementation tasks:

```typescript
const tasks = createTaskService();

// Create task linked to requirements
const task = tasks.createTask({
  id: 'TASK-001',
  title: 'Implement JWT authentication',
  description: 'Implement JWT-based authentication module',
  requirements: ['REQ-001'],
  designs: ['COMP-001'],
  estimatedHours: 4,
  acceptanceCriteria: [
    'Login API endpoint completed',
    'JWT generation/validation tests passing'
  ]
});

// Track progress
tasks.updateProgress('TASK-001', {
  status: 'in-progress',
  completedItems: ['Login API endpoint completed']
});
```

### Phase 4: Validation

Check compliance with 9 Constitutional Articles:

```typescript
const validation = createValidationService();

// Full validation
const result = validation.validateAll({
  requirements: requirements.getAllRequirements(),
  designs: design.getAllDesigns(),
  tasks: tasks.getAllTasks()
});

// Check results
console.log('Compliant:', result.compliant);
console.log('Score:', result.score);

// Check details by Article
result.articleResults.forEach(article => {
  console.log(`Article ${article.number}: ${article.passed ? '✓' : '✗'}`);
  if (!article.passed) {
    console.log('  Issues:', article.issues);
  }
});
```

---

## Self-Learning System

MUSUBIX includes a self-learning system that improves through feedback collection and pattern extraction.

### Learning CLI Commands

```bash
# View learning status dashboard
musubix learn status

# Record feedback on an artifact
musubix learn feedback <artifact-id> --type accept|reject|modify --artifact-type requirement|design|code|test --reason "explanation"

# List learned patterns
musubix learn patterns

# Manually register a pattern
musubix learn add-pattern <name> --category code|design|requirement|test --action prefer|avoid --description "pattern description"

# Remove a pattern
musubix learn remove-pattern <pattern-id>

# Get context-based recommendations
musubix learn recommend --artifact-type code

# Apply decay to unused patterns
musubix learn decay

# Export learning data (v1.4.0 enhanced)
musubix learn export --output learning-data.json
# Options:
#   --privacy-filter         Remove sensitive data (API keys, passwords)
#   --patterns-only          Export patterns only (exclude feedback)
#   --feedback-only          Export feedback only (exclude patterns)
#   --min-confidence <n>     Minimum confidence threshold (0-1)

# Import learning data with merge strategy (v1.4.0 enhanced)
musubix learn import learning-data.json
# Options:
#   --merge-strategy <skip|overwrite|merge>  How to handle duplicates
#   --dry-run                                Preview without applying
#   --patterns-only                          Import patterns only
#   --feedback-only                          Import feedback only
```

### Programmatic Usage

```typescript
import { createLearningEngine } from '@nahisaho/musubix-core';

const learningEngine = createLearningEngine();

// Record feedback
await learningEngine.recordFeedback({
  type: 'accept',
  artifactType: 'code',
  artifactId: 'AUTH-001',
  reason: 'Good implementation of JWT authentication'
});

// Get recommendations
const recommendations = await learningEngine.getRecommendations({
  artifactType: 'code',
  context: 'authentication'
});

// Export learning data
const data = await learningEngine.exportData();
```

### Pattern Extraction

Patterns are automatically extracted when similar feedback is recorded multiple times (default threshold: 3).

```typescript
// Patterns gain confidence with each occurrence
// High-confidence patterns (≥70%) appear in recommendations
const stats = await learningEngine.getStats();
console.log(`Total patterns: ${stats.totalPatterns}`);
console.log(`High confidence patterns: ${stats.highConfidencePatterns}`);
```

---

## C4 Code Generation

Generate TypeScript skeleton code from C4 design documents.

### CLI Usage

```bash
# Generate code from C4 design
musubix codegen generate design-c4.md --output src/

# With specific language
musubix codegen generate design-c4.md --output src/ --language typescript
```

### Generated Code Structure

From a C4 design with components like:

| ID | Name | Type | Description |
|----|------|------|-------------|
| auth | AuthService | component | Authentication |

MUSUBIX generates:

```typescript
// auth-service.ts
export interface IAuthService {
  authenticate(credentials: { username: string; password: string }): Promise<{ token: string }>;
  validate(token: string): Promise<boolean>;
}

export class AuthService implements IAuthService {
  async authenticate(credentials: { username: string; password: string }): Promise<{ token: string }> {
    // TODO: Implement authenticate
    throw new Error('Not implemented');
  }
  
  async validate(token: string): Promise<boolean> {
    // TODO: Implement validate
    throw new Error('Not implemented');
  }
}

export function createAuthService(): IAuthService {
  return new AuthService();
}
```

---

## Interactive REPL Mode

*(New in v1.5.0, Enhanced in v1.6.0)*

MUSUBIX provides an interactive REPL (Read-Eval-Print-Loop) shell for real-time command execution and exploration.

### Starting REPL

```bash
# Start interactive REPL
musubix repl

# With custom history file
musubix repl --history ~/.musubix-repl-history

# Without colors
musubix repl --no-color
```

### REPL Features

| Feature | Description |
|---------|-------------|
| Command completion | TAB completion for commands, options |
| History navigation | UP/DOWN arrows, history search |
| Session variables | `$name=value` to set, `$name` to reference |
| Output formatting | JSON, YAML, Table auto-formatting |
| CLI integration | Execute any CLI command directly |

### Basic Usage

```bash
musubix> help                          # Show all commands
musubix> help requirements             # Show command details
musubix> requirements analyze input.md # Execute CLI command
musubix> $project=my-app               # Set session variable
musubix> design generate $project      # Use variable in command
musubix> history                       # Show command history
musubix> exit                          # Exit REPL
```

### Session Variables

```bash
# Set variables
musubix> $req=REQ-001
musubix> $file=./docs/requirements.md

# Use in commands
musubix> requirements validate $file
musubix> trace impact $req

# Special variable: $_ holds last result
musubix> requirements analyze input.md
musubix> $_                           # Access last result
```

### Output Formats

```bash
# Auto-detect best format (default)
musubix> learn status

# Force JSON output
musubix> set format json
musubix> learn patterns

# Force YAML output
musubix> set format yaml

# Force table output
musubix> set format table
```

### History Management

```bash
# Show recent commands
musubix> history

# Search history (Ctrl+R style)
musubix> history search requirements

# Clear history
musubix> history clear
```

### REPL Components

| Component | Purpose |
|-----------|---------|
| `ReplEngine` | Main REPL controller |
| `CommandCompleter` | TAB completion provider |
| `HistoryManager` | Command history persistence |
| `SessionState` | Variable storage |
| `OutputFormatter` | JSON/YAML/Table output |
| `PromptRenderer` | Dynamic prompt display |

---

## YATA Local

*(New in v1.6.3)*

YATA Local provides a high-performance, SQLite-based local knowledge graph with built-in inference capabilities. Designed for single-user, offline scenarios where data sovereignty and speed are critical.

### Features

| Feature | Description |
|---------|-------------|
| **SQLite Storage** | WAL mode for concurrent reads, single-writer |
| **Full-Text Search** | FTS5-based triple search |
| **Graph Traversal** | BFS/DFS with depth control |
| **Inference Engine** | 4 OWL-lite rules (transitivity, symmetry, inverse, domain/range) |
| **Constraints** | 4 validation rules (cardinality, disjoint, unique, required) |
| **ACID Transactions** | Full transaction support |

### Installation

```bash
npm install @nahisaho/yata-local
```

### Quick Start

```typescript
import { YataLocal } from '@nahisaho/yata-local';

// Initialize with default config
const yata = new YataLocal('./knowledge.db');
await yata.initialize();

// Add triples
await yata.addTriple({
  subject: 'Person:john',
  predicate: 'hasParent',
  object: 'Person:mary'
});

// Query triples
const results = await yata.query({
  subject: 'Person:john',
  predicate: 'hasParent'
});

// Full-text search
const searchResults = await yata.search('john parent');

// Graph traversal (BFS)
const ancestors = await yata.traverse('Person:john', 'hasParent', {
  direction: 'outgoing',
  maxDepth: 5,
  algorithm: 'bfs'
});

// Clean up
await yata.close();
```

### Inference Engine

YATA Local supports four OWL-lite inference rules:

| Rule | Description | Example |
|------|-------------|---------|
| **Transitivity** | If A→B and B→C then A→C | hasAncestor is transitive |
| **Symmetry** | If A→B then B→A | friendOf is symmetric |
| **Inverse** | If A→B via P then B→A via P⁻¹ | hasChild ↔ hasParent |
| **Domain/Range** | Type inference from predicate | hasAge implies Person |

```typescript
// Run inference
const inferred = await yata.infer();
console.log(`Inferred ${inferred.length} new triples`);
```

### Constraints

```typescript
// Define constraints
await yata.addConstraint({
  type: 'cardinality',
  predicate: 'hasSpouse',
  max: 1
});

// Validate
const violations = await yata.validate();
if (violations.length > 0) {
  console.error('Constraint violations:', violations);
}
```

### Configuration Options

```typescript
const yata = new YataLocal('./knowledge.db', {
  // WAL mode for better concurrency (default: true)
  walMode: true,
  
  // Enable FTS5 search (default: true)
  enableSearch: true,
  
  // Auto-run inference on writes (default: false)
  autoInfer: false,
  
  // Journal mode (default: 'wal')
  journalMode: 'wal'
});
```

---

## YATA Global

*(New in v1.6.3)*

YATA Global is a distributed knowledge graph platform for team collaboration. It provides REST API access to shared knowledge graphs with offline support and intelligent synchronization.

### Features

| Feature | Description |
|---------|-------------|
| **REST API** | Full CRUD operations via HTTP |
| **Offline Cache** | SQLite-based local cache |
| **Sync Engine** | Push/Pull with conflict resolution |
| **Conflict Resolution** | Last-write-wins or custom strategies |
| **Authentication** | API key-based auth |
| **Batch Operations** | Bulk triple operations |

### Installation

```bash
npm install @nahisaho/yata-global
```

### Quick Start

```typescript
import { YataGlobal } from '@nahisaho/yata-global';

// Initialize client
const yata = new YataGlobal({
  endpoint: 'https://yata.example.com/api',
  apiKey: 'your-api-key',
  graphId: 'project-knowledge'
});

await yata.initialize();

// Add triples (batched)
await yata.addTriples([
  { subject: 'Task:001', predicate: 'assignedTo', object: 'User:alice' },
  { subject: 'Task:001', predicate: 'status', object: 'in-progress' }
]);

// Query with filters
const tasks = await yata.query({
  predicate: 'assignedTo',
  object: 'User:alice'
});

// Clean up
await yata.close();
```

### Offline Support

YATA Global supports offline-first operation with automatic synchronization:

```typescript
const yata = new YataGlobal({
  endpoint: 'https://yata.example.com/api',
  apiKey: 'your-api-key',
  graphId: 'project-knowledge',
  
  // Offline configuration
  offlineMode: true,
  cachePath: './yata-cache.db',
  syncInterval: 60000  // Auto-sync every 60 seconds
});

// Works offline - cached locally
await yata.addTriple({
  subject: 'Note:001',
  predicate: 'content',
  object: 'Important meeting notes'
});

// Manual sync when online
await yata.sync();
```

### Conflict Resolution

```typescript
const yata = new YataGlobal({
  // ... other options
  
  conflictStrategy: 'last-write-wins',  // Default
  // or: 'server-wins', 'client-wins', 'manual'
  
  onConflict: async (local, remote) => {
    // Custom resolution logic
    console.log('Conflict detected:', local, remote);
    return remote;  // Prefer remote version
  }
});
```

### Sync Status

```typescript
// Check sync status
const status = await yata.getSyncStatus();
console.log(`Pending changes: ${status.pendingPush}`);
console.log(`Last sync: ${status.lastSyncAt}`);

// Force full sync
await yata.sync({ force: true });
```

### When to Use YATA Local vs YATA Global

| Use Case | Recommended |
|----------|-------------|
| Personal knowledge base | YATA Local |
| Single-user application | YATA Local |
| Privacy-sensitive data | YATA Local |
| Team collaboration | YATA Global |
| Cross-device access | YATA Global |
| Shared project knowledge | YATA Global |
| Offline-first with sync | YATA Global |

---

## KGPR - Knowledge Graph Pull Request

*(v1.6.4)*

KGPR (Knowledge Graph Pull Request) enables safe sharing of knowledge graphs from YATA Local to YATA Global using a GitHub PR-like workflow.

### Workflow

```
┌─────────────┐     ┌──────────────┐     ┌───────────────┐
│ YATA Local  │ ──► │ KGPR (Draft) │ ──► │ YATA Global   │
│ (Local KG)  │     │ (Extract)    │     │ (Review/Merge)│
└─────────────┘     └──────────────┘     └───────────────┘

Status Flow:
draft → open → reviewing → approved/changes_requested → merged/closed
```

### Privacy Levels

| Level | Filtered Content |
|-------|------------------|
| `strict` | File paths, URLs, credentials, all metadata |
| `moderate` | File paths, URLs, credentials |
| `none` | No filtering |

### CLI Commands

```bash
# Create a KGPR
musubix kgpr create -t "Add authentication patterns"

# Preview diff before creating
musubix kgpr diff --namespace myproject --privacy moderate

# List KGPRs
musubix kgpr list

# Submit KGPR for review
musubix kgpr submit <id>

# Show KGPR details
musubix kgpr show <id>

# Close without merging
musubix kgpr close <id>
```

### MCP Tools

| Tool | Description |
|------|-------------|
| `kgpr_create` | Create KGPR from local knowledge graph |
| `kgpr_diff` | Preview diff before creating KGPR |
| `kgpr_list` | List all KGPRs |
| `kgpr_submit` | Submit KGPR for review |
| `kgpr_review` | Review KGPR (approve/changes_requested/commented) |

### Example Usage

```bash
# 1. Preview what will be shared
musubix kgpr diff --privacy strict

# 2. Create KGPR with description
musubix kgpr create -t "Share React patterns" -d "Learned patterns from project-x"

# 3. Review the KGPR
musubix kgpr show KGPR-001

# 4. Submit for review
musubix kgpr submit KGPR-001
```

---

## YATA Platform Enhancements

*(v1.7.0)*

Version 1.7.0 introduces significant enhancements to the YATA platform with 5 major features.

### Phase 1: Index Optimization

Optimized query performance for YATA Local with composite indexes.

```typescript
import { IndexOptimizer } from '@nahisaho/yata-local';

const optimizer = new IndexOptimizer(database);

// Analyze and create optimal indexes
const analysis = await optimizer.analyzeQueryPatterns();
const created = await optimizer.createOptimalIndexes();

// Check index health
const health = await optimizer.checkIndexHealth();
```

**Key Features:**
- Composite index creation for common query patterns
- Index health monitoring with fragmentation detection
- Automatic optimization recommendations

### Phase 2: Enhanced Export Pipeline

Powerful export capabilities with incremental export and multiple formats.

```typescript
import { ExportPipeline } from '@nahisaho/yata-local';

const pipeline = new ExportPipeline(database);

// Full export
const fullData = await pipeline.exportFull({ namespace: 'myproject' });

// Incremental export (changes since last export)
const changes = await pipeline.exportIncremental({
  since: lastExportTimestamp,
  format: 'json'
});

// Export with transformation
const transformed = await pipeline.exportWithTransform({
  format: 'rdf',
  includeMetadata: true
});
```

**Supported Formats:**
- JSON (default)
- RDF/Turtle
- N-Triples
- Custom transformers

### Phase 3: Global Sync Integration

Seamless synchronization between YATA Local and YATA Global.

```typescript
import { GlobalSyncClient, SyncEngine } from '@nahisaho/yata-global';

const client = new GlobalSyncClient({
  endpoint: 'https://yata-global.example.com',
  offlineMode: true
});

// Initialize sync
await client.initialize();

// Push local changes
const syncResult = await client.sync({
  namespace: 'myproject',
  direction: 'push'
});

// Pull updates from global
await client.sync({
  namespace: 'shared-patterns',
  direction: 'pull'
});
```

**Features:**
- Offline-first with automatic sync
- Conflict resolution strategies
- Selective namespace sync
- Framework pattern repository

### Phase 4: Code Generator Enhancement

Advanced code generation from design documents.

```typescript
import { CodeGenerator } from '@nahisaho/yata-local';

const generator = new CodeGenerator({
  language: 'typescript',
  outputDir: './src/generated'
});

// Generate from C4 design
const result = await generator.generateFromC4(designDocument);

// Generate with custom templates
await generator.generate({
  template: 'repository-pattern',
  context: { entityName: 'User' }
});
```

**Supported Patterns:**
- Repository Pattern
- Service Layer
- Factory Pattern
- Domain Events
- Value Objects

### Phase 5: YATA UI (Web Visualization)

Web-based visualization and management interface for knowledge graphs.

```typescript
import { YataUIServer, createYataUIServer } from '@nahisaho/yata-ui';

// Create and start server
const server = createYataUIServer({
  port: 3000,
  enableRealtime: true
});

// Set data provider
server.setDataProvider(async () => ({
  nodes: await getEntities(),
  edges: await getRelationships()
}));

await server.start();
console.log(`UI available at ${server.getUrl()}`);
```

**UI Features:**
- Interactive graph visualization
- Real-time updates via WebSocket
- Namespace filtering
- Entity/Relationship editing
- Export/Import functionality

### v1.7.0 Package Summary

| Package | Description |
|---------|-------------|
| `@nahisaho/yata-local` | IndexOptimizer, ExportPipeline, CodeGenerator |
| `@nahisaho/yata-global` | GlobalSyncClient, SyncEngine, CacheManager |
| `@nahisaho/yata-ui` | YataUIServer, Graph visualization |

---

## Formal Verification

*(v1.7.5)*

The `@nahisaho/musubix-formal-verify` package provides formal verification capabilities using the Z3 SMT solver.

### Installation

```bash
npm install @nahisaho/musubix-formal-verify
# Optional: Install z3-solver for WebAssembly support
npm install z3-solver
```

### Z3 SMT Solver Integration

```typescript
import { Z3Adapter, PreconditionVerifier, PostconditionVerifier } from '@nahisaho/musubix-formal-verify';

// Create Z3 adapter (auto-selects backend)
const z3 = await Z3Adapter.create();

// Precondition verification
const preVerifier = new PreconditionVerifier(z3);
const result = await preVerifier.verify({
  condition: { expression: 'amount > 0 && balance >= amount', format: 'javascript' },
  variables: [
    { name: 'amount', type: 'Int' },
    { name: 'balance', type: 'Int' },
  ],
});

console.log(result.status); // 'valid' | 'invalid' | 'unknown' | 'error'
```

### Hoare Triple Verification

```typescript
// Verify {P} C {Q}
const postVerifier = new PostconditionVerifier(z3);
const hoareResult = await postVerifier.verify({
  precondition: { expression: 'balance >= amount', format: 'javascript' },
  postcondition: { expression: 'balance_new == balance - amount', format: 'javascript' },
  preVariables: [{ name: 'balance', type: 'Int' }, { name: 'amount', type: 'Int' }],
  postVariables: [{ name: 'balance_new', type: 'Int' }],
  transition: 'balance_new == balance - amount',
});
```

### EARS to SMT Conversion

```typescript
import { EarsToSmtConverter } from '@nahisaho/musubix-formal-verify';

const converter = new EarsToSmtConverter();

// Convert EARS requirements to SMT-LIB2
const results = converter.convertMultiple([
  'THE system SHALL validate inputs',           // ubiquitous
  'WHEN error, THE system SHALL notify user',   // event-driven
  'WHILE busy, THE system SHALL queue requests', // state-driven
  'THE system SHALL NOT expose secrets',        // unwanted
  'IF admin, THEN THE system SHALL allow edit', // optional
]);

results.forEach(r => {
  console.log(`Pattern: ${r.formula?.metadata.earsPattern.type}`);
  console.log(`SMT: ${r.formula?.smtLib2}`);
});
```

### Traceability Database

```typescript
import { TraceabilityDB, ImpactAnalyzer } from '@nahisaho/musubix-formal-verify';

// Create SQLite-based traceability database
const db = new TraceabilityDB('./trace.db');

// Add nodes
await db.addNode({ id: 'REQ-001', type: 'requirement', title: 'User Auth' });
await db.addNode({ id: 'DES-001', type: 'design', title: 'AuthService' });
await db.addNode({ id: 'CODE-001', type: 'code', title: 'auth.ts' });

// Add traceability links
await db.addLink({ source: 'DES-001', target: 'REQ-001', type: 'satisfies' });
await db.addLink({ source: 'CODE-001', target: 'DES-001', type: 'implements' });

// Impact analysis
const analyzer = new ImpactAnalyzer(db);
const impact = await analyzer.analyze('REQ-001');
console.log(`Impacted nodes: ${impact.totalImpacted}`);
```

### v1.7.5 Package Summary

| Package | Description |
|---------|-------------|
| `@nahisaho/musubix-formal-verify` | Z3 integration, Hoare verification, EARS→SMT, TraceabilityDB |

### Supported Variable Types

| Type | Description |
|------|-------------|
| `Int` | Integer values |
| `Real` | Real numbers |
| `Bool` | Boolean values |
| `String` | String values |
| `Array` | Array types |
| `BitVec` | Bit vectors |

---

## Security Analysis

*(v1.8.0)*

The `@nahisaho/musubix-security` package provides comprehensive security analysis capabilities for TypeScript/JavaScript projects.

### Installation

```bash
npm install @nahisaho/musubix-security
```

### Vulnerability Scanning

Detects OWASP Top 10 and CWE Top 25 vulnerabilities using AST analysis:

```typescript
import { VulnerabilityScanner, createSecurityService } from '@nahisaho/musubix-security';

// Scan a single file
const scanner = new VulnerabilityScanner();
const vulnerabilities = scanner.scanFile('src/api.ts');

// Scan a directory
const result = await scanner.scanDirectory('./src');
console.log(`Found ${result.vulnerabilities.length} vulnerabilities`);
console.log(`Scanned ${result.scannedFiles} files`);
```

### Detected Vulnerabilities

| Category | CWE | Severity |
|----------|-----|----------|
| SQL Injection | CWE-89 | Critical |
| Command Injection | CWE-78 | Critical |
| XSS | CWE-79 | High |
| Path Traversal | CWE-22 | High |
| Code Injection | CWE-94 | Critical |
| NoSQL Injection | CWE-943 | High |

### Secret Detection

Detects hardcoded credentials and sensitive information:

```typescript
import { SecretDetector } from '@nahisaho/musubix-security';

const detector = new SecretDetector();
const secrets = detector.scanContent(content, 'config.ts');
const result = await detector.scan('./src');

console.log(`Found ${result.summary.total} secrets`);
```

### Detected Secret Types

| Type | Pattern |
|------|--------|
| AWS Access Key | `AKIA...` |
| AWS Secret Key | 40-char base64 |
| GitHub Token | `ghp_*`, `gho_*`, `ghu_*` |
| Private Key | PEM format |
| Database URL | `postgres://`, `mongodb://` |
| JWT Secret | JWT signing secrets |
| Stripe Key | `sk_live_*`, `sk_test_*` |

### Taint Analysis

Tracks data flow from user input (sources) to dangerous functions (sinks):

```typescript
import { TaintAnalyzer } from '@nahisaho/musubix-security';

const analyzer = new TaintAnalyzer();
const result = analyzer.analyze('./src');

console.log(`Sources: ${result.sources.length}`);
console.log(`Sinks: ${result.sinks.length}`);
console.log(`Taint paths: ${result.paths.length}`);
```

### Dependency Auditing

Integrates with npm audit to detect vulnerable dependencies:

```typescript
import { DependencyAuditor } from '@nahisaho/musubix-security';

const auditor = new DependencyAuditor();
const result = await auditor.audit('./project');

console.log(`Critical: ${result.summary.critical}`);
console.log(`High: ${result.summary.high}`);
```

### Integrated Security Service

Combines all security analysis features:

```typescript
import { createSecurityService } from '@nahisaho/musubix-security';

const service = createSecurityService();

// Full security scan
const result = await service.scan({
  target: './src',
  vulnerabilities: true,
  taint: true,
  secrets: true,
  dependencies: true,
  generateFixes: true,
});

console.log(`Total vulnerabilities: ${result.summary.totalVulnerabilities}`);
console.log(`Total secrets: ${result.summary.totalSecrets}`);
console.log(`Fixes generated: ${result.summary.fixesGenerated}`);
```

### Report Generation

Generate reports in multiple formats:

```typescript
// SARIF format (GitHub Code Scanning compatible)
const sarifReport = await service.generateReport(result, 'sarif');

// Markdown format
const mdReport = await service.generateReport(result, 'markdown');

// HTML format
const htmlReport = await service.generateReport(result, 'html');
```

### CLI Usage

```bash
# Full security scan
npx musubix-security scan ./src

# Vulnerability scan only
npx musubix-security scan ./src --vulnerabilities-only

# Secret detection
npx musubix-security secrets ./src

# Taint analysis
npx musubix-security taint ./src

# Dependency audit
npx musubix-security audit ./project

# Generate SARIF report
npx musubix-security scan ./src --format sarif --output report.sarif
```

### v1.8.0 Package Summary

| Package | Description |
|---------|-------------|
| `@nahisaho/musubix-security` | Vulnerability scanning, secret detection, taint analysis, dependency auditing |

---

## DFG/CFG Extraction

*(v2.0.0-alpha.1)*

The `@nahisaho/musubix-dfg` package provides Data Flow Graph (DFG) and Control Flow Graph (CFG) extraction for TypeScript and JavaScript code analysis.

### Installation

```bash
npm install @nahisaho/musubix-dfg
```

### DFG Extraction

Extract data flow graphs from source code:

```typescript
import { extractDFG, DFGExtractor } from '@nahisaho/musubix-dfg';

// Simple extraction
const dfg = extractDFG(sourceCode, 'typescript');

// With configuration
const extractor = new DFGExtractor({
  includeImplicitFlows: true,
  trackConstants: true,
});
const result = extractor.extract(sourceCode);

console.log(`Nodes: ${result.nodes.length}`);
console.log(`Edges: ${result.edges.length}`);
```

### CFG Extraction

Extract control flow graphs:

```typescript
import { extractCFG, CFGExtractor } from '@nahisaho/musubix-dfg';

const cfg = extractCFG(sourceCode);

// Traverse CFG
for (const block of cfg.blocks) {
  console.log(`Block ${block.id}: ${block.statements.length} statements`);
  console.log(`Successors: ${block.successors.join(', ')}`);
}
```

### Def-Use Chain Analysis

Build definition-use chains for variable tracking:

```typescript
import { analyzeDefUse } from '@nahisaho/musubix-dfg';

const chains = analyzeDefUse(dfg);

for (const chain of chains) {
  console.log(`Variable: ${chain.variable}`);
  console.log(`Defined at: line ${chain.definition.line}`);
  console.log(`Used at: ${chain.uses.map(u => u.line).join(', ')}`);
}
```

### Data Dependency Analysis

Analyze data dependencies between statements:

```typescript
import { analyzeDataDependencies } from '@nahisaho/musubix-dfg';

const deps = analyzeDataDependencies(dfg);

for (const dep of deps) {
  console.log(`${dep.from} -> ${dep.to}: ${dep.type}`);
}
```

---

## Lean 4 Integration

*(v2.0.0-alpha.1)*

The `@nahisaho/musubix-lean` package provides integration with the Lean 4 theorem prover for formal verification of requirements.

### Installation

```bash
npm install @nahisaho/musubix-lean
```

### EARS to Lean Conversion

Convert EARS requirements to Lean 4 theorems:

```typescript
import { EarsToLeanConverter } from '@nahisaho/musubix-lean';

const converter = new EarsToLeanConverter();

// Convert EARS requirement
const earsRequirement = {
  id: 'REQ-001',
  type: 'event-driven',
  trigger: 'user clicks submit',
  response: 'system saves form data',
};

const theorem = converter.convert(earsRequirement);
console.log(theorem.leanCode);
// theorem REQ_001 : ∀ (s : State), 
//   user_clicks_submit s → saves_form_data (next s)
```

### Lean AST Parsing

Parse and manipulate Lean 4 code:

```typescript
import { LeanParser, LeanAST } from '@nahisaho/musubix-lean';

const parser = new LeanParser();
const ast = parser.parse(leanCode);

// Traverse AST
for (const decl of ast.declarations) {
  if (decl.type === 'theorem') {
    console.log(`Theorem: ${decl.name}`);
    console.log(`Statement: ${decl.statement}`);
  }
}
```

### Proof Engine

Execute proofs using Lean 4:

```typescript
import { LeanProofEngine } from '@nahisaho/musubix-lean';

const engine = new LeanProofEngine({
  leanPath: '/usr/bin/lean',
  timeout: 30000,
});

const result = await engine.prove(theorem);

if (result.success) {
  console.log('Proof verified!');
  console.log(`Proof: ${result.proof}`);
} else {
  console.log(`Failed: ${result.error}`);
}
```

### ReProver Integration

Use ReProver for automated proof search:

```typescript
import { ReProverClient } from '@nahisaho/musubix-lean';

const reprover = new ReProverClient({
  endpoint: 'http://localhost:8080',
  maxDepth: 10,
});

const proof = await reprover.searchProof(theorem);

if (proof.found) {
  console.log('Proof found!');
  console.log(proof.tactics);
}
```

---

## YATA Scale

*(v2.0.0-alpha.1)*

The `@nahisaho/yata-scale` package provides distributed knowledge graph capabilities with sharding, caching, and synchronization.

### Installation

```bash
npm install @nahisaho/yata-scale
```

### High-Level API

Use `YataScaleManager` for simplified access:

```typescript
import { YataScaleManager } from '@nahisaho/yata-scale';

const yata = new YataScaleManager({
  shards: 16,
  cacheConfig: {
    l1MaxSize: 1000,
    l2MaxSize: 10000,
    l3Path: './cache',
  },
});

// Store entity
await yata.putEntity({
  id: 'entity-1',
  type: 'Document',
  properties: { title: 'Example' },
});

// Query
const results = await yata.query('SELECT ?s WHERE { ?s rdf:type Document }');
```

### Sharding

Distribute data across shards using consistent hashing:

```typescript
import { ShardManager, HashPartitionStrategy } from '@nahisaho/yata-scale';

const shardManager = new ShardManager({
  shardCount: 16,
  virtualNodes: 150,
  strategy: new HashPartitionStrategy(),
});

// Get shard for entity
const shard = shardManager.getShardForEntity('entity-id');
console.log(`Entity assigned to shard ${shard.id}`);

// Rebalance on node changes
await shardManager.addNode('node-5');
```

### Multi-Tier Caching

Three-tier caching for optimal performance:

```typescript
import { CacheManager, L1Cache, L2Cache, L3Cache } from '@nahisaho/yata-scale';

const cache = new CacheManager({
  l1: new L1Cache({ maxSize: 1000 }),    // LRU cache
  l2: new L2Cache({ maxSize: 10000 }),   // LFU cache
  l3: new L3Cache({ path: './cache' }),  // Disk cache
});

// Cache operations
await cache.set('key', value, { ttl: 3600 });
const result = await cache.get('key');

// Invalidation
await cache.invalidate('key');
await cache.invalidatePattern('user:*');
```

### Index Management

Multiple index types for efficient queries:

```typescript
import { IndexManager, BPlusTreeIndex, FullTextIndex, GraphIndex } from '@nahisaho/yata-scale';

const indexManager = new IndexManager();

// B+ Tree for range queries
indexManager.addIndex('timestamp', new BPlusTreeIndex());

// Full-text for search
indexManager.addIndex('content', new FullTextIndex());

// Graph for traversal
indexManager.addIndex('relationships', new GraphIndex());
```

### Vector Clock Synchronization

Distributed synchronization with conflict resolution:

```typescript
import { SyncController, VectorClock, ConflictResolver } from '@nahisaho/yata-scale';

const sync = new SyncController({
  nodeId: 'node-1',
  conflictStrategy: 'last-write-wins',
});

// Synchronize with peers
await sync.synchronize();

// Manual conflict resolution
sync.onConflict((conflict) => {
  console.log(`Conflict on ${conflict.key}`);
  return conflict.local; // or conflict.remote
});
```

### v2.0.0-alpha.1 Package Summary

| Package | Tests | Description |
|---------|-------|-------------|
| `@nahisaho/musubix-dfg` | 30 | DFG/CFG extraction, Def-Use analysis |
| `@nahisaho/musubix-lean` | 151 | Lean 4 theorem proving, EARS conversion |
| `@nahisaho/yata-scale` | 57 | Distributed sharding, caching, sync |
| **Total** | **238** | **Phase 1: Deep Symbolic Integration** |

---

## MCP Server Integration

### CLI Startup

```bash
# Default (stdio transport)
musubix-mcp

# SSE transport
musubix-mcp --transport sse --port 3000

# WebSocket transport
musubix-mcp --transport websocket --port 3001
```

### Programmatic Startup

```typescript
import { startServer, createMCPServer } from '@nahisaho/musubix-mcp-server';

// Simple startup
await startServer();

// Startup with options
const server = createMCPServer({
  transport: 'sse',
  port: 3000
});
await server.start();
```

### AI Platform Integration

#### GitHub Copilot (VS Code)

Add to `.vscode/settings.json`:

```json
{
  "github.copilot.chat.mcpServers": {
    "musubix": {
      "command": "musubix-mcp",
      "args": ["--transport", "stdio"]
    }
  }
}
```

#### Claude Desktop

Add to Claude configuration file (`~/.config/claude/config.json` or similar):

```json
{
  "mcpServers": {
    "musubix": {
      "command": "musubix-mcp",
      "args": []
    }
  }
}
```

#### Cursor

Add to `.cursor/mcp.json`:

```json
{
  "mcpServers": {
    "musubix": {
      "command": "musubix-mcp",
      "args": ["--transport", "stdio"]
    }
  }
}
```

### Available MCP Tools

| Tool Name | Description |
|-----------|-------------|
| `create_requirement` | Create EARS-format requirement |
| `validate_requirements` | Validate requirements |
| `create_design` | Create C4 design element |
| `create_adr` | Create ADR |
| `create_task` | Create implementation task |
| `validate_all` | Full 9 Articles compliance check |
| `get_traceability` | Get traceability matrix |

---

## Symbolic Reasoning

*(v1.2.0 New Feature)*

### Overview

Symbolic reasoning enhances LLM outputs by applying formal verification and knowledge-graph backed reasoning. This hybrid approach (Neuro-Symbolic) combines the creativity of neural networks with the precision of symbolic logic.

### Key Components

| Component | Description |
|-----------|-------------|
| `SemanticCodeFilterPipeline` | Filter LLM outputs for code quality |
| `HallucinationDetector` | Detect and prevent hallucinated outputs |
| `EarsToFormalSpecConverter` | Convert EARS requirements to formal Z3 specifications |
| `Z3Adapter` | Interface with Z3 solver for formal verification |
| `QualityGateValidator` | Validate against 17 quality gate checks |

### Usage

#### Semantic Code Filtering

```typescript
import { SemanticCodeFilterPipeline } from '@nahisaho/musubix-core';

const pipeline = new SemanticCodeFilterPipeline({
  enableHallucinationDetection: true,
  maxRetries: 3
});

const result = await pipeline.filter({
  code: generatedCode,
  context: { language: 'typescript', domain: 'authentication' }
});

if (result.isValid) {
  console.log('Code passed validation:', result.filteredCode);
} else {
  console.log('Issues found:', result.issues);
}
```

#### Hallucination Detection

```typescript
import { HallucinationDetector } from '@nahisaho/musubix-core';

const detector = new HallucinationDetector();

const analysis = await detector.analyze({
  response: llmResponse,
  groundTruth: knownFacts,
  context: projectContext
});

console.log('Confidence score:', analysis.confidence);
console.log('Hallucination risks:', analysis.risks);
```

#### EARS to Formal Specification

```typescript
import { EarsToFormalSpecConverter } from '@nahisaho/musubix-core';

const converter = new EarsToFormalSpecConverter();

const formalSpec = await converter.convert({
  earsRequirement: 'WHEN user clicks login, THE system SHALL authenticate within 2 seconds',
  requirementId: 'REQ-AUTH-001'
});

// Returns Z3-compatible specification
console.log(formalSpec.z3Expression);
```

#### Quality Gate Validation

```typescript
import { QualityGateValidator } from '@nahisaho/musubix-core';

const validator = new QualityGateValidator();

const gateResult = await validator.validate({
  requirements: requirementsList,
  designs: designDocuments,
  tasks: taskList
});

console.log('All gates passed:', gateResult.allPassed);
console.log('Gate details:', gateResult.gates);
// 17 quality checks including EARS compliance, traceability, etc.
```

### Quality Gate Checks

| Gate | Description |
|------|-------------|
| EARS Compliance | Requirements follow EARS patterns |
| Unique IDs | All artifacts have unique identifiers |
| Traceability | Full traceability chain exists |
| Design Coverage | All requirements have designs |
| Task Coverage | All designs have tasks |
| No Orphans | No orphaned requirements or tasks |
| Completeness | All required fields are present |
| ... | And 10 more quality checks |

---

## Consistency Validation

*(v1.4.1 New Feature)*

### Overview

Consistency validation ensures data integrity when adding triples to the knowledge graph. Based on OWL constraints, it detects violations before they corrupt the knowledge base.

### Validation Types

| Type | Description | Severity |
|------|-------------|----------|
| `disjoint-class-membership` | Instance belongs to disjoint classes | error |
| `functional-property-violation` | Multiple values for functional property | error |
| `inverse-functional-violation` | Same value maps to multiple subjects | error |
| `asymmetric-violation` | Inverse relation exists for asymmetric property | error |
| `irreflexive-violation` | Self-reference for irreflexive property | error |
| `duplicate-triple` | Exact duplicate triple | warning |
| `circular-dependency` | Circular subClassOf chain | error |

### Usage

#### Validated Triple Addition

```typescript
import { N3Store } from '@nahisaho/musubix-ontology-mcp';

// Enable validation on add
const store = new N3Store({}, true);

// Add with validation
const result = store.addTripleValidated({
  subject: 'http://example.org/Person1',
  predicate: 'http://example.org/hasMother',
  object: 'http://example.org/Mother1'
});

if (!result.success) {
  console.error('Validation errors:', result.validation.errors);
}
```

#### Store-wide Consistency Check

```typescript
// Check entire store
const consistency = store.checkConsistency();

if (!consistency.consistent) {
  for (const violation of consistency.violations) {
    console.log(`${violation.type}: ${violation.message}`);
    console.log('Affected triples:', violation.triples);
  }
  
  // Get fix suggestions
  for (const suggestion of consistency.suggestions) {
    console.log(`Suggestion: ${suggestion.suggestion}`);
    console.log(`Auto-fixable: ${suggestion.autoFixable}`);
  }
}
```

#### Direct Validator Usage

```typescript
import { ConsistencyValidator } from '@nahisaho/musubix-ontology-mcp';

const validator = new ConsistencyValidator({
  checkDisjointClasses: true,
  checkFunctionalProperties: true,
  checkDuplicates: true,
  checkCircularDependencies: true
});

// Validate before adding
const validation = validator.validateTriple(newTriple, existingTriples);
if (!validation.valid) {
  console.error(validation.errors);
}

// Find duplicates
const duplicates = validator.findDuplicates(allTriples);
const semanticDuplicates = validator.findSemanticDuplicates(allTriples);
```

---

## Advanced Inference

*(v1.4.5 New Feature)*

### Overview

Advanced Inference provides OWL 2 RL reasoning and Datalog evaluation capabilities for the knowledge graph. It supports materialization of implicit facts, rule-based inference, and human-readable explanations.

### Key Components

| Component | Description |
|-----------|-------------|
| `OWL2RLReasoner` | OWL 2 RL profile reasoning with 20+ built-in rules |
| `DatalogEngine` | Stratified Datalog evaluation engine |
| `InferenceExplainer` | Natural language explanation generator |
| `ProgressReporter` | Real-time inference progress tracking |

### OWL 2 RL Reasoning

```typescript
import { OWL2RLReasoner } from '@nahisaho/musubix-ontology-mcp';

const reasoner = new OWL2RLReasoner({
  maxIterations: 100,
  enablePropertyChains: true,
  enableInverseProperties: true
});

// Run reasoning on store
const result = await reasoner.reason(store, {
  onProgress: (progress) => {
    console.log(`Iteration ${progress.iteration}: ${progress.newTriples} new triples`);
  }
});

console.log(`Inferred ${result.inferredCount} new facts`);
console.log(`Rules applied: ${result.rulesApplied.join(', ')}`);
```

### OWL 2 RL Rules

| Rule ID | Name | Description |
|---------|------|-------------|
| `prp-dom` | Property Domain | Infer type from property domain |
| `prp-rng` | Property Range | Infer type from property range |
| `prp-inv1/2` | Inverse Properties | Infer inverse relationships |
| `prp-trp` | Transitive Properties | Chain transitive properties |
| `prp-symp` | Symmetric Properties | Infer symmetric relationships |
| `cax-sco` | SubClassOf | Propagate class membership |
| `scm-spo` | SubPropertyOf | Property subsumption |
| `eq-rep-s/p/o` | SameAs Replacement | Substitute equal individuals |

### Datalog Evaluation

```typescript
import { DatalogEngine } from '@nahisaho/musubix-ontology-mcp';

const engine = new DatalogEngine();

// Define rules
const rules = [
  {
    head: { predicate: 'ancestor', args: ['?x', '?y'] },
    body: [
      { predicate: 'parent', args: ['?x', '?y'] }
    ]
  },
  {
    head: { predicate: 'ancestor', args: ['?x', '?z'] },
    body: [
      { predicate: 'parent', args: ['?x', '?y'] },
      { predicate: 'ancestor', args: ['?y', '?z'] }
    ]
  }
];

// Evaluate rules
const result = await engine.evaluate(rules, facts, {
  onProgress: (progress) => {
    console.log(`Stratum ${progress.stratum}: evaluating ${progress.rule}`);
  }
});

console.log(`Derived ${result.derivedFacts.length} new facts`);
```

### Inference Explanation

```typescript
import { InferenceExplainer, ExplanationFormat } from '@nahisaho/musubix-ontology-mcp';

const explainer = new InferenceExplainer(reasoner.getProvenanceLog());

// Get explanation for a specific triple
const explanation = explainer.explain(
  'http://example.org/Animal',
  'rdf:type',
  'owl:Class',
  ExplanationFormat.TEXT
);

console.log(explanation);
// Output: "Animal is a Class because it is declared as owl:Class via rule cax-sco"

// Generate HTML explanation
const htmlExplanation = explainer.explain(
  subject, predicate, object,
  ExplanationFormat.HTML
);
```

### Progress Reporting

```typescript
import { createProgressReporter } from '@nahisaho/musubix-ontology-mcp';

const reporter = createProgressReporter({
  onProgress: (info) => {
    console.log(`Phase: ${info.phase}`);
    console.log(`Iteration: ${info.iteration}/${info.maxIterations}`);
    console.log(`Triples: ${info.totalTriples}`);
    console.log(`New inferences: ${info.newInferences}`);
  },
  throttleMs: 500  // Report every 500ms
});

await reasoner.reason(store, { progressReporter: reporter });
```

---

## YATA Integration

### What is YATA?

**YATA** (Yet Another Thinking Agent) is a knowledge graph management MCP server that stores and retrieves expertise and know-how as structured data. **Note: YATA is a separate Python-based installation.**

### Architecture

```
┌─────────────────────────────────────────┐
│           AI Platform                    │
│    (GitHub Copilot, Claude, etc.)       │
└─────────────┬───────────────────────────┘
              │ MCP Protocol
      ┌───────┴───────┐
      ↓               ↓
┌──────────┐   ┌──────────┐
│ MUSUBIX  │   │   YATA   │
│   MCP    │   │   MCP    │
│  Server  │   │  Server  │
└────┬─────┘   └────┬─────┘
     │              │
     ↓              ↓
┌──────────┐   ┌──────────┐
│   SDD    │   │ Knowledge│
│  Engine  │   │   Graph  │
└──────────┘   └──────────┘
```

### YATA Client (from MUSUBIX)

```typescript
import { createYATAClient } from '@nahisaho/musubix-yata-client';

// Create client
const yata = createYATAClient({
  endpoint: 'http://localhost:8000',
  apiKey: process.env.YATA_API_KEY
});

// Save knowledge
await yata.addKnowledge({
  topic: 'jwt-authentication',
  content: 'Best practices for JWT implementation',
  tags: ['security', 'authentication'],
  relatedRequirements: ['REQ-001']
});

// Search knowledge
const results = await yata.search({
  query: 'authentication best practices',
  limit: 10
});
```

### YATA Features

| Feature | Description |
|---------|-------------|
| 34 MCP Tools | Read/write/query knowledge graphs |
| 47 Frameworks | TypeScript, Python, React, etc. |
| Vector Search | Semantic knowledge search |
| Relationship Mapping | Connect knowledge nodes |

---

## Best Practices

### 1. Requirements Best Practices

✅ **Recommended**:
- Use EARS format
- Include verifiable acceptance criteria
- One function per requirement

❌ **Avoid**:
- Vague expressions ("appropriately", "quickly", etc.)
- Multiple functions in one requirement
- Implementation details in requirements

### 2. Design Best Practices

✅ **Recommended**:
- Utilize all 4 C4 levels
- Document important decisions with ADR
- Maintain traceability to requirements

❌ **Avoid**:
- Over-detailed initial design
- Omitting decision rationale
- Isolated design documents

### 3. Task Management Best Practices

✅ **Recommended**:
- Granularity within 4 hours
- Clear links to requirements
- Explicit completion criteria

❌ **Avoid**:
- Tasks too large (8+ hours)
- Tasks without requirement links
- Vague completion criteria

---

## Troubleshooting

### Common Problems and Solutions

#### Requirements Validation Error

```
Error: EARS format not detected
```

**Solution**: Include an EARS pattern in your requirement text.

```typescript
// Before
const text = 'Implement authentication feature';

// After
const text = 'When a user logs in, the system shall perform authentication';
```

#### Traceability Warning

```
Warning: Requirement REQ-001 has no design reference
```

**Solution**: Create a design document and link it.

```typescript
requirementsService.linkDesign('REQ-001', 'DES-001');
```

#### MCP Server Connection Error

```
Error: Cannot connect to MCP server
```

**Solution**:
1. Verify server is running
2. Check port number
3. Check firewall settings

```bash
# Check server status
ps aux | grep musubix
```

#### YATA Connection Error

```
Error: Cannot connect to YATA endpoint
```

**Solution**:
1. Verify endpoint URL
2. Check API key
3. Check network settings

```typescript
const client = createYATAClient({
  endpoint: 'http://localhost:8000',  // Correct URL
  apiKey: process.env.YATA_API_KEY    // Verify environment variable
});
```

---

## Next Steps

- 📚 See [API Reference](./API-REFERENCE.md)
- 💡 Check [Sample Projects](./examples/)
- 🤝 Read [Contribution Guide](./CONTRIBUTING.md)

---

## Related Documents

| Document | Description |
|----------|-------------|
| [INSTALL-GUIDE.md](INSTALL-GUIDE.md) | Detailed installation guide |
| [API-REFERENCE.md](API-REFERENCE.md) | API reference |
| [evolution-from-musubi-to-musubix.md](evolution-from-musubi-to-musubix.md) | Evolution from MUSUBI |

---

**Version**: 1.8.5  
**Last Updated**: 2026-01-08  
**MUSUBIX Project**
