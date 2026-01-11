# YATA Local User Guide

> **YATA Local** - SQLite-based Local Knowledge Graph Storage

## 📖 Overview

YATA Local (`@nahisaho/yata-local`) is a local knowledge graph storage system for AI coding assistants. Using SQLite as a backend, it efficiently manages code structures, relationships, and patterns.

### Key Features

| Feature | Description |
|---------|-------------|
| **Entity Management** | Store code elements like classes, functions, interfaces |
| **Relationship Tracking** | Record inheritance, calls, dependencies |
| **Reasoning Engine** | Rule-based inference and constraint validation |
| **Query Engine** | Pattern matching, path finding, subgraph extraction |
| **Import/Export** | JSON, RDF, GraphML format support |
| **KGPR** | Knowledge Graph Pull Request for knowledge sharing |
| **Wake-Sleep Learning** | Pattern learning and consolidation |

---

## 🚀 Installation

```bash
npm install @nahisaho/yata-local
```

### Prerequisites

- Node.js >= 20.0.0
- npm >= 10.0.0

---

## 📘 Basic Usage

### Initialization and Connection

```typescript
import { createYataLocal } from '@nahisaho/yata-local';

// Create instance
const yata = createYataLocal({
  path: './.yata/knowledge.db',  // Database file path
  walMode: true,                  // WAL mode (recommended)
  cacheSize: 64 * 1024,          // Cache size (KB)
});

// Open database
await yata.open();

// ... operations ...

// Close on exit
await yata.close();
```

### Configuration Options

```typescript
interface DatabaseConfig {
  path: string;           // Database file path (default: '.yata/knowledge.db')
  walMode: boolean;       // Enable WAL mode (default: true)
  mmapSize: number;       // Memory mapping size (default: 256MB)
  cacheSize: number;      // Cache size (default: 64MB)
  foreignKeys: boolean;   // Foreign key constraints (default: true)
  encryption?: {          // Encryption settings (optional)
    enabled: boolean;
    key: string;
  };
}
```

---

## 📦 Entity Operations

### Adding Entities

```typescript
// Add single entity
const entityId = await yata.addEntity({
  type: 'class',
  name: 'UserService',
  namespace: 'app.services',
  filePath: 'src/services/user.ts',
  line: 10,
  description: 'User management service',
  metadata: {
    entityKind: 'service',
    isExported: true,
  },
});

console.log('Created entity:', entityId);
```

### Batch Addition

```typescript
// Add multiple entities at once
const ids = await yata.addEntities([
  {
    type: 'interface',
    name: 'IUserRepository',
    namespace: 'app.repositories',
    filePath: 'src/repositories/user.ts',
  },
  {
    type: 'function',
    name: 'createUser',
    namespace: 'app.services.user',
    filePath: 'src/services/user.ts',
  },
]);
```

### Retrieving Entities

```typescript
// Get by ID
const entity = await yata.getEntity(entityId);

// Get by name
const userService = await yata.getEntityByName('UserService', 'app.services');

// Get by type
const classes = await yata.getEntitiesByType('class');

// Get by namespace
const serviceEntities = await yata.getEntitiesByNamespace('app.services');

// Get by metadata entityKind
const services = await yata.getEntitiesByKind('service');
```

### Updating Entities

```typescript
// Update
await yata.updateEntity(entityId, {
  description: 'Updated description',
  metadata: { version: '2.0.0' },
});

// Upsert (update if exists, add if not)
const result = await yata.upsertEntity({
  type: 'class',
  name: 'UserService',
  namespace: 'app.services',
  filePath: 'src/services/user.ts',
  metadata: { version: '3.0.0' },
}, 'name-namespace');  // Match criteria: name + namespace

console.log(result);
// => { id: '...', created: false }  // If updated
// => { id: '...', created: true }   // If newly created
```

### Deleting Entities

```typescript
// Delete by ID
await yata.deleteEntity(entityId);

// Bulk delete by file path
const deletedCount = await yata.deleteEntitiesByFile('src/services/user.ts');
console.log(`Deleted ${deletedCount} entities`);
```

---

## 🔗 Relationship Operations

### Entity Types

```typescript
type EntityType =
  | 'class'      // Class
  | 'interface'  // Interface
  | 'function'   // Function
  | 'method'     // Method
  | 'variable'   // Variable
  | 'constant'   // Constant
  | 'type'       // Type definition
  | 'enum'       // Enumeration
  | 'module'     // Module
  | 'package'    // Package
  | 'file'       // File
  | 'parameter'  // Parameter
  | 'property'   // Property
  | 'import'     // Import
  | 'export'     // Export
  | 'unknown';   // Unknown
```

### Relationship Types

```typescript
type RelationType =
  | 'calls'              // Calls
  | 'imports'            // Imports
  | 'exports'            // Exports
  | 'extends'            // Extends
  | 'inherits'           // Inherits
  | 'implements'         // Implements
  | 'contains'           // Contains
  | 'uses'               // Uses
  | 'defines'            // Defines
  | 'references'         // References
  | 'depends-on'         // Depends on
  | 'transitively-depends-on'  // Transitive dependency
  | 'type-compatible'    // Type compatible
  | 'has-method'         // Has method
  | 'overrides'          // Overrides
  | 'returns'            // Returns
  | 'parameter_of'       // Parameter of
  | 'member_of'          // Member of
  | 'related-to'         // Related to
  | 'defined-in-same-file'  // Defined in same file
  | 'unknown';           // Unknown
```

### Adding and Getting Relationships

```typescript
// Add relationship
const relId = await yata.addRelationship(
  classId,        // Source entity ID
  interfaceId,    // Target entity ID
  'implements',   // Relationship type
  { isRequired: true }  // Metadata
);

// Get relationships
const outgoing = await yata.getRelationships(classId, 'out');   // Outgoing
const incoming = await yata.getRelationships(classId, 'in');    // Incoming
const all = await yata.getRelationships(classId, 'both');       // Both directions

// Delete relationship
await yata.deleteRelationship(relId);
```

---

## 🔍 Query Operations

### Basic Query

```typescript
const result = await yata.query({
  entityFilters: {
    types: ['class', 'interface'],
    namespaces: ['app.services'],
  },
  textSearch: 'User',
  relationshipFilters: {
    types: ['implements', 'extends'],
  },
}, {
  limit: 100,
  offset: 0,
  sortBy: 'name',
  sortOrder: 'asc',
});

console.log(`Found ${result.entities.length} entities`);
```

### Full-text Search

```typescript
const entities = await yata.search('UserService', 50);
```

### Path Finding

```typescript
// Find path between two entities
const path = await yata.findPath(startId, endId, {
  maxDepth: 5,
  relationshipTypes: ['calls', 'imports'],
  direction: 'forward',
});

if (path) {
  console.log('Path found:', path.entities.map(e => e.name).join(' -> '));
}
```

### Subgraph Extraction

```typescript
// Extract subgraph around an entity
const subgraph = await yata.extractSubgraph(rootId, {
  depth: 3,
  entityTypes: ['class', 'interface', 'function'],
  relationshipTypes: ['calls', 'implements'],
  direction: 'both',
});

console.log(`Subgraph: ${subgraph.entities.length} entities, ${subgraph.relationships.length} relationships`);
```

### Pattern Matching

```typescript
// Match graph patterns
const matches = await yata.matchPattern({
  nodes: [
    { id: 'service', type: 'class', namePattern: /.*Service$/ },
    { id: 'repository', type: 'interface', namePattern: /.*Repository$/ },
  ],
  edges: [
    { sourceId: 'service', targetId: 'repository', type: 'uses' },
  ],
});

for (const match of matches) {
  console.log('Match:', match.bindings);
}
```

---

## 💬 Natural Language Query (v2.4.1 NEW!)

YATA Local supports natural language queries in both English and Japanese. Ask questions about code structure using natural language.

### Basic Usage

```typescript
// Use the ask() method
const result = await yata.ask('What functions call UserService?');

console.log('Intent:', result.parsedQuery.intent);
// => Intent: find_callers

console.log('Results:');
for (const entity of result.entities) {
  console.log(`  - ${entity.name} (${entity.type})`);
}

console.log('Explanation:', result.explanation);
// => Found 3 function(s) calling "UserService"
```

### Natural Language → API Command Mapping

Natural language queries are internally converted to appropriate API method calls.

#### Find Callers

| Natural Language Query | Equivalent API Command |
|----------------------|------------------------|
| `What functions call UserService?` | `yata.getRelationships(userServiceId, 'in', { types: ['calls'] })` |
| `What calls authenticate?` | `yata.query({ relationshipFilters: { types: ['calls'], targetId: authId } })` |
| `Which methods invoke processOrder?` | `yata.traverse(processOrderId, ['calls'], 'backward', 1)` |

```typescript
// Natural language
const result = await yata.ask('What functions call UserService?');

// Equivalent API call
const entity = await yata.getEntityByName('UserService');
const callers = await yata.getRelationships(entity.id, 'in');
const callerEntities = callers
  .filter(r => r.type === 'calls')
  .map(r => yata.getEntity(r.sourceId));
```

#### Find Callees

| Natural Language Query | Equivalent API Command |
|----------------------|------------------------|
| `What does UserService call?` | `yata.getRelationships(userServiceId, 'out', { types: ['calls'] })` |
| `List functions called by processOrder` | `yata.traverse(processOrderId, ['calls'], 'forward', 1)` |

```typescript
// Natural language
const result = await yata.ask('What does UserService call?');

// Equivalent API call
const entity = await yata.getEntityByName('UserService');
const callees = await yata.getRelationships(entity.id, 'out');
const calleeEntities = callees
  .filter(r => r.type === 'calls')
  .map(r => yata.getEntity(r.targetId));
```

#### Find Implementations

| Natural Language Query | Equivalent API Command |
|----------------------|------------------------|
| `Show implementations of Repository` | `yata.getRelationships(repositoryId, 'in', { types: ['implements'] })` |
| `What implements UserInterface?` | `yata.query({ relationshipFilters: { types: ['implements'], targetId: interfaceId } })` |
| `List classes implementing Service` | `yata.matchPattern({ edges: [{ targetId: 'interface', type: 'implements' }] })` |

```typescript
// Natural language
const result = await yata.ask('Show implementations of Repository');

// Equivalent API call
const iface = await yata.getEntityByName('Repository');
const implementations = await yata.getRelationships(iface.id, 'in');
const implEntities = implementations
  .filter(r => r.type === 'implements')
  .map(r => yata.getEntity(r.sourceId));
```

#### Find Dependencies

| Natural Language Query | Equivalent API Command |
|----------------------|------------------------|
| `What does UserService depend on?` | `yata.getRelationships(userServiceId, 'out', { types: ['depends-on', 'imports', 'uses'] })` |
| `Show dependencies of OrderProcessor` | `yata.traverse(processorId, ['depends-on', 'imports'], 'forward', 1)` |

```typescript
// Natural language
const result = await yata.ask('What does UserService depend on?');

// Equivalent API call
const entity = await yata.getEntityByName('UserService');
const deps = await yata.getRelationships(entity.id, 'out');
const dependencies = deps
  .filter(r => ['depends-on', 'imports', 'uses'].includes(r.type))
  .map(r => yata.getEntity(r.targetId));
```

#### Find Entity

| Natural Language Query | Equivalent API Command |
|----------------------|------------------------|
| `Find UserService` | `yata.search('UserService')` |
| `Where is ConfigManager defined?` | `yata.getEntityByName('ConfigManager')` |
| `Locate the login method` | `yata.query({ textSearch: 'login' })` |

```typescript
// Natural language
const result = await yata.ask('Find UserService');

// Equivalent API call
const entities = await yata.search('UserService', 10);
// or
const entity = await yata.getEntityByName('UserService');
```

#### Find by Namespace

| Natural Language Query | Equivalent API Command |
|----------------------|------------------------|
| `Classes in app.services` | `yata.query({ entityFilters: { namespaces: ['app.services'], types: ['class'] } })` |
| `Show all classes in utils` | `yata.getEntitiesByNamespace('utils')` |

```typescript
// Natural language
const result = await yata.ask('Classes in app.services');

// Equivalent API call
const queryResult = await yata.query({
  entityFilters: {
    namespaces: ['app.services'],
    types: ['class'],
  },
});
```

#### Find Related

| Natural Language Query | Equivalent API Command |
|----------------------|------------------------|
| `Related to UserService` | `yata.getNeighbors(userServiceId, { direction: 'both' })` |
| `Entities related to Repository` | `yata.extractSubgraph(repositoryId, { depth: 1 })` |

```typescript
// Natural language
const result = await yata.ask('Related to UserService');

// Equivalent API call
const entity = await yata.getEntityByName('UserService');
const neighbors = await yata.getNeighbors(entity.id, { direction: 'both' });
```

#### Explain Relationship

| Natural Language Query | Equivalent API Command |
|----------------------|------------------------|
| `Relationship between UserService and Repository` | `yata.findPath(userServiceId, repositoryId)` |
| `How is A related to B?` | `yata.findPath(aId, bId, { direction: 'both' })` |

```typescript
// Natural language
const result = await yata.ask('Relationship between UserService and Repository');

// Equivalent API call
const entityA = await yata.getEntityByName('UserService');
const entityB = await yata.getEntityByName('Repository');
const path = await yata.findPath(entityA.id, entityB.id, {
  maxDepth: 5,
  direction: 'both',
});
```

### Advanced Usage

```typescript
// Query with configuration options
const result = await yata.ask('dependencies of UserService', {
  language: 'en',              // Explicit language
  fuzzyMatching: true,         // Enable fuzzy matching
  minConfidence: 0.7,          // Minimum confidence threshold
  maxResults: 50,              // Maximum results
  includeInferred: true,       // Include inferred relationships
});

// Result details
console.log('Query:', result.parsedQuery.originalQuery);
console.log('Intent:', result.parsedQuery.intent);
console.log('Subject:', result.parsedQuery.subject);
console.log('Confidence:', result.parsedQuery.confidence);
console.log('Entities:', result.entities.length);
console.log('Execution time:', result.executionTimeMs, 'ms');
```

### MCP Tool Integration

Natural language queries can also be used via the MCP server:

```json
// Query via MCP (sdd_ask_knowledge tool)
// Input:
{
  "question": "What functions call UserService?",
  "maxResults": 20
}
```

### Supported Intents

| Intent | Description | Example | Internal API |
|--------|-------------|---------|--------------|
| `find_entity` | Search for entity | "Find UserService" | `search()`, `getEntityByName()` |
| `find_callers` | Find callers | "What calls X?" | `getRelationships(id, 'in')` |
| `find_callees` | Find callees | "What does X call?" | `getRelationships(id, 'out')` |
| `find_implementations` | Find implementations | "Implementations of X" | `getRelationships(id, 'in', {types: ['implements']})` |
| `find_dependencies` | Find dependencies | "What does X depend on?" | `traverse(id, ['depends-on'], 'forward')` |
| `find_dependents` | Find dependents | "What depends on X?" | `traverse(id, ['depends-on'], 'backward')` |
| `find_related` | Find related entities | "Related to X" | `getNeighbors(id, {direction: 'both'})` |
| `find_by_type` | Search by type | "Show all classes" | `query({entityFilters: {types: [...]}})` |
| `find_by_namespace` | Search by namespace | "Classes in app.services" | `query({entityFilters: {namespaces: [...]}})` |
| `explain_relationship` | Explain relationship | "Relationship between A and B" | `findPath(idA, idB)` |
| `general_search` | General search | Fallback for unmatched | `search(keywords)` |

---

## 🧠 Reasoning Engine

### Running Inference

```typescript
// Apply inference rules
const inferenceResult = await yata.infer({
  rules: ['transitivity', 'type-compatibility'],
  maxIterations: 100,
});

console.log(`Inferred ${inferenceResult.inferredRelationships.length} new relationships`);
```

### Custom Inference Rules

```typescript
// Add custom rule
yata.addInferenceRule({
  id: 'service-uses-repository',
  name: 'Service Uses Repository',
  description: 'Services typically use repositories',
  condition: (source, target) => 
    source.type === 'class' && 
    source.name.endsWith('Service') &&
    target.type === 'interface' &&
    target.name.endsWith('Repository'),
  consequent: {
    type: 'uses',
    weight: 0.8,
  },
});
```

### Constraint Validation

```typescript
// Validate graph constraints
const validation = await yata.validate({
  constraints: ['no-circular-dependencies', 'single-inheritance'],
});

if (!validation.isValid) {
  console.log('Violations:', validation.violations);
}
```

---

## 📤 Import/Export

### JSON Format

```typescript
// Export
const jsonExport = await yata.exportJson('./backup.json');
console.log(`Exported ${jsonExport.entities.length} entities`);

// Import
const mergeResult = await yata.importJson('./backup.json', {
  merge: true,
  dryRun: false,
});

console.log(`Imported: ${mergeResult.entitiesAdded} added, ${mergeResult.entitiesUpdated} updated`);
```

### Unified Export API

```typescript
// Export with multiple formats
const exportResult = await yata.export({
  format: 'json',  // 'json' | 'rdf' | 'graphml'
  namespace: 'app.services',
  outputPath: './export/services.json',
});

// Incremental export (changes only)
const incrementalExport = await yata.exportIncremental(
  new Date('2024-01-01'),
  { format: 'json' }
);
```

---

## 🔄 KGPR (Knowledge Graph Pull Request)

KGPR is a workflow for sharing local knowledge graph changes with YATA Global.

### Creating KGPR

```typescript
import { createLocalKGPRManager } from '@nahisaho/yata-local';

const kgprManager = createLocalKGPRManager(yata.getDb());

const kgpr = await kgprManager.createKGPR({
  title: 'Share UserService patterns',
  description: 'Patterns learned from user authentication flow',
  namespace: 'app.services',
  entityTypes: ['class', 'interface'],
  privacyLevel: 'strict',  // 'strict' | 'moderate' | 'none'
  author: 'developer@example.com',
});

console.log('KGPR created:', kgpr.id);
```

### Privacy Levels

| Level | Description |
|-------|-------------|
| `strict` | Remove file paths, line numbers, sensitive metadata |
| `moderate` | Relativize file paths, keep line numbers, remove sensitive metadata |
| `none` | No filtering |

---

## 🌙 Wake-Sleep Learning

Wake-Sleep is a continuous learning cycle for learning and consolidating patterns from code.

```typescript
import { createLocalWakeSleepCycle } from '@nahisaho/yata-local';

const wakeSleep = createLocalWakeSleepCycle(yata.getDb(), {
  wakeObserveLimit: 1000,
  sleepMinClusterSize: 3,
  sleepSimilarityThreshold: 0.7,
  compressMinOccurrences: 5,
});

// Wake phase: observe code and extract patterns
const wakeResult = await wakeSleep.wake({
  namespace: 'app.services',
  entityTypes: ['class', 'function'],
});

// Sleep phase: consolidate and compress patterns
const sleepResult = await wakeSleep.sleep();

// Complete cycle
const cycleResult = await wakeSleep.runCycle({
  namespace: 'app',
});
```

---

## 📊 Statistics

```typescript
const stats = await yata.getStats();

console.log('Graph Statistics:');
console.log(`  Total entities: ${stats.totalEntities}`);
console.log(`  Total relationships: ${stats.totalRelationships}`);
console.log(`  Entities by type:`, stats.entitiesByType);
console.log(`  Relationships by type:`, stats.relationshipsByType);
```

---

## 📚 Related Documentation

- [YATA Global User Guide](./YATA-GLOBAL-GUIDE.md)
- [API Reference](./API-REFERENCE.md)
- [MUSUBIX User Guide](./USER-GUIDE.md)

---

**Last Updated**: 2026-01-11
**Package**: `@nahisaho/yata-local`
