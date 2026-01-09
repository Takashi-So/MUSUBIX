# @nahisaho/musubix-codegraph

**Multi-language Code Graph Analysis Engine for MUSUBIX**

[![npm version](https://img.shields.io/npm/v/@nahisaho/musubix-codegraph.svg)](https://www.npmjs.com/package/@nahisaho/musubix-codegraph)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## Overview

`@nahisaho/musubix-codegraph` is a high-performance code graph analysis library that provides:

- **AST Parsing**: Tree-sitter based multi-language code parsing (**16 languages** in v2.3.2)
- **Graph Engine**: Code entity and relationship graph construction
- **GraphRAG**: Graph-based Retrieval Augmented Generation for code search
- **YATA Integration**: Seamless integration with YATA knowledge graph

## Installation

```bash
npm install @nahisaho/musubix-codegraph
```

## Quick Start

### Direct Library Usage

```typescript
import { CodeGraph } from '@nahisaho/musubix-codegraph';

// Create instance
const codeGraph = new CodeGraph({
  storage: 'memory', // or 'sqlite', 'yata'
});

// Index a repository
const result = await codeGraph.index('/path/to/repo');
console.log(`Indexed ${result.entitiesIndexed} entities`);

// Query the graph
const deps = await codeGraph.findDependencies('UserService', { depth: 3 });
const callers = await codeGraph.findCallers('authenticate');

// GraphRAG search
const results = await codeGraph.globalSearch('authentication flow');

// Get statistics
const stats = await codeGraph.getStats();
```

### Using Individual Components

```typescript
import { ASTParser, GraphEngine, GraphRAGSearch } from '@nahisaho/musubix-codegraph';

// Parse a single file
const parser = new ASTParser();
const parseResult = await parser.parseFile('src/index.ts');

// Use graph engine directly
const graph = new GraphEngine(storage);
await graph.addEntity(entity);
const path = await graph.findPath('A', 'B');

// GraphRAG search
const search = new GraphRAGSearch(graph);
const communities = await search.detectCommunities();
```

## Supported Languages (16 languages - v2.3.2)

| Priority | Language | Extensions | Status |
|----------|----------|-----------|--------|
| **Existing** | TypeScript | `.ts`, `.tsx` | ✅ Full Support |
| **Existing** | JavaScript | `.js`, `.jsx`, `.mjs` | ✅ Full Support |
| **Existing** | Python | `.py`, `.pyw` | ✅ Full Support |
| **P0** | Rust | `.rs` | ✅ Full Support |
| **P0** | Go | `.go` | ✅ Full Support |
| **P0** | Java | `.java` | ✅ Full Support |
| **P1** | PHP | `.php` | ✅ Full Support |
| **P1** | C# | `.cs` | ✅ Full Support |
| **P1** | C | `.c`, `.h` | ✅ Full Support |
| **P1** | C++ | `.cpp`, `.hpp`, `.cc`, `.hh` | ✅ Full Support |
| **P1** | Ruby | `.rb` | ✅ Full Support |
| **P2** | HCL/Terraform | `.tf`, `.hcl` | ✅ Full Support |
| **P2** | Kotlin | `.kt`, `.kts` | ✅ Full Support |
| **P2** | Swift | `.swift` | ✅ Full Support |
| **P2** | Scala | `.scala`, `.sc` | ✅ Full Support |
| **P2** | Lua | `.lua` | ✅ Full Support |

**Entity Types Extracted:**
- Functions, Methods, Constructors
- Classes, Interfaces, Traits, Protocols
- Structs, Enums, Records, Unions
- Modules, Packages, Namespaces
- Variables, Constants, Properties
- Type Definitions, Templates
- Language-specific constructs (Terraform resources, Swift extensions, etc.)

## API Reference

### CodeGraph (Facade)

```typescript
class CodeGraph {
  // Indexing
  index(path: string): Promise<IndexResult>;
  reindex(path: string): Promise<IndexResult>;
  
  // Querying
  query(query: string): Promise<QueryResult>;
  findDependencies(entity: string, options?: DepOptions): Promise<Entity[]>;
  findCallers(entity: string): Promise<CallPath[]>;
  findCallees(entity: string): Promise<CallPath[]>;
  findImplementations(interfaceName: string): Promise<Entity[]>;
  analyzeModule(path: string): Promise<ModuleAnalysis>;
  
  // Code Retrieval
  getSnippet(entityId: string): Promise<CodeSnippet>;
  getFileStructure(path: string): Promise<FileStructure>;
  
  // GraphRAG
  globalSearch(query: string): Promise<SearchResult[]>;
  localSearch(entity: string, options?: LocalSearchOptions): Promise<SearchResult[]>;
  
  // Statistics
  getStats(): Promise<GraphStatistics>;
  
  // Events
  on(event: 'indexing:start' | 'indexing:progress' | 'indexing:complete', handler): void;
}
```

### Storage Options

```typescript
const codeGraph = new CodeGraph({
  storage: 'memory',  // In-memory (default, fast, no persistence)
});

const codeGraph = new CodeGraph({
  storage: 'sqlite',  // SQLite (persistent)
  sqlitePath: '.codegraph/index.db',
});

// YATA integration
import { YataDatabase } from '@nahisaho/yata-local';
import { createYataAdapter } from '@nahisaho/musubix-codegraph/storage';

const yata = new YataDatabase();
await yata.open();

const codeGraph = new CodeGraph({
  storage: createYataAdapter(yata),
});
```

## CLI Usage

When used with MUSUBIX CLI:

```bash
# Index repository
musubix cg index /path/to/repo

# Query graph
musubix cg query "UserService"

# Find dependencies
musubix cg deps UserService

# Find callers/callees
musubix cg callers functionName
musubix cg callees functionName

# Semantic search
musubix cg search "authentication flow"

# Show statistics
musubix cg stats

# Show supported languages (v2.3.2)
musubix cg languages        # Table format
musubix cg languages --json # JSON format
musubix cg langs            # Alias
```

## Performance

| Metric | Value |
|--------|-------|
| Indexing speed | ~32 entities/sec |
| Query response | < 500ms |
| Incremental index | < 2 sec |
| Memory usage | < 500MB |

## Requirements

- Node.js >= 20.0.0
- npm >= 10.0.0

## License

MIT License - see [LICENSE](../../LICENSE)

## Related

- [MUSUBIX](https://github.com/nahisaho/MUSUBIX) - Neuro-Symbolic AI Integration System
- [@nahisaho/yata-local](../yata-local) - Local Knowledge Graph Storage
- [CodeGraphMCPServer](https://github.com/nahisaho/CodeGraphMCPServer) - Original Python implementation
