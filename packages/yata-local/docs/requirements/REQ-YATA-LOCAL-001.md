# YATA Local Requirements

## Document Information

| 項目 | 内容 |
|------|------|
| Document ID | REQ-YATA-LOCAL-001 |
| Version | 1.0.0 |
| Status | Draft |
| Author | MUSUBIX Team |
| Created | 2026-01-06 |

## 1. Overview

YATA Localは、プロジェクトローカルの知識グラフを管理するTypeScriptライブラリです。
SQLiteを使用してローカルファイルシステムに知識グラフを永続化し、高速なクエリと推論を提供します。

## 2. Functional Requirements

### 2.1 Knowledge Graph Storage (REQ-YL-STORE)

#### REQ-YL-STORE-001: Local Database
THE system SHALL store knowledge graph data in SQLite database within the project directory.

#### REQ-YL-STORE-002: Schema Management
WHEN the database is initialized, THE system SHALL create necessary tables and indexes automatically.

#### REQ-YL-STORE-003: Entity Storage
THE system SHALL persist entities with properties: id, type, name, namespace, metadata, timestamps.

#### REQ-YL-STORE-004: Relationship Storage
THE system SHALL persist relationships with properties: sourceId, targetId, relationType, weight, metadata.

#### REQ-YL-STORE-005: Transaction Support
THE system SHALL support atomic transactions for bulk operations.

### 2.2 Query Operations (REQ-YL-QUERY)

#### REQ-YL-QUERY-001: Entity Search
WHEN a user queries by entity name or type, THE system SHALL return matching entities within 100ms for graphs under 100K nodes.

#### REQ-YL-QUERY-002: Path Finding
WHEN a user requests paths between two entities, THE system SHALL compute shortest paths using BFS/Dijkstra algorithms.

#### REQ-YL-QUERY-003: Subgraph Extraction
WHEN a user requests a subgraph around an entity, THE system SHALL return the N-hop neighborhood efficiently.

#### REQ-YL-QUERY-004: Pattern Matching
WHEN a user specifies a graph pattern, THE system SHALL find all matching subgraphs.

#### REQ-YL-QUERY-005: Full-Text Search
THE system SHALL support full-text search on entity names and descriptions.

### 2.3 Incremental Updates (REQ-YL-UPDATE)

#### REQ-YL-UPDATE-001: Add Entities
WHEN new source code is parsed, THE system SHALL add new entities to the knowledge graph.

#### REQ-YL-UPDATE-002: Update Entities
WHEN source code is modified, THE system SHALL update existing entities preserving their relationships.

#### REQ-YL-UPDATE-003: Delete Entities
WHEN source code files are deleted, THE system SHALL remove corresponding entities and orphan relationships.

#### REQ-YL-UPDATE-004: Merge Graphs
WHEN importing external knowledge, THE system SHALL merge entities by ID with conflict resolution.

#### REQ-YL-UPDATE-005: Change Tracking
THE system SHALL track all modifications with timestamps for audit and sync purposes.

### 2.4 Reasoning Engine (REQ-YL-REASON)

#### REQ-YL-REASON-001: Type Inference
WHEN entity types are ambiguous, THE system SHALL infer types from relationships and context.

#### REQ-YL-REASON-002: Relationship Inference
WHEN direct relationships are missing, THE system SHALL infer transitive relationships.

#### REQ-YL-REASON-003: Constraint Validation
THE system SHALL validate graph constraints (e.g., no circular inheritance, valid references).

#### REQ-YL-REASON-004: Confidence Scoring
THE system SHALL assign confidence scores to inferred knowledge.

### 2.5 Export/Import (REQ-YL-IO)

#### REQ-YL-IO-001: JSON Export
THE system SHALL export knowledge graphs to JSON format compatible with YATA Global.

#### REQ-YL-IO-002: JSON Import
WHEN importing from JSON, THE system SHALL validate schema and merge with existing data.

#### REQ-YL-IO-003: RDF Export
THE system SHALL export knowledge graphs to RDF/Turtle format.

#### REQ-YL-IO-004: Incremental Sync
THE system SHALL support incremental sync with YATA Global by tracking deltas.

## 3. Non-Functional Requirements

### 3.1 Performance (REQ-YL-PERF)

#### REQ-YL-PERF-001: Query Latency
THE system SHALL respond to queries within 100ms for graphs under 100K entities.

#### REQ-YL-PERF-002: Memory Usage
WHILE processing large graphs, THE system SHALL limit memory usage to 512MB.

#### REQ-YL-PERF-003: Startup Time
THE system SHALL initialize within 500ms for typical project sizes.

### 3.2 Reliability (REQ-YL-REL)

#### REQ-YL-REL-001: Data Integrity
THE system SHALL NOT corrupt data during crashes or power failures.

#### REQ-YL-REL-002: Backup Support
THE system SHALL support database backup and restore operations.

### 3.3 Security (REQ-YL-SEC)

#### REQ-YL-SEC-001: Local Only
THE system SHALL NOT transmit data to external servers without explicit user consent.

#### REQ-YL-SEC-002: Encryption Option
IF encryption is enabled, THEN THE system SHALL encrypt the database file at rest.

## 4. Integration Requirements

### 4.1 MUSUBIX Integration (REQ-YL-INT)

#### REQ-YL-INT-001: Core Integration
THE system SHALL integrate with @nahisaho/musubix-core for SDD workflow support.

#### REQ-YL-INT-002: MCP Server
THE system SHALL expose knowledge graph via MCP protocol for AI tool integration.

#### REQ-YL-INT-003: YATA Global Sync
WHEN connected to YATA Global, THE system SHALL synchronize local knowledge bidirectionally.

## 5. API Requirements

### 5.1 TypeScript API (REQ-YL-API)

```typescript
// Primary interfaces
interface YataLocal {
  // Database
  open(path: string): Promise<void>;
  close(): Promise<void>;
  
  // Entities
  addEntity(entity: Entity): Promise<string>;
  getEntity(id: string): Promise<Entity | null>;
  updateEntity(id: string, updates: Partial<Entity>): Promise<void>;
  deleteEntity(id: string): Promise<void>;
  
  // Relationships
  addRelationship(rel: Relationship): Promise<string>;
  getRelationships(entityId: string, direction?: 'in' | 'out' | 'both'): Promise<Relationship[]>;
  
  // Queries
  query(query: GraphQuery): Promise<QueryResult>;
  findPath(from: string, to: string, options?: PathOptions): Promise<Path[]>;
  getSubgraph(centerId: string, hops: number): Promise<Subgraph>;
  
  // Reasoning
  infer(rules: InferenceRule[]): Promise<InferenceResult>;
  validate(constraints: Constraint[]): Promise<ValidationResult>;
  
  // Sync
  exportDelta(since: Date): Promise<Delta>;
  importDelta(delta: Delta): Promise<MergeResult>;
}
```

## 6. Traceability

| Requirement | Design Element | Test Case |
|-------------|---------------|-----------|
| REQ-YL-STORE-001 | DES-YL-DB-001 | TST-YL-DB-001 |
| REQ-YL-QUERY-001 | DES-YL-QUERY-001 | TST-YL-QUERY-001 |
| REQ-YL-REASON-001 | DES-YL-REASON-001 | TST-YL-REASON-001 |
