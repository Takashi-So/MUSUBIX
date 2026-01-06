# YATA改善 設計書

**Document ID**: DES-YATA-IMPROVEMENTS-001  
**Version**: 1.0.0  
**Created**: 2026-01-06  
**Requirements**: REQ-YATA-IMPROVEMENTS-001 v1.1.0  
**Status**: Draft (Review Required)

---

## 1. 概要

YATA Local/Global改善のC4モデル設計。5フェーズに分けて設計：
1. インデックス最適化
2. エクスポート機能
3. YATA Global統合
4. コード生成強化
5. Web UI

---

## 2. C4 Context Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                         MUSUBIX System                          │
│                                                                 │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐     │
│  │ MUSUBIX CLI  │───▶│  YATA Local  │◀───│  YATA Global │     │
│  └──────────────┘    └──────────────┘    └──────────────┘     │
│         │                   │                   │              │
│         │                   │                   │              │
│         ▼                   ▼                   ▼              │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐     │
│  │   YATA UI    │    │   SQLite DB  │    │  Remote API  │     │
│  │  (Browser)   │    │              │    │              │     │
│  └──────────────┘    └──────────────┘    └──────────────┘     │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘

External:
  ┌─────────────┐    ┌─────────────┐
  │  Developer  │    │ CI/CD System│
  └─────────────┘    └─────────────┘
```

---

## 3. Phase 1: インデックス最適化 設計

### 3.1 Component: IndexOptimizer

**Location**: `packages/yata-local/src/index-optimizer.ts`  
**Implements**: REQ-YI-IDX-001, REQ-YI-IDX-002, REQ-YI-IDX-003

```typescript
interface IndexAnalysisResult {
  indexes: IndexInfo[];
  recommendations: IndexRecommendation[];
  queryStats: QueryStats[];
  analysisTimeMs: number;
}

interface IndexInfo {
  name: string;
  table: string;
  columns: string[];
  unique: boolean;
  usageCount: number;
  lastUsed?: Date;
}

interface IndexRecommendation {
  type: 'create' | 'drop' | 'modify';
  table: string;
  columns: string[];
  reason: string;
  estimatedImprovement: number; // percentage
}

interface QueryStats {
  query: string;
  avgTimeMs: number;
  executionCount: number;
  indexesUsed: string[];
}
```

### 3.2 Sequence: analyze-indexes

```
Developer -> CLI: musubix yata analyze-indexes
CLI -> IndexOptimizer: analyzeIndexes()
IndexOptimizer -> SQLite: PRAGMA index_list()
IndexOptimizer -> SQLite: SELECT * FROM sqlite_stat1
IndexOptimizer -> IndexOptimizer: calculateRecommendations()
IndexOptimizer -> CLI: IndexAnalysisResult
CLI -> Developer: JSON/Table output
```

### 3.3 Database Changes

新規テーブル追加（クエリログ）:
```sql
CREATE TABLE IF NOT EXISTS query_log (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  query_hash TEXT NOT NULL,
  query_pattern TEXT NOT NULL,
  execution_time_ms INTEGER NOT NULL,
  rows_examined INTEGER,
  indexes_used TEXT,
  timestamp TEXT NOT NULL
);

CREATE INDEX IF NOT EXISTS idx_query_log_hash ON query_log(query_hash);
CREATE INDEX IF NOT EXISTS idx_query_log_timestamp ON query_log(timestamp);
```

---

## 4. Phase 2: エクスポート機能 設計

### 4.1 Component: KnowledgeGraphIO

**Location**: `packages/yata-local/src/io.ts` (拡張)  
**Implements**: REQ-YI-EXP-001, REQ-YI-EXP-002, REQ-YI-EXP-003

```typescript
interface ExportOptions {
  format: 'json' | 'rdf' | 'graphml';
  namespace?: string;
  includeMetadata?: boolean;
  incremental?: boolean;
  since?: Date;
}

interface ImportOptions {
  format: 'json' | 'rdf' | 'graphml';
  mergeStrategy: 'skip' | 'overwrite' | 'merge';
  dryRun?: boolean;
}

interface ExportResult {
  success: boolean;
  entityCount: number;
  relationshipCount: number;
  fileSize: number;
  exportTimeMs: number;
  outputPath?: string;
}

interface ImportResult {
  success: boolean;
  entitiesCreated: number;
  entitiesUpdated: number;
  entitiesSkipped: number;
  relationshipsCreated: number;
  errors: ImportError[];
  importTimeMs: number;
}
```

### 4.2 Export Formats

#### JSON Format
```json
{
  "version": "1.0",
  "exported_at": "2026-01-06T00:00:00Z",
  "namespace": "project-management",
  "entities": [
    {
      "id": "ENT-001",
      "type": "class",
      "name": "ProjectService",
      "namespace": "project-management",
      "metadata": {}
    }
  ],
  "relationships": [
    {
      "id": "REL-001",
      "source_id": "ENT-001",
      "target_id": "ENT-002",
      "type": "implements"
    }
  ]
}
```

#### RDF/Turtle Format
```turtle
@prefix yata: <http://musubix.dev/yata#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

yata:ENT-001 a yata:Class ;
    rdfs:label "ProjectService" ;
    yata:namespace "project-management" .

yata:ENT-001 yata:implements yata:ENT-002 .
```

#### GraphML Format
```xml
<?xml version="1.0" encoding="UTF-8"?>
<graphml xmlns="http://graphml.graphdrawing.org/xmlns">
  <key id="type" for="node" attr.name="type" attr.type="string"/>
  <key id="name" for="node" attr.name="name" attr.type="string"/>
  <graph id="G" edgedefault="directed">
    <node id="ENT-001">
      <data key="type">class</data>
      <data key="name">ProjectService</data>
    </node>
    <edge id="REL-001" source="ENT-001" target="ENT-002"/>
  </graph>
</graphml>
```

---

## 5. Phase 3: YATA Global統合 設計

### 5.1 Component: GlobalSyncManager

**Location**: `packages/yata-local/src/sync.ts`  
**Implements**: REQ-YI-GLB-001, REQ-YI-GLB-002, REQ-YI-GLB-003

```typescript
interface SyncConfig {
  globalEndpoint: string;
  authToken?: string;
  namespace: string;
  syncDirection: 'push' | 'pull' | 'bidirectional';
  conflictStrategy: 'local-wins' | 'remote-wins' | 'manual';
}

interface SyncStatus {
  state: 'idle' | 'syncing' | 'error' | 'conflict';
  progress: number; // 0-100
  lastSyncAt?: Date;
  pendingChanges: number;
  conflicts: SyncConflict[];
}

interface SyncConflict {
  entityId: string;
  localVersion: Entity;
  remoteVersion: Entity;
  conflictType: 'update-update' | 'delete-update' | 'create-create';
}

interface SyncResult {
  success: boolean;
  uploaded: number;
  downloaded: number;
  conflicts: SyncConflict[];
  syncTimeMs: number;
}
```

### 5.2 Sync Protocol

```
1. LocalDB -> ChangeLog: Get changes since last sync
2. ChangeLog -> SyncManager: Pending changes
3. SyncManager -> GlobalAPI: POST /sync/push (changes + lastSyncId)
4. GlobalAPI -> SyncManager: Remote changes + conflicts
5. SyncManager -> ConflictResolver: Resolve conflicts
6. SyncManager -> LocalDB: Apply remote changes
7. SyncManager -> LocalDB: Update lastSyncId
```

### 5.3 State Machine: SyncState

```
     ┌─────────┐
     │  Idle   │◀───────────────────────────┐
     └────┬────┘                            │
          │ sync()                          │
          ▼                                 │
     ┌─────────┐                            │
     │Preparing│                            │
     └────┬────┘                            │
          │                                 │
          ▼                                 │
     ┌─────────┐    conflict    ┌─────────┐│
     │Uploading│───────────────▶│Conflict ││
     └────┬────┘                └────┬────┘│
          │                          │      │
          ▼                    resolve()    │
     ┌─────────┐                     │      │
     │Downloading◀───────────────────┘      │
     └────┬────┘                            │
          │                                 │
          ▼                                 │
     ┌─────────┐                            │
     │Finalizing────────────────────────────┘
     └─────────┘
```

---

## 6. Phase 4: コード生成強化 設計

### 6.1 Component: EnhancedCodeGenerator

**Location**: `packages/core/src/codegen/enhanced-generator.ts`  
**Implements**: REQ-YI-GEN-001, REQ-YI-GEN-002, REQ-YI-GEN-003

```typescript
interface CodeGenConfig {
  outputDir: string;
  language: 'typescript' | 'javascript';
  framework?: 'express' | 'fastify' | 'nestjs';
  includeTests: boolean;
  testFramework: 'vitest' | 'jest';
  templateDir?: string;
}

interface GeneratedCode {
  entities: GeneratedFile[];
  repositories: GeneratedFile[];
  services: GeneratedFile[];
  controllers: GeneratedFile[];
  tests: GeneratedFile[];
  traceabilityMap: TraceabilityEntry[];
}

interface GeneratedFile {
  path: string;
  content: string;
  requirementIds: string[];
  designElementIds: string[];
}

interface TraceabilityEntry {
  requirementId: string;
  designElementId: string;
  filePath: string;
  lineNumbers: number[];
}
```

### 6.2 Template System

```
templates/
├── entity.hbs           # Entity class template
├── repository.hbs       # Repository interface/impl
├── service.hbs          # Service class template
├── controller.hbs       # API controller template
├── test-unit.hbs        # Unit test template
├── test-integration.hbs # Integration test template
└── partials/
    ├── imports.hbs
    ├── jsdoc.hbs
    └── validation.hbs
```

### 6.3 Generation Pipeline

```
C4 Design Doc
     │
     ▼
┌─────────────┐
│ Parser      │ Parse Markdown/JSON design
└─────┬───────┘
      │
      ▼
┌─────────────┐
│ Analyzer    │ Detect patterns (Repository, Factory, etc.)
└─────┬───────┘
      │
      ▼
┌─────────────┐
│ Generator   │ Apply templates
└─────┬───────┘
      │
      ▼
┌─────────────┐
│ Formatter   │ Prettier/ESLint
└─────┬───────┘
      │
      ▼
Generated Files
```

---

## 7. Phase 5: Web UI 設計

### 7.1 Component: YataUIServer

**Location**: `packages/yata-ui/` (新規パッケージ)  
**Implements**: REQ-YI-WEB-001, REQ-YI-WEB-002, REQ-YI-WEB-003

```typescript
interface UIServerConfig {
  port: number;
  host: string;
  dbPath: string;
  openBrowser: boolean;
}

interface GraphVisualization {
  nodes: VisNode[];
  edges: VisEdge[];
  layout: 'force' | 'hierarchical' | 'circular';
}

interface VisNode {
  id: string;
  label: string;
  type: EntityType;
  namespace: string;
  x?: number;
  y?: number;
  color?: string;
  size?: number;
}

interface VisEdge {
  id: string;
  source: string;
  target: string;
  label: string;
  type: RelationType;
  weight?: number;
}
```

### 7.2 Architecture

```
┌─────────────────────────────────────────────────────┐
│                    Browser                          │
│  ┌─────────────────────────────────────────────┐   │
│  │              React App                       │   │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐    │   │
│  │  │ Graph   │  │ Search  │  │ Detail  │    │   │
│  │  │ View    │  │ Panel   │  │ Panel   │    │   │
│  │  │(Cytoscape│  │         │  │         │    │   │
│  │  └─────────┘  └─────────┘  └─────────┘    │   │
│  └─────────────────────────────────────────────┘   │
└───────────────────────┬─────────────────────────────┘
                        │ HTTP/WebSocket
                        ▼
┌─────────────────────────────────────────────────────┐
│                  Express Server                     │
│  ┌─────────────┐  ┌─────────────┐  ┌───────────┐  │
│  │ REST API    │  │ WebSocket   │  │ Static    │  │
│  │ /api/       │  │ /ws         │  │ /         │  │
│  └──────┬──────┘  └──────┬──────┘  └───────────┘  │
└─────────┼────────────────┼──────────────────────────┘
          │                │
          ▼                ▼
     ┌─────────────────────────┐
     │      YATA Local         │
     │      (SQLite)           │
     └─────────────────────────┘
```

### 7.3 API Endpoints

| Method | Path | Description |
|--------|------|-------------|
| GET | /api/entities | List entities with filters |
| GET | /api/entities/:id | Get entity details |
| GET | /api/relationships | List relationships |
| GET | /api/search?q=query | Full-text search |
| GET | /api/stats | Database statistics |
| WS | /ws | Real-time updates |

### 7.4 Frontend Components

```
src/
├── App.tsx
├── components/
│   ├── GraphView/
│   │   ├── GraphView.tsx      # Cytoscape.js wrapper
│   │   ├── NodeTooltip.tsx    # Hover details
│   │   └── GraphControls.tsx  # Zoom, layout buttons
│   ├── SearchPanel/
│   │   ├── SearchPanel.tsx
│   │   ├── FilterChips.tsx
│   │   └── SearchResults.tsx
│   └── DetailPanel/
│       ├── DetailPanel.tsx
│       ├── EntityDetails.tsx
│       └── RelationshipList.tsx
├── hooks/
│   ├── useGraph.ts
│   ├── useSearch.ts
│   └── useWebSocket.ts
└── api/
    └── client.ts
```

---

## 8. 技術スタック

### Phase 1-3 (Backend)
| Component | Technology |
|-----------|------------|
| Language | TypeScript |
| Database | SQLite (better-sqlite3) |
| HTTP Client | fetch / node-fetch |

### Phase 4 (Code Generation)
| Component | Technology |
|-----------|------------|
| Template Engine | Handlebars |
| AST Parser | TypeScript Compiler API |
| Formatter | Prettier |

### Phase 5 (Web UI)
| Component | Technology |
|-----------|------------|
| Server | Express.js |
| Frontend | React 18 |
| Graph Library | Cytoscape.js |
| WebSocket | ws |
| Build | Vite |
| Styling | Tailwind CSS |

---

## 9. トレーサビリティ

| Requirement | Design Element | File |
|-------------|----------------|------|
| REQ-YI-IDX-001 | IndexOptimizer.analyzeIndexes() | index-optimizer.ts |
| REQ-YI-IDX-002 | IndexOptimizer.createComposite() | index-optimizer.ts |
| REQ-YI-IDX-003 | QueryLogger.monitor() | index-optimizer.ts |
| REQ-YI-EXP-001 | KnowledgeGraphIO.export() | io.ts |
| REQ-YI-EXP-002 | KnowledgeGraphIO.import() | io.ts |
| REQ-YI-EXP-003 | KnowledgeGraphIO.exportIncremental() | io.ts |
| REQ-YI-GLB-001 | GlobalSyncManager.sync() | sync.ts |
| REQ-YI-GLB-002 | SyncStateManager | sync.ts |
| REQ-YI-GLB-003 | ConflictResolver | sync.ts |
| REQ-YI-GEN-001 | EnhancedCodeGenerator.generateFull() | enhanced-generator.ts |
| REQ-YI-GEN-002 | TestGenerator.generateComprehensive() | test-generator.ts |
| REQ-YI-GEN-003 | TemplateLoader | template-loader.ts |
| REQ-YI-WEB-001 | YataUIServer.start() | server.ts |
| REQ-YI-WEB-002 | SearchAPI.search() | api/search.ts |
| REQ-YI-WEB-003 | WebSocketServer.broadcast() | ws-server.ts |

---

## 10. レビュー依頼事項

1. **アーキテクチャ**: コンポーネント分割は適切か？
2. **技術選定**: Cytoscape.js vs D3.js の選択は妥当か？
3. **API設計**: REST APIのエンドポイント設計は十分か？
4. **スケーラビリティ**: 10万エンティティでの性能要件を満たせるか？

---

**Next Step**: レビュー完了後、Phase 1から実装開始

