# YATA Global User Guide

> **YATA Global** - Distributed Knowledge Graph Platform

## 📖 Overview

YATA Global (`@nahisaho/yata-global`) is a community-based knowledge sharing platform. It enables global sharing and searching of framework knowledge, design patterns, and best practices.

### Key Features

| Feature | Description |
|---------|-------------|
| **Framework Knowledge** | Knowledge base for various frameworks |
| **Pattern Sharing** | Share design patterns and code patterns |
| **KGPR** | Contribution via Knowledge Graph Pull Request |
| **Offline Mode** | Offline operation via local cache |
| **Sync Engine** | Automatic/manual data synchronization |
| **Authentication** | User authentication and access control |

---

## 🚀 Installation

```bash
npm install @nahisaho/yata-global
```

### Prerequisites

- Node.js >= 20.0.0
- npm >= 10.0.0

---

## 📘 Basic Usage

### Client Initialization

```typescript
import { createYataGlobal } from '@nahisaho/yata-global';

const yataGlobal = createYataGlobal({
  serverUrl: 'https://api.yata.example.com',  // API server URL
  offlineMode: false,      // Offline mode
  cacheSize: 100,          // Cache size (MB)
  autoSync: true,          // Auto sync
  syncInterval: 300000,    // Sync interval (5 minutes)
});

// Register event listeners
yataGlobal.on('sync:start', () => console.log('Sync started'));
yataGlobal.on('sync:complete', (result) => console.log('Sync complete:', result));
yataGlobal.on('sync:error', (error) => console.error('Sync error:', error));

// On exit
yataGlobal.close();
```

### Configuration Options

```typescript
interface SyncConfig {
  serverUrl: string;        // API server URL
  offlineMode: boolean;     // Offline mode (default: false)
  cacheSize: number;        // Local cache size (default: 100MB)
  autoSync: boolean;        // Auto sync (default: true)
  syncInterval: number;     // Sync interval (ms, default: 300000)
  retryAttempts: number;    // Retry attempts (default: 3)
  timeout: number;          // Timeout (ms)
}
```

---

## 🔐 Authentication

### Login

```typescript
// Login with username/password
const token = await yataGlobal.login({
  username: 'developer',
  password: 'secure-password',
});

console.log('Logged in, token expires:', token.expiresAt);
```

### Token Authentication

```typescript
// Login with existing token
const token = await yataGlobal.loginWithToken('your-access-token');
```

### Logout

```typescript
await yataGlobal.logout();
```

### Check Authentication Status

```typescript
if (yataGlobal.isAuthenticated()) {
  const user = await yataGlobal.getCurrentUser();
  console.log('Current user:', user?.username);
}
```

---

## 📚 Framework Knowledge

### Search Frameworks

```typescript
const result = await yataGlobal.searchFrameworks({
  query: 'react',
  category: 'web-frontend',
  language: 'typescript',
  tags: ['ui', 'component'],
  minQuality: 70,
  sortBy: 'popularity',  // 'popularity' | 'quality' | 'updated' | 'relevance'
  limit: 20,
  offset: 0,
});

console.log(`Found ${result.total} frameworks`);
for (const fw of result.items) {
  console.log(`- ${fw.name} v${fw.version} (${fw.popularity}★)`);
}
```

### Framework Categories

```typescript
type FrameworkCategory =
  | 'web-frontend'     // Web Frontend
  | 'web-backend'      // Web Backend
  | 'mobile'           // Mobile
  | 'desktop'          // Desktop
  | 'database'         // Database
  | 'orm'              // ORM
  | 'testing'          // Testing
  | 'build-tool'       // Build Tool
  | 'cli'              // CLI
  | 'ai-ml'            // AI/ML
  | 'devops'           // DevOps
  | 'cloud'            // Cloud
  | 'security'         // Security
  | 'networking'       // Networking
  | 'data-processing'  // Data Processing
  | 'logging'          // Logging
  | 'monitoring'       // Monitoring
  | 'documentation'    // Documentation
  | 'other';           // Other
```

### Get Individual Framework

```typescript
const framework = await yataGlobal.getFramework('react-18');
if (framework) {
  console.log('Name:', framework.name);
  console.log('Version:', framework.version);
  console.log('Description:', framework.description);
  console.log('Docs:', framework.documentationUrl);
  console.log('Quality:', framework.quality);
  console.log('Tags:', framework.tags.join(', '));
}
```

---

## 🧩 Patterns

### Search Patterns

```typescript
const patterns = await yataGlobal.searchPatterns({
  query: 'repository pattern',
  category: 'data-access',
  language: 'typescript',
  sortBy: 'quality',
  limit: 20,
});

for (const pattern of patterns.items) {
  console.log(`- ${pattern.name}: ${pattern.description}`);
  console.log(`  Rating: ${pattern.rating.average}/5 (${pattern.downloads} downloads)`);
}
```

### Pattern Categories

```typescript
type PatternCategory =
  | 'architecture'      // Architecture
  | 'design-pattern'    // Design Pattern
  | 'testing'           // Testing
  | 'error-handling'    // Error Handling
  | 'authentication'    // Authentication
  | 'authorization'     // Authorization
  | 'api-design'        // API Design
  | 'data-access'       // Data Access
  | 'validation'        // Validation
  | 'logging'           // Logging
  | 'caching'           // Caching
  | 'async'             // Async
  | 'configuration'     // Configuration
  | 'other';            // Other
```

### Share Patterns

```typescript
// Authentication required
if (!yataGlobal.isAuthenticated()) {
  await yataGlobal.login({ username, password });
}

const patternId = await yataGlobal.sharePattern({
  name: 'Service Layer Pattern',
  description: 'Service layer pattern for encapsulating business logic',
  category: 'architecture',
  language: 'typescript',
  frameworks: ['nestjs', 'express'],
  template: `
export class {{ServiceName}} {
  constructor(private readonly repository: I{{EntityName}}Repository) {}
  
  async create(dto: Create{{EntityName}}Dto): Promise<{{EntityName}}> {
    return this.repository.save(dto);
  }
}`,
  tags: ['service', 'layer', 'architecture'],
  visibility: 'public',
  official: false,
});

console.log('Pattern shared:', patternId);
```

### Rate Patterns

```typescript
await yataGlobal.ratePattern('pattern-id', 5);  // 1-5 rating
```

---

## 🔄 Sync

### Manual Sync

```typescript
const syncResult = await yataGlobal.sync();

console.log('Sync result:');
console.log(`  Frameworks synced: ${syncResult.frameworksSynced}`);
console.log(`  Patterns synced: ${syncResult.patternsSynced}`);
console.log(`  Duration: ${syncResult.duration}ms`);
```

### Sync Status

```typescript
const status = yataGlobal.getSyncStatus();

console.log('Sync status:');
console.log(`  Last sync: ${status.lastSyncAt}`);
console.log(`  Pending changes: ${status.pendingChanges}`);
console.log(`  Is syncing: ${status.isSyncing}`);
```

### Offline Mode

```typescript
// Enable offline mode
yataGlobal.enableOfflineMode();

// Disable offline mode (go online)
yataGlobal.disableOfflineMode();
```

In offline mode:
- Data is retrieved from local cache
- Change operations are saved to sync queue
- Auto-sync on reconnection

---

## 📤 KGPR (Knowledge Graph Pull Request)

KGPR is a workflow for contributing local knowledge graph changes to YATA Global.

### KGPR Workflow

```
┌─────────────────────────────────────────────────────────────┐
│                    KGPR Workflow                            │
│                                                             │
│  [YATA Local]              [YATA Global]                   │
│       │                         │                          │
│  1. Create KGPR                 │                          │
│  (Apply privacy filter)         │                          │
│       │                         │                          │
│       ▼                         │                          │
│  2. Calculate diff              │                          │
│  (Entities & relationships)     │                          │
│       │                         │                          │
│       └─── 3. Submit KGPR ─────►│                          │
│                                 │                          │
│                            4. Review                       │
│                            (approve/reject)                │
│                                 │                          │
│                            5. Merge                        │
│                            (Conflict resolution)           │
│                                 │                          │
│       ◄───── 6. Notification ───┘                          │
└─────────────────────────────────────────────────────────────┘
```

### KGPR REST API Endpoints

| Method | Endpoint | Description |
|--------|----------|-------------|
| GET | `/api/v1/kgprs` | List KGPRs |
| POST | `/api/v1/kgprs` | Create KGPR |
| GET | `/api/v1/kgprs/:id` | Get KGPR details |
| POST | `/api/v1/kgprs/:id/review` | Review KGPR |
| POST | `/api/v1/kgprs/:id/merge` | Merge KGPR |

### Create KGPR (REST API)

```bash
curl -X POST http://localhost:3000/api/v1/kgprs \
  -H "Content-Type: application/json" \
  -d '{
    "title": "Add UserService pattern",
    "description": "Patterns learned from user authentication flow",
    "sourceNamespace": "app.services",
    "labels": ["pattern", "authentication"],
    "diff": {
      "entities": {
        "added": [
          {
            "changeType": "add",
            "localId": "entity-1",
            "name": "UserService",
            "entityType": "class",
            "namespace": "app.services",
            "description": "User management service"
          }
        ],
        "updated": [],
        "deleted": []
      },
      "relationships": {
        "added": [],
        "updated": [],
        "deleted": []
      },
      "stats": {
        "entitiesAdded": 1,
        "entitiesUpdated": 0,
        "entitiesDeleted": 0,
        "relationshipsAdded": 0,
        "relationshipsUpdated": 0,
        "relationshipsDeleted": 0,
        "totalChanges": 1
      }
    }
  }'
```

### Review KGPR (REST API)

```bash
# Approve
curl -X POST http://localhost:3000/api/v1/kgprs/KGPR-abc123/review \
  -H "Content-Type: application/json" \
  -d '{
    "decision": "approve",
    "comment": "LGTM! Great pattern."
  }'

# Request changes
curl -X POST http://localhost:3000/api/v1/kgprs/KGPR-abc123/review \
  -H "Content-Type: application/json" \
  -d '{
    "decision": "changes_requested",
    "comment": "Please add more documentation."
  }'
```

### Merge KGPR (REST API)

```bash
curl -X POST http://localhost:3000/api/v1/kgprs/KGPR-abc123/merge \
  -H "Content-Type: application/json" \
  -d '{
    "conflictStrategy": "skip_conflicts"
  }'
```

### Conflict Types

```typescript
type ConflictType =
  | 'entity_exists'        // Entity with same name already exists
  | 'entity_modified'      // Entity was modified after KGPR creation
  | 'entity_deleted'       // Entity was deleted after KGPR creation
  | 'relationship_exists'  // Relationship already exists
  | 'relationship_broken'  // Source/target entity doesn't exist
  | 'circular_dependency'  // Would create circular dependency
  | 'schema_violation';    // Global KG schema violation

type ConflictResolution =
  | 'use_local'   // Use local (KGPR) value
  | 'use_global'  // Keep global value
  | 'merge'       // Merge both values
  | 'skip'        // Skip this change
  | 'rename';     // Rename to avoid conflict
```

---

## 🐳 Docker Environment

### Start with Docker Compose

```bash
cd docker
docker compose up -d
```

### Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Docker Network                           │
│  ┌──────────────────┐    ┌──────────────────────────────┐  │
│  │  yata-global     │    │      musubix-dev             │  │
│  │  (Port 3000)     │◄───│  (Development Environment)   │  │
│  │                  │    │                              │  │
│  │  - HTTP API      │    │  - MUSUBIX CLI               │  │
│  │  - KGPR Server   │    │  - YATA Local                │  │
│  │  - Pattern Store │    │  - Project Workspace         │  │
│  └──────────────────┘    └──────────────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
```

### Health Check

```bash
curl http://localhost:3000/health
# {"status":"healthy","timestamp":"...","version":"1.0.0"}
```

### E2E Test

```bash
cd docker
./test-kgpr-flow.sh
```

---

## 🔧 HTTP Server

YATA Global HTTP server can be started standalone.

### Start Server

```bash
# Via npm
npx yata-global-server

# Or directly
node packages/yata-global/dist/bin/yata-global-server.js
```

### Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `PORT` | 3000 | Listen port |
| `HOST` | 0.0.0.0 | Listen host |

### API Endpoints

| Method | Path | Description |
|--------|------|-------------|
| GET | `/health` | Health check |
| POST | `/auth/login` | Login |
| POST | `/auth/logout` | Logout |
| GET | `/api/v1/kgprs` | List KGPRs |
| POST | `/api/v1/kgprs` | Create KGPR |
| GET | `/api/v1/kgprs/:id` | Get KGPR |
| POST | `/api/v1/kgprs/:id/review` | Review |
| POST | `/api/v1/kgprs/:id/merge` | Merge |
| GET | `/api/v1/patterns` | List patterns |
| POST | `/api/v1/patterns` | Create pattern |
| GET | `/api/v1/patterns/:id` | Get pattern |
| GET | `/api/v1/frameworks` | List frameworks |
| GET | `/api/v1/frameworks/:id` | Get framework |

---

## 📱 Events

YataGlobal emits the following events:

```typescript
// Authentication events
yataGlobal.on('auth:login', (user) => {
  console.log('User logged in:', user.username);
});

yataGlobal.on('auth:logout', () => {
  console.log('User logged out');
});

// Sync events
yataGlobal.on('sync:start', () => {
  console.log('Sync started');
});

yataGlobal.on('sync:complete', (result) => {
  console.log('Sync completed:', result);
});

yataGlobal.on('sync:error', (error) => {
  console.error('Sync error:', error);
});

// Connection events
yataGlobal.on('connection:online', () => {
  console.log('Online');
});

yataGlobal.on('connection:offline', () => {
  console.log('Offline');
});
```

---

## 🔒 Privacy Filter

When creating a KGPR, a privacy filter is applied.

### Privacy Levels

| Level | Description |
|-------|-------------|
| `strict` | Completely remove file paths, line numbers, sensitive metadata |
| `moderate` | Relativize file paths, keep line numbers, remove sensitive metadata |
| `none` | No filtering |

### Sensitive Information Detection

Information automatically filtered:
- API keys
- Passwords
- Tokens
- Personal information (email addresses, etc.)
- Internal path information

---

## 📚 Related Documentation

- [YATA Local User Guide](./YATA-LOCAL-GUIDE.md)
- [Docker Environment README](../docker/README.md)
- [API Reference](./API-REFERENCE.md)
- [MUSUBIX User Guide](./USER-GUIDE.md)

---

## 📝 Version History

| Version | Major Changes |
|---------|---------------|
| v2.4.1 | HTTP server added, Docker support |
| v1.7.0 | MergeEngine enhancement, conflict resolution |
| v1.6.5 | KGPR, privacy filter added |
| v1.0.0 | Initial release |

---

**Last Updated**: 2026-01-11
**Package**: `@nahisaho/yata-global`
