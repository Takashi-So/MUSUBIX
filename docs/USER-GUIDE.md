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
8. [MCP Server Integration](#mcp-server-integration)
9. [YATA Integration](#yata-integration)
10. [Best Practices](#best-practices)
11. [Troubleshooting](#troubleshooting)

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

# Export learning data
musubix learn export --output learning-data.json

# Import learning data
musubix learn import learning-data.json
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

**Version**: 1.0.12  
**Last Updated**: 2026-01-03  
**MUSUBIX Project**
