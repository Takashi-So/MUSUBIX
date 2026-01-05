# MUSUBIX - Neuro-Symbolic AI Integration System

[![CI](https://github.com/nahisaho/MUSUBIX/actions/workflows/ci.yml/badge.svg)](https://github.com/nahisaho/MUSUBIX/actions/workflows/ci.yml)
[![npm version](https://img.shields.io/npm/v/musubix.svg)](https://www.npmjs.com/package/musubix)
[![npm core](https://img.shields.io/npm/v/@nahisaho/musubix-core.svg?label=@nahisaho/musubix-core)](https://www.npmjs.com/package/@nahisaho/musubix-core)
[![npm mcp](https://img.shields.io/npm/v/@nahisaho/musubix-mcp-server.svg?label=@nahisaho/musubix-mcp-server)](https://www.npmjs.com/package/@nahisaho/musubix-mcp-server)
[![Node.js Version](https://img.shields.io/badge/node-%3E%3D20.0.0-brightgreen)](https://nodejs.org/)
[![License](https://img.shields.io/badge/license-MIT-blue)](LICENSE)
[![TypeScript](https://img.shields.io/badge/TypeScript-5.3-blue)](https://www.typescriptlang.org/)
[![Tests](https://img.shields.io/badge/tests-775%20passing-brightgreen)](https://github.com/nahisaho/MUSUBIX)

> Next-generation AI Coding System powered by MUSUBI × YATA Integration
>
> **v1.4.1** - Consistency Validation & OWL Constraint Checking

**[日本語版 README](README.ja.md)**

## Overview

MUSUBIX is an innovative AI coding system that integrates **Neural (LLM)** and **Symbolic (Knowledge Graph)** reasoning. It combines MUSUBI SDD methodology with YATA knowledge graph reasoning to support high-quality software development.

### Features

- 🧠 **Neuro-Symbolic Integration** - Fusion of LLM creativity and YATA knowledge graph precision
- � **Symbolic Reasoning** - Formal verification, hallucination detection, constitution enforcement
- 📝 **EARS Requirements Analysis** - Conversion and validation from natural language to formal requirements
- 🎨 **Design Pattern Recommendations** - Context-based C4 model and ADR generation
- ✅ **Test-Driven Development** - Quality assurance through Test-First principles
- 🔗 **Complete Traceability** - Tracking from requirements to code
- 💬 **Interactive Q&A Hearing** - Dialogue-based requirements gathering support
- 🌐 **Internationalization (i18n)** - Japanese and English support
- 🔒 **Security Scanning** - Vulnerability detection, secret scanning, OWASP patterns
- 📚 **Self-Learning System** - Adaptive improvement through feedback collection and pattern extraction
- 🏗️ **C4 Code Generation** - Generate TypeScript skeleton from C4 design documents
- ⚙️ **Quality Gates** - Automated quality validation before phase transitions

## Architecture

```mermaid
flowchart TB
    subgraph MUSUBIX["MUSUBIX System"]
        subgraph Packages["Packages"]
            Core["@nahisaho/musubix-core"]
            MCP["@nahisaho/musubix-mcp-server"]
            YATA["@nahisaho/musubix-yata-client"]
        end
        
        Core <--> MCP
        MCP <--> YATA
        
        subgraph Integration["Neuro-Symbolic Integration"]
            NSI["LLM Creativity + Knowledge Graph Precision"]
        end
        
        Core --> Integration
        MCP --> Integration
        YATA --> Integration
    end
```

## Project Structure

| Path | Description |
|------|-------------|
| `packages/core/` | Core library (224 modules) |
| `packages/core/auth/` | Authentication & Authorization |
| `packages/core/cli/` | CLI Interface |
| `packages/core/codegen/` | Code Generation & Analysis |
| `packages/core/design/` | Design Patterns & C4 Models |
| `packages/core/error/` | Error Handling |
| `packages/core/explanation/` | Explanation Generation & Visualization |
| `packages/core/learning/` | Self-Learning & Pattern Extraction |
| `packages/core/requirements/` | Requirements Analysis & Decomposition |
| `packages/core/symbolic/` | Symbolic Reasoning |
| `packages/core/traceability/` | Traceability |
| `packages/core/types/` | Type Definitions |
| `packages/core/utils/` | Utilities |
| `packages/core/validators/` | EARS Validation |
| `packages/mcp-server/` | MCP Server (16 tools, 3 prompts) |
| `packages/yata-client/` | YATA Client |
| `packages/pattern-mcp/` | **Pattern Learning (NEW!)** |
| `packages/ontology-mcp/` | **Ontology Engine (NEW!)** |
| `packages/wake-sleep/` | **Wake-Sleep Learning (NEW!)** |
| `packages/sdd-ontology/` | **SDD Ontology (NEW!)** |
| `steering/` | Project Memory |
| `storage/` | Specifications & Artifacts |
| `templates/` | Templates |
| `docs/` | Documentation |

## Requirements

- Node.js >= 20.0.0
- npm >= 10.0.0
- TypeScript >= 5.3

## Installation

### npm/npx (Recommended)

```bash
# Global installation
npm install -g musubix

# Run directly with npx
npx musubix init
npx musubix --help

# Start MCP Server
npx @nahisaho/musubix-mcp-server
npx musubix-mcp --transport stdio
```

### Scoped Packages

```bash
# Install individual packages
npm install @nahisaho/musubix-core
npm install @nahisaho/musubix-mcp-server
npm install @nahisaho/musubix-yata-client
```

### Build from Source

```bash
git clone https://github.com/nahisaho/MUSUBIX.git
cd MUSUBIX
npm install
npm run build
```

## Development

```bash
# Build
npm run build

# Run tests
npm test

# Lint
npm run lint

# Type check
npm run type-check
```

## Key Features

### Requirements Definition (Article II Compliant)

- **EARS Validation**: Easy Approach to Requirements Syntax pattern validation
- **Interactive Q&A Hearing**: Dialogue-based requirements gathering
- **Requirements Decomposition**: Breaking down large requirements into implementation units
- **Related Requirements Search**: Automatic detection of similar and dependent requirements

### Design Generation (Article III Compliant)

- **C4 Model Generation**: Context/Container/Component/Code diagrams
- **ADR Generation**: Architecture Decision Records
- **Pattern Detection**: Automatic detection and recommendation of design patterns
- **SOLID Validation**: SOLID principle compliance checking

### Code Generation & Verification

- **Static Analysis**: Quality metrics and complexity calculation
- **Security Scanning**: Vulnerability detection
- **Test Generation**: Unit and integration test generation
- **Coverage Reporting**: Test coverage measurement

### MCP Server

Provides 16 tools (9 SDD + 7 Pattern) and 3 prompts:

```bash
# Start MCP Server
npx @nahisaho/musubix-mcp-server
```

## Documentation

| Document | Description |
|----------|-------------|
| [Requirements Specification](storage/specs/REQ-MUSUBIX-001.md) | EARS format functional/non-functional requirements |
| [Design Document](storage/specs/DES-MUSUBIX-001.md) | C4 model and ADR-based design |
| [Task Definition](storage/specs/TSK-MUSUBIX-001.md) | 56 tasks sprint plan |
| [API Reference](docs/API-REFERENCE.md) | Public API specification |
| [Symbolic Integration](storage/specs/REQ-SYMB-001.md) | Neuro-Symbolic requirements (27 requirements) |

## Symbolic Reasoning Module (v1.2.0)

The new symbolic reasoning module provides:

### Phase 1: Foundation
- **SemanticCodeFilterPipeline** - LLM output semantic validation
- **HallucinationDetector** - Undefined symbol/invalid import detection
- **ConstitutionRuleRegistry** - 9 Constitution articles enforcement
- **ConfidenceEstimator** - AST complexity, requirement coverage scoring
- **ConfidenceBasedRouter** - Confidence-based routing decisions
- **ErrorHandler** - Graceful degradation

### Phase 2: Formal Verification
- **EarsToFormalSpecConverter** - EARS → SMT-LIB conversion
- **VerificationConditionGenerator** - Verification condition (VC) generation
- **Z3Adapter** - Z3 SMT solver integration
- **SecurityScanner** - OWASP patterns, secret detection

### Phase 3: Advanced Features
- **CandidateRanker** - Multi-criteria candidate scoring
- **ResultBlender** - Neural/Symbolic result integration (3 strategies)
- **ExtensibleRuleConfig** - YAML/JSON rule configuration
- **AuditLogger** - SHA-256 hash-chain tamper detection
- **PerformanceBudget** - Step-level budgets, SLO metrics
- **QualityGateValidator** - Automated quality gate validation

## Wake-Sleep Learning Cycle (v1.3.0)

Continuous learning system based on the Wake-Sleep algorithm:

| Phase | Processing |
|-------|------------|
| **Wake** | Code observation → Pattern extraction → Knowledge graph update |
| **Sleep** | Pattern consolidation → Similar pattern compression → Memory optimization |

### Key Components
- **WakeSleepCycle** - Learning cycle orchestration
- **PatternLibrary** - Persistent pattern storage management
- **PatternOntologyBridge** - Pattern ↔ Ontology bidirectional conversion
- **N3Store** - RDF/OWL-based knowledge graph storage

### New MCP Tools (7 tools)
- `pattern_extract` - Extract patterns from code
- `pattern_compress` - Abstraction and compression of patterns
- `pattern_store` - Save to pattern library
- `pattern_query` - Search and retrieve patterns
- `pattern_consolidate` - Consolidate similar patterns
- `ontology_query` - Query ontology graph
- `ontology_infer` - Execute ontology-based inference

## Constitutional Articles (9 Articles)

MUSUBIX adheres to the following 9 constitutional articles:

1. **Specification First** - Requirements before implementation
2. **Design Before Code** - Design before coding
3. **Single Source of Truth** - Project memory is authoritative
4. **Traceability** - Tracking from requirements to code
5. **Incremental Progress** - Small, frequent deliveries
6. **Decision Documentation** - Decisions recorded as ADRs
7. **Quality Gates** - Phase validation required
8. **User-Centric** - Document user value
9. **Continuous Learning** - Retrospectives and improvements

## License

MIT License - See [LICENSE](LICENSE) for details

## Author

nahisaho

## Changelog

See [CHANGELOG.md](CHANGELOG.md)

---

**Document ID**: README  
**Version**: 1.3.0  
**Last Updated**: 2026-01-05
