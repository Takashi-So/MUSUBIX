# musubix

MUSUBIX - Neuro-Symbolic AI Integration System for Software Development

## Installation

```bash
npm install musubix
```

This will install all MUSUBIX packages:

- `@nahisaho/musubix-core` - Core library (CLI, EARS validation, code generation)
- `@nahisaho/musubix-mcp-server` - MCP Server (19 tools, 3 prompts)
- `@nahisaho/musubix-security` - Security analysis
- `@nahisaho/musubix-formal-verify` - Formal verification with Z3
- `@nahisaho/musubix-yata-client` - YATA knowledge graph client
- `@nahisaho/yata-local` - Local SQLite-based knowledge graph
- `@nahisaho/yata-global` - Distributed knowledge graph platform
- `@nahisaho/yata-scale` - Distributed sharding and caching
- `@nahisaho/musubix-pattern-mcp` - Pattern learning MCP
- `@nahisaho/musubix-ontology-mcp` - Ontology reasoning MCP
- `@nahisaho/musubix-wake-sleep` - Wake-Sleep learning cycle
- `@nahisaho/musubix-sdd-ontology` - SDD methodology ontology
- `@nahisaho/musubix-dfg` - Data Flow Graph extraction
- `@nahisaho/musubix-lean` - Lean 4 theorem prover integration
- `@nahisaho/musubix-library-learner` - API pattern learning
- `@nahisaho/musubix-neural-search` - Semantic code search
- `@nahisaho/musubix-synthesis` - Program synthesis

## Usage

### CLI

```bash
npx musubix --help
npx musubix init
npx musubix requirements analyze <file>
npx musubix design generate <file>
npx musubix design traceability            # REQ↔DES traceability validation (v3.1.0)
npx musubix codegen generate <file>
npx musubix codegen status <spec>          # Status transition code generation (v3.1.0)
npx musubix scaffold domain-model <name>   # DDD project scaffolding
npx musubix scaffold domain-model <name> -v "Price,Email"  # With Value Objects (v3.1.0)
npx musubix scaffold domain-model <name> -s "Order,Task"   # With status machines (v3.1.0)
```

### Library

```typescript
import { EarsValidator, CodeGenerator } from 'musubix';
import { security, synthesis, neuralSearch } from 'musubix';

// Core features
const validator = new EarsValidator();
const result = validator.validate(requirement);

// Advanced features
const synthesizer = synthesis.createEnhancedPBESynthesizer();
const searcher = neuralSearch.createHybridRanker();
```

## Documentation

- [User Guide](https://github.com/nahisaho/MUSUBIX/blob/main/docs/USER-GUIDE.md)
- [API Reference](https://github.com/nahisaho/MUSUBIX/blob/main/docs/API-REFERENCE.md)
- [AGENTS.md](https://github.com/nahisaho/MUSUBIX/blob/main/AGENTS.md) - For AI coding agents

## License

MIT
