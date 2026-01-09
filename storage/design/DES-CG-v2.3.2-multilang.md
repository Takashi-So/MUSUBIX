# MUSUBIX v2.3.2 設計書

## 多言語AST解析拡張（CodeGraph Multi-Language Support）

**Document ID**: DES-CG-MULTILANG
**Version**: 2.3.2
**Status**: Draft
**Created**: 2026-01-09
**Author**: AI Agent (Claude)
**Requirements**: REQ-CG-MULTILANG

---

## 1. C4モデル設計

### 1.1 Level 1: System Context

```
┌─────────────────────────────────────────────────────────────────────┐
│                        External Systems                              │
└─────────────────────────────────────────────────────────────────────┘
        │                    │                    │
        ▼                    ▼                    ▼
┌───────────────┐   ┌───────────────┐   ┌───────────────┐
│   Developer   │   │  CI/CD Tool   │   │  MCP Client   │
│   (User)      │   │  (GitHub      │   │  (Claude/     │
│               │   │   Actions)    │   │   Copilot)    │
└───────┬───────┘   └───────┬───────┘   └───────┬───────┘
        │                    │                    │
        │      CLI           │      CLI           │      MCP
        ▼                    ▼                    ▼
┌─────────────────────────────────────────────────────────────────────┐
│                                                                      │
│                     MUSUBIX CodeGraph System                         │
│                                                                      │
│   • Multi-language AST parsing (16 languages)                        │
│   • Code knowledge graph construction                                │
│   • GraphRAG-based semantic search                                   │
│   • Entity/Relation extraction                                       │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
        │                    │                    │
        ▼                    ▼                    ▼
┌───────────────┐   ┌───────────────┐   ┌───────────────┐
│  Source Code  │   │   SQLite DB   │   │  YATA Local   │
│  Repository   │   │   (Graph      │   │  (Knowledge   │
│  (16 langs)   │   │    Storage)   │   │    Graph)     │
└───────────────┘   └───────────────┘   └───────────────┘
```

### 1.2 Level 2: Container Diagram

```
┌─────────────────────────────────────────────────────────────────────┐
│                     MUSUBIX CodeGraph Package                        │
│                    (@nahisaho/musubix-codegraph)                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │                    CodeGraph Facade                           │   │
│  │                    (codegraph.ts)                             │   │
│  │                                                               │   │
│  │  • index(path)     - Index directory                          │   │
│  │  • query(options)  - Query entities                           │   │
│  │  • search(query)   - Semantic search                          │   │
│  │  • getStats()      - Get statistics                           │   │
│  └──────────────────────────────────────────────────────────────┘   │
│           │                    │                    │                │
│           ▼                    ▼                    ▼                │
│  ┌─────────────┐     ┌─────────────┐     ┌─────────────┐            │
│  │   Indexer   │     │   GraphRAG  │     │    Graph    │            │
│  │             │     │   Search    │     │   Engine    │            │
│  │ indexer/    │     │ graphrag/   │     │ graph/      │            │
│  └──────┬──────┘     └─────────────┘     └─────────────┘            │
│         │                                                            │
│         ▼                                                            │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │                      AST Parser                               │   │
│  │                    (parser/ast-parser.ts)                     │   │
│  │                                                               │   │
│  │  • parseFile(path)    - Parse single file                     │   │
│  │  • parseContent()     - Parse code string                     │   │
│  │  • getLanguage()      - Detect language                       │   │
│  └──────────────────────────────────────────────────────────────┘   │
│         │                                                            │
│         ▼                                                            │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │                Language Extractors (NEW)                      │   │
│  │               (parser/extractors/*.ts)                        │   │
│  │                                                               │   │
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐             │   │
│  │  │ Python  │ │TypeScript│ │  Rust   │ │   Go    │             │   │
│  │  └─────────┘ └─────────┘ └─────────┘ └─────────┘             │   │
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐             │   │
│  │  │  Java   │ │   PHP   │ │   C#    │ │  C/C++  │             │   │
│  │  └─────────┘ └─────────┘ └─────────┘ └─────────┘             │   │
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐             │   │
│  │  │  Ruby   │ │   HCL   │ │ Kotlin  │ │  Swift  │             │   │
│  │  └─────────┘ └─────────┘ └─────────┘ └─────────┘             │   │
│  │  ┌─────────┐ ┌─────────┐                                      │   │
│  │  │  Scala  │ │   Lua   │                                      │   │
│  │  └─────────┘ └─────────┘                                      │   │
│  └──────────────────────────────────────────────────────────────┘   │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.3 Level 3: Component Diagram - Language Extractors

```
┌─────────────────────────────────────────────────────────────────────┐
│                  Language Extractors Architecture                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │                    BaseExtractor (Abstract)                   │   │
│  │                   (extractors/base-extractor.ts)              │   │
│  ├──────────────────────────────────────────────────────────────┤   │
│  │  + config: LanguageConfig                                     │   │
│  │  + extract(tree, filePath, sourceCode): ParseResult           │   │
│  │  # createEntity(opts): Entity                                 │   │
│  │  # createRelation(opts): Relation                             │   │
│  │  # walkTree(node, visitor): void                              │   │
│  │  # getNodeText(node): string                                  │   │
│  └──────────────────────────────────────────────────────────────┘   │
│                              △                                       │
│                              │ extends                               │
│         ┌────────────────────┼────────────────────┐                 │
│         │                    │                    │                  │
│  ┌──────┴─────┐      ┌──────┴─────┐      ┌──────┴─────┐            │
│  │ TypeScript │      │   Python   │      │    Rust    │            │
│  │ Extractor  │      │ Extractor  │      │ Extractor  │            │
│  └────────────┘      └────────────┘      └────────────┘            │
│  ┌────────────┐      ┌────────────┐      ┌────────────┐            │
│  │    Go      │      │    Java    │      │    PHP     │            │
│  │ Extractor  │      │ Extractor  │      │ Extractor  │            │
│  └────────────┘      └────────────┘      └────────────┘            │
│  ┌────────────┐      ┌────────────┐      ┌────────────┐            │
│  │   C#       │      │   C/C++    │      │   Ruby     │            │
│  │ Extractor  │      │ Extractor  │      │ Extractor  │            │
│  └────────────┘      └────────────┘      └────────────┘            │
│  ┌────────────┐      ┌────────────┐      ┌────────────┐            │
│  │    HCL     │      │  Kotlin    │      │   Swift    │            │
│  │ Extractor  │      │ Extractor  │      │ Extractor  │            │
│  └────────────┘      └────────────┘      └────────────┘            │
│  ┌────────────┐      ┌────────────┐                                 │
│  │   Scala    │      │    Lua     │                                 │
│  │ Extractor  │      │ Extractor  │                                 │
│  └────────────┘      └────────────┘                                 │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 2. 詳細設計

### 2.1 DES-CG-BASE: BaseExtractor（基底クラス）

**Implements**: Common extraction interface
**Location**: `packages/codegraph/src/parser/extractors/base-extractor.ts`

```typescript
/**
 * Language configuration for extractors
 */
export interface LanguageConfig {
  name: Language;
  extensions: string[];
  treeSitterName: string;
  functionNodes: string[];
  classNodes: string[];
  importNodes: string[];
  interfaceNodes?: string[];
  moduleNodes?: string[];
}

/**
 * Abstract base class for language extractors
 */
export abstract class BaseExtractor {
  abstract readonly config: LanguageConfig;

  /**
   * Extract entities and relations from AST
   */
  abstract extract(
    tree: SyntaxTree,
    filePath: string,
    sourceCode: string
  ): ParseResult;

  /**
   * Create an entity with generated ID
   */
  protected createEntity(options: {
    type: EntityType;
    name: string;
    filePath?: string;
    startLine: number;
    endLine: number;
    language: Language;
    namespace?: string;
    docstring?: string;
    signature?: string;
  }): Entity;

  /**
   * Create a relation between entities
   */
  protected createRelation(options: {
    type: RelationType;
    sourceId: string;
    targetId: string;
    filePath?: string;
  }): Relation;

  /**
   * Walk AST tree with visitor pattern
   */
  protected walkTree(
    node: SyntaxNode,
    visitor: (node: SyntaxNode, depth: number) => void
  ): void;

  /**
   * Get text content from AST node
   */
  protected getNodeText(node: SyntaxNode): string;

  /**
   * Find child node by field name
   */
  protected getChildByField(node: SyntaxNode, field: string): SyntaxNode | null;
}
```

**Design Patterns Used**:
- **Template Method**: `extract()` defines skeleton, subclasses implement details
- **Visitor Pattern**: `walkTree()` for AST traversal
- **Factory Method**: `createEntity()`, `createRelation()`

---

### 2.2 DES-CG-RUST: Rust Language Extractor

**Implements**: REQ-CG-MULTILANG-001
**Location**: `packages/codegraph/src/parser/extractors/rust.ts`

```typescript
export class RustExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'rust',
    extensions: ['.rs'],
    treeSitterName: 'rust',
    functionNodes: ['function_item'],
    classNodes: ['struct_item', 'enum_item'],
    importNodes: ['use_declaration'],
    interfaceNodes: ['trait_item'],
    moduleNodes: ['mod_item'],
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    const entities: Entity[] = [];
    const relations: Relation[] = [];

    this.walkTree(tree.rootNode, (node) => {
      switch (node.type) {
        case 'function_item':
          entities.push(this.extractFunction(node, filePath));
          break;
        case 'struct_item':
          entities.push(this.extractStruct(node, filePath));
          break;
        case 'enum_item':
          entities.push(this.extractEnum(node, filePath));
          break;
        case 'trait_item':
          entities.push(this.extractTrait(node, filePath));
          break;
        case 'impl_item':
          this.extractImpl(node, filePath, entities, relations);
          break;
        case 'use_declaration':
          relations.push(...this.extractUse(node, filePath));
          break;
      }
    });

    return { entities, relations, errors: [], stats: {} };
  }

  private extractFunction(node: SyntaxNode, filePath: string): Entity;
  private extractStruct(node: SyntaxNode, filePath: string): Entity;
  private extractEnum(node: SyntaxNode, filePath: string): Entity;
  private extractTrait(node: SyntaxNode, filePath: string): Entity;
  private extractImpl(node: SyntaxNode, filePath: string, entities: Entity[], relations: Relation[]): void;
  private extractUse(node: SyntaxNode, filePath: string): Relation[];
}
```

**AST Node Mapping**:
| Rust Construct | tree-sitter Node | Entity Type |
|----------------|------------------|-------------|
| `fn name()` | `function_item` | function |
| `struct Name` | `struct_item` | struct |
| `enum Name` | `enum_item` | enum |
| `trait Name` | `trait_item` | trait |
| `impl Name` | `impl_item` | impl |
| `mod name` | `mod_item` | module |
| `use path::item` | `use_declaration` | import (relation) |

---

### 2.3 DES-CG-GO: Go Language Extractor

**Implements**: REQ-CG-MULTILANG-002
**Location**: `packages/codegraph/src/parser/extractors/go.ts`

```typescript
export class GoExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'go',
    extensions: ['.go'],
    treeSitterName: 'go',
    functionNodes: ['function_declaration', 'method_declaration'],
    classNodes: ['type_declaration'],
    importNodes: ['import_declaration', 'import_spec'],
    interfaceNodes: ['type_declaration'], // interface type
  };

  extract(tree: SyntaxTree, filePath: string, sourceCode: string): ParseResult {
    // Extract package name first
    // Then iterate through declarations
  }

  private extractFunction(node: SyntaxNode, filePath: string): Entity;
  private extractMethod(node: SyntaxNode, filePath: string): Entity;
  private extractStruct(node: SyntaxNode, filePath: string): Entity;
  private extractInterface(node: SyntaxNode, filePath: string): Entity;
  private extractImport(node: SyntaxNode, filePath: string): Relation[];
}
```

**AST Node Mapping**:
| Go Construct | tree-sitter Node | Entity Type |
|--------------|------------------|-------------|
| `func name()` | `function_declaration` | function |
| `func (r T) name()` | `method_declaration` | method |
| `type Name struct` | `type_declaration` (struct) | struct |
| `type Name interface` | `type_declaration` (interface) | interface |
| `import "path"` | `import_declaration` | import (relation) |

---

### 2.4 DES-CG-JAVA: Java Language Extractor

**Implements**: REQ-CG-MULTILANG-003
**Location**: `packages/codegraph/src/parser/extractors/java.ts`

```typescript
export class JavaExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'java',
    extensions: ['.java'],
    treeSitterName: 'java',
    functionNodes: ['method_declaration', 'constructor_declaration'],
    classNodes: ['class_declaration', 'enum_declaration'],
    importNodes: ['import_declaration'],
    interfaceNodes: ['interface_declaration'],
  };
}
```

**AST Node Mapping**:
| Java Construct | tree-sitter Node | Entity Type |
|----------------|------------------|-------------|
| `class Name` | `class_declaration` | class |
| `interface Name` | `interface_declaration` | interface |
| `enum Name` | `enum_declaration` | enum |
| `void method()` | `method_declaration` | method |
| `Name()` | `constructor_declaration` | method |
| `import x.y.Z` | `import_declaration` | import (relation) |

---

### 2.5 DES-CG-PHP: PHP Language Extractor

**Implements**: REQ-CG-MULTILANG-004
**Location**: `packages/codegraph/src/parser/extractors/php.ts`

```typescript
export class PHPExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'php',
    extensions: ['.php'],
    treeSitterName: 'php',
    functionNodes: ['function_definition', 'method_declaration'],
    classNodes: ['class_declaration', 'trait_declaration'],
    importNodes: ['namespace_use_declaration'],
    interfaceNodes: ['interface_declaration'],
  };
}
```

---

### 2.6 DES-CG-CSHARP: C# Language Extractor

**Implements**: REQ-CG-MULTILANG-005
**Location**: `packages/codegraph/src/parser/extractors/csharp.ts`

```typescript
export class CSharpExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'csharp',
    extensions: ['.cs'],
    treeSitterName: 'c_sharp',
    functionNodes: ['method_declaration', 'constructor_declaration'],
    classNodes: ['class_declaration', 'struct_declaration', 'enum_declaration'],
    importNodes: ['using_directive'],
    interfaceNodes: ['interface_declaration'],
  };
}
```

---

### 2.7 DES-CG-C: C Language Extractor

**Implements**: REQ-CG-MULTILANG-006
**Location**: `packages/codegraph/src/parser/extractors/c.ts`

```typescript
export class CExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'c',
    extensions: ['.c', '.h'],
    treeSitterName: 'c', // Uses tree-sitter-c or tree-sitter-cpp
    functionNodes: ['function_definition', 'declaration'],
    classNodes: ['struct_specifier', 'enum_specifier'],
    importNodes: ['preproc_include'],
  };
}
```

---

### 2.8 DES-CG-CPP: C++ Language Extractor

**Implements**: REQ-CG-MULTILANG-007
**Location**: `packages/codegraph/src/parser/extractors/cpp.ts`

```typescript
export class CppExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'cpp',
    extensions: ['.cpp', '.hpp', '.cc', '.cxx', '.hxx'],
    treeSitterName: 'cpp',
    functionNodes: ['function_definition'],
    classNodes: ['class_specifier', 'struct_specifier'],
    importNodes: ['preproc_include'],
    moduleNodes: ['namespace_definition'],
  };
}
```

---

### 2.9 DES-CG-RUBY: Ruby Language Extractor

**Implements**: REQ-CG-MULTILANG-008
**Location**: `packages/codegraph/src/parser/extractors/ruby.ts`

```typescript
export class RubyExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'ruby',
    extensions: ['.rb', '.rake', '.gemspec'],
    treeSitterName: 'ruby',
    functionNodes: ['method', 'singleton_method'],
    classNodes: ['class', 'module'],
    importNodes: ['call'], // require, require_relative
  };
}
```

---

### 2.10 DES-CG-HCL: HCL/Terraform Language Extractor

**Implements**: REQ-CG-MULTILANG-009
**Location**: `packages/codegraph/src/parser/extractors/hcl.ts`

```typescript
export class HCLExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'hcl',
    extensions: ['.tf', '.hcl', '.tfvars'],
    treeSitterName: 'hcl',
    functionNodes: [],
    classNodes: ['block'], // resource, data, variable, output
    importNodes: [],
  };
}
```

---

### 2.11 DES-CG-KOTLIN: Kotlin Language Extractor

**Implements**: REQ-CG-MULTILANG-010
**Location**: `packages/codegraph/src/parser/extractors/kotlin.ts`

```typescript
export class KotlinExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'kotlin',
    extensions: ['.kt', '.kts'],
    treeSitterName: 'kotlin',
    functionNodes: ['function_declaration'],
    classNodes: ['class_declaration', 'object_declaration'],
    importNodes: ['import_header'],
    interfaceNodes: ['class_declaration'], // interface keyword
  };
}
```

---

### 2.12 DES-CG-SWIFT: Swift Language Extractor

**Implements**: REQ-CG-MULTILANG-011
**Location**: `packages/codegraph/src/parser/extractors/swift.ts`

```typescript
export class SwiftExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'swift',
    extensions: ['.swift'],
    treeSitterName: 'swift',
    functionNodes: ['function_declaration'],
    classNodes: ['class_declaration', 'struct_declaration'],
    importNodes: ['import_declaration'],
    interfaceNodes: ['protocol_declaration'],
  };
}
```

---

### 2.13 DES-CG-SCALA: Scala Language Extractor

**Implements**: REQ-CG-MULTILANG-012
**Location**: `packages/codegraph/src/parser/extractors/scala.ts`

```typescript
export class ScalaExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'scala',
    extensions: ['.scala', '.sc'],
    treeSitterName: 'scala',
    functionNodes: ['function_definition'],
    classNodes: ['class_definition', 'object_definition'],
    importNodes: ['import_declaration'],
    interfaceNodes: ['trait_definition'],
  };
}
```

---

### 2.14 DES-CG-LUA: Lua Language Extractor

**Implements**: REQ-CG-MULTILANG-013
**Location**: `packages/codegraph/src/parser/extractors/lua.ts`

```typescript
export class LuaExtractor extends BaseExtractor {
  readonly config: LanguageConfig = {
    name: 'lua',
    extensions: ['.lua'],
    treeSitterName: 'lua',
    functionNodes: ['function_declaration', 'local_function'],
    classNodes: [],
    importNodes: ['function_call'], // require()
  };
}
```

---

## 3. ExtractorRegistry設計

### 3.1 DES-CG-REGISTRY: Extractor Registry

**Location**: `packages/codegraph/src/parser/extractors/index.ts`

```typescript
/**
 * Registry of language extractors
 */
const extractorRegistry = new Map<Language, BaseExtractor>();

/**
 * Register an extractor for a language
 */
export function registerExtractor(extractor: BaseExtractor): void {
  extractorRegistry.set(extractor.config.name, extractor);
}

/**
 * Get extractor for a language
 */
export function getExtractor(language: Language): BaseExtractor | undefined {
  return extractorRegistry.get(language);
}

/**
 * Get all registered languages
 */
export function getRegisteredLanguages(): Language[] {
  return Array.from(extractorRegistry.keys());
}

// Auto-register all extractors on import
import { TypeScriptExtractor } from './typescript.js';
import { PythonExtractor } from './python.js';
import { RustExtractor } from './rust.js';
import { GoExtractor } from './go.js';
import { JavaExtractor } from './java.js';
import { PHPExtractor } from './php.js';
import { CSharpExtractor } from './csharp.js';
import { CExtractor } from './c.js';
import { CppExtractor } from './cpp.js';
import { RubyExtractor } from './ruby.js';
import { HCLExtractor } from './hcl.js';
import { KotlinExtractor } from './kotlin.js';
import { SwiftExtractor } from './swift.js';
import { ScalaExtractor } from './scala.js';
import { LuaExtractor } from './lua.js';

// Register all extractors
[
  new TypeScriptExtractor(),
  new PythonExtractor(),
  new RustExtractor(),
  new GoExtractor(),
  new JavaExtractor(),
  new PHPExtractor(),
  new CSharpExtractor(),
  new CExtractor(),
  new CppExtractor(),
  new RubyExtractor(),
  new HCLExtractor(),
  new KotlinExtractor(),
  new SwiftExtractor(),
  new ScalaExtractor(),
  new LuaExtractor(),
].forEach(registerExtractor);
```

---

## 4. AST Parser更新設計

### 4.1 DES-CG-PARSER: AST Parser Integration

**Location**: `packages/codegraph/src/parser/ast-parser.ts`

```typescript
// Updated initialization
private async ensureInitialized(): Promise<void> {
  if (this.initialized) return;

  try {
    const Parser = (await import('tree-sitter')).default;
    this.parser = new Parser();

    // Load all available grammars
    await this.loadGrammar('typescript', () => import('tree-sitter-typescript'));
    await this.loadGrammar('python', () => import('tree-sitter-python'));
    await this.loadGrammar('rust', () => import('tree-sitter-rust'));
    await this.loadGrammar('go', () => import('tree-sitter-go'));
    await this.loadGrammar('java', () => import('tree-sitter-java'));
    await this.loadGrammar('php', () => import('tree-sitter-php'));
    await this.loadGrammar('csharp', () => import('tree-sitter-c-sharp'));
    await this.loadGrammar('cpp', () => import('tree-sitter-cpp'));
    await this.loadGrammar('ruby', () => import('tree-sitter-ruby'));
    await this.loadGrammar('hcl', () => import('tree-sitter-hcl'));
    await this.loadGrammar('kotlin', () => import('tree-sitter-kotlin'));
    await this.loadGrammar('swift', () => import('tree-sitter-swift'));
    await this.loadGrammar('scala', () => import('tree-sitter-scala'));
    await this.loadGrammar('lua', () => import('tree-sitter-lua'));

    this.initialized = true;
  } catch {
    this.initialized = true; // Fallback mode
  }
}

/**
 * Load grammar with graceful fallback
 */
private async loadGrammar(
  language: Language,
  loader: () => Promise<unknown>
): Promise<void> {
  try {
    const mod = await loader();
    // Handle different module export patterns
    const grammar = (mod as any).default || (mod as any);
    this.languages.set(language, grammar);
  } catch {
    // Grammar not available - will use fallback
    console.warn(`Grammar for ${language} not available`);
  }
}

/**
 * Parse using tree-sitter with extractor
 */
private parseWithTreeSitter(
  content: string,
  language: Language,
  filePath: string | undefined,
  lineCount: number
): ParseResult {
  const extractor = getExtractor(language);
  if (!extractor) {
    throw new Error(`No extractor for ${language}`);
  }

  const grammar = this.languages.get(language);
  if (!grammar || !this.parser) {
    throw new Error('Grammar not loaded');
  }

  this.parser.setLanguage(grammar);
  const tree = this.parser.parse(content);

  return extractor.extract(tree, filePath || 'unknown', content);
}
```

---

## 5. トレーサビリティマトリクス

| 要件ID | 設計ID | ファイル | 状態 |
|--------|--------|----------|------|
| REQ-CG-MULTILANG-001 | DES-CG-RUST | extractors/rust.ts | 設計完了 |
| REQ-CG-MULTILANG-002 | DES-CG-GO | extractors/go.ts | 設計完了 |
| REQ-CG-MULTILANG-003 | DES-CG-JAVA | extractors/java.ts | 設計完了 |
| REQ-CG-MULTILANG-004 | DES-CG-PHP | extractors/php.ts | 設計完了 |
| REQ-CG-MULTILANG-005 | DES-CG-CSHARP | extractors/csharp.ts | 設計完了 |
| REQ-CG-MULTILANG-006 | DES-CG-C | extractors/c.ts | 設計完了 |
| REQ-CG-MULTILANG-007 | DES-CG-CPP | extractors/cpp.ts | 設計完了 |
| REQ-CG-MULTILANG-008 | DES-CG-RUBY | extractors/ruby.ts | 設計完了 |
| REQ-CG-MULTILANG-009 | DES-CG-HCL | extractors/hcl.ts | 設計完了 |
| REQ-CG-MULTILANG-010 | DES-CG-KOTLIN | extractors/kotlin.ts | 設計完了 |
| REQ-CG-MULTILANG-011 | DES-CG-SWIFT | extractors/swift.ts | 設計完了 |
| REQ-CG-MULTILANG-012 | DES-CG-SCALA | extractors/scala.ts | 設計完了 |
| REQ-CG-MULTILANG-013 | DES-CG-LUA | extractors/lua.ts | 設計完了 |
| REQ-CG-MULTILANG-NFR-001 | DES-CG-PARSER | ast-parser.ts | 設計完了 |
| REQ-CG-MULTILANG-NFR-002 | DES-CG-PARSER | ast-parser.ts | 設計完了 |
| REQ-CG-MULTILANG-NFR-003 | DES-CG-REGISTRY | extractors/index.ts | 設計完了 |

---

## 6. 設計パターン適用

| パターン | 適用箇所 | 理由 |
|----------|----------|------|
| **Template Method** | BaseExtractor.extract() | 抽出ロジックの骨格を定義、言語固有部分を派生クラスで実装 |
| **Factory Method** | createEntity(), createRelation() | エンティティ/リレーション生成を標準化 |
| **Strategy** | ExtractorRegistry | 言語に応じたエクストラクターを切り替え |
| **Visitor** | walkTree() | AST走査を統一的に処理 |
| **Registry** | extractorRegistry | 利用可能なエクストラクターを集中管理 |
| **Lazy Loading** | loadGrammar() | 必要な言語のみ初期化、メモリ節約 |

---

## 7. 変更履歴

| バージョン | 日付 | 変更内容 |
|-----------|------|----------|
| 1.0.0 | 2026-01-09 | 初版作成 |
