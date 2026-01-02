# MUSUBIX - ニューロシンボリックAI統合システム 設計書

**文書ID**: DES-MUSUBIX-001  
**プロジェクト**: MUSUBIX  
**バージョン**: 1.1  
**作成日**: 2026-01-01  
**ステータス**: Approved  
**承認日**: 2026-01-01  
**要件定義書**: REQ-MUSUBIX-001 v1.1

---

## 1. 設計概要

### 1.1 目的

本文書は、MUSUBIX（MUSUBI × YATA統合システム）のアーキテクチャ設計、コンポーネント設計、インターフェース設計を定義する。

### 1.2 設計原則

本設計は以下の憲法条項に準拠する：

| Article | 原則 | 設計への適用 |
|---------|------|-------------|
| I | Library-First | 全機能をライブラリとして分離 |
| II | CLI Interface | 全ライブラリにCLIエントリーポイント |
| III | Test-First | テスト駆動で実装 |
| V | Traceability | 全コンポーネントに要件ID紐付け |
| VII | Simplicity Gate | 初期は3プロジェクト以内 |
| VIII | Anti-Abstraction | フレームワークAPI直接使用 |
| IX | Integration Testing | 実サービスでテスト |

### 1.3 要件カバレッジマトリクス（全41要件）

| 要件ID | 設計コンポーネント | 本文書セクション | 優先度 |
|--------|------------------|-----------------|--------|
| REQ-ARC-001 | LibraryStructure | 3.1 | P0 |
| REQ-ARC-002 | CLIInterface | 3.2 | P0 |
| REQ-INT-001 | NeuroSymbolicIntegrator | 4.1 | P0 |
| REQ-INT-002 | ConfidenceEvaluator | 4.2 | P0 |
| REQ-INT-003 | ContradictionDetector | 4.3 | P0 |
| REQ-RA-001 | EARSValidator | 5.1 | P0 |
| REQ-RA-002 | OntologyMapper | 5.2 | P0 |
| REQ-RA-003 | RelatedRequirementsFinder | 5.3 | P1 |
| REQ-RA-004 | RequirementsDecomposer | 5.4 | P2 |
| REQ-DES-001 | PatternDetector | 6.1 | P0 |
| REQ-DES-002 | FrameworkOptimizer | 6.3 | P0 |
| REQ-DES-003 | SOLIDValidator | 6.2 | P0 |
| REQ-DES-004 | C4ModelGenerator | 6.4 | P1 |
| REQ-DES-005 | ADRGenerator | 6.5 | P1 |
| REQ-COD-001 | CodeGenerator | 7.1 | P0 |
| REQ-COD-002 | StaticAnalyzer | 7.3 | P0 |
| REQ-COD-003 | PatternConformanceChecker | 7.4 | P0 |
| REQ-COD-004 | DependencyAnalyzer | 7.5 | P0 |
| REQ-COD-005 | CodingStandardsChecker | 7.6 | P1 |
| REQ-COD-006 | SecurityScanner | 7.2 | P0 |
| REQ-TST-001 | UnitTestGenerator | 8.1 | P0 |
| REQ-TST-002 | IntegrationTestGenerator | 8.2 | P0 |
| REQ-EXP-001 | ReasoningChainRecorder | 12.1 | P0 |
| REQ-EXP-002 | ExplanationGenerator | 12.2 | P0 |
| REQ-EXP-003 | VisualExplanationGenerator | 12.3 | P2 |
| REQ-TRA-001 | TraceabilityManager | 9.1 | P0 |
| REQ-TRA-002 | ImpactAnalyzer | 9.1 | P0 |
| REQ-ERR-001 | GracefulDegradation | 10.1 | P0 |
| REQ-ERR-002 | DataPersistence | 10.2 | P0 |
| REQ-ERR-003 | VersionCompatibility | 10.3 | P1 |
| REQ-PER-001 | PerformanceProfile | 13.1 | P1 |
| REQ-PER-002 | ScalabilityDesign | 13.2 | P1 |
| REQ-QUA-001 | QualityMetricsCalculator | 7.3 | P0 |
| REQ-QUA-002 | CoverageReporter | 8.3 | P0 |
| REQ-SEC-001 | DataProtector | 14.1 | P0 |
| REQ-SEC-002 | AuthManager | 14.2 | P1 |
| REQ-INT-101 | PlatformAdapter | 15.1 | P0 |
| REQ-INT-102 | MCPServer | 11.1 | P0 |
| REQ-MNT-001 | Logger | 16.1 | P1 |
| REQ-MNT-002 | ErrorHandler | 16.2 | P0 |
| REQ-I18N-001 | I18nManager | 17.1 | P2 |

---

## 2. C4モデル

### 2.1 Level 1: System Context

```plantuml
@startuml C4_Context
!include https://raw.githubusercontent.com/plantuml-stdlib/C4-PlantUML/master/C4_Context.puml

title MUSUBIX - System Context Diagram

Person(developer, "Developer", "AI Coding Agent/Human Developer")
Person(reviewer, "Code Reviewer", "Reviews generated code")

System(musubix, "MUSUBIX", "Neuro-Symbolic AI Coding System\nMUSUBI + YATA Integration")

System_Ext(llm_api, "LLM API", "Claude/GPT/Gemini API")
System_Ext(git, "Git Repository", "Source code repository")
System_Ext(ai_platform, "AI Coding Platform", "Claude Code/Copilot/Cursor etc.")

Rel(developer, musubix, "Uses", "CLI/MCP")
Rel(reviewer, musubix, "Reviews via", "Explanation API")
Rel(musubix, llm_api, "Neural inference", "HTTPS")
Rel(musubix, git, "Reads/Writes", "Git protocol")
Rel(ai_platform, musubix, "Invokes tools", "MCP/stdio/SSE")

@enduml
```

**トレーサビリティ**: REQ-INT-101, REQ-INT-102

---

### 2.2 Level 2: Container

```plantuml
@startuml C4_Container
!include https://raw.githubusercontent.com/plantuml-stdlib/C4-PlantUML/master/C4_Container.puml

title MUSUBIX - Container Diagram

Person(developer, "Developer")

System_Boundary(musubix, "MUSUBIX System") {
    Container(cli, "MUSUBIX CLI", "Node.js", "Command-line interface\nfor all operations")
    Container(mcp_server, "MCP Server", "Node.js", "Model Context Protocol\nserver for AI platforms")
    Container(core, "Core Library", "Node.js", "Neuro-Symbolic\nintegration engine")
    Container(yata_client, "YATA Client", "Node.js", "Knowledge graph\nclient library")
    ContainerDb(storage, "Local Storage", "JSON/SQLite", "Project data,\ncache, logs")
}

System_Ext(yata_mcp, "YATA MCP Server", "Knowledge Graph\nSymbolic reasoning")
System_Ext(llm_api, "LLM API", "Neural inference")

Rel(developer, cli, "Executes", "Shell")
Rel(developer, mcp_server, "Invokes via", "AI Platform")
Rel(cli, core, "Uses")
Rel(mcp_server, core, "Uses")
Rel(core, yata_client, "Queries")
Rel(core, llm_api, "Infers", "HTTPS")
Rel(yata_client, yata_mcp, "Queries", "MCP/stdio")
Rel(core, storage, "Reads/Writes")

@enduml
```

**トレーサビリティ**: REQ-ARC-001, REQ-ARC-002, REQ-INT-001

---

### 2.3 Level 3: Component

```plantuml
@startuml C4_Component
!include https://raw.githubusercontent.com/plantuml-stdlib/C4-PlantUML/master/C4_Component.puml

title MUSUBIX Core Library - Component Diagram

Container_Boundary(core, "Core Library") {
    Component(integrator, "NeuroSymbolicIntegrator", "Class", "Combines neural and\nsymbolic inference results")
    Component(confidence, "ConfidenceEvaluator", "Class", "Evaluates confidence\nscores and decides output")
    Component(contradiction, "ContradictionDetector", "Class", "Detects and classifies\ncontradictions")
    
    Component(ears_validator, "EARSValidator", "Class", "Validates EARS\nrequirements syntax")
    Component(ontology_mapper, "OntologyMapper", "Class", "Maps requirements\nto ontology")
    
    Component(pattern_detector, "PatternDetector", "Class", "Detects applicable\ndesign patterns")
    Component(code_generator, "CodeGenerator", "Class", "Generates code\nfrom design")
    Component(static_analyzer, "StaticAnalyzer", "Class", "Analyzes code\nquality metrics")
    
    Component(test_generator, "TestGenerator", "Class", "Generates unit and\nintegration tests")
    Component(traceability, "TraceabilityManager", "Class", "Manages requirement-\ndesign-code links")
    Component(explanation, "ExplanationGenerator", "Class", "Generates natural\nlanguage explanations")
}

Rel(integrator, confidence, "Uses")
Rel(integrator, contradiction, "Uses")
Rel(ears_validator, ontology_mapper, "Validates then maps")
Rel(pattern_detector, code_generator, "Recommends to")
Rel(code_generator, static_analyzer, "Analyzed by")
Rel(code_generator, test_generator, "Generates tests via")
Rel(traceability, integrator, "Tracks all")
Rel(explanation, integrator, "Explains")

@enduml
```

**トレーサビリティ**: REQ-INT-001〜003, REQ-RA-001〜002, REQ-DES-001, REQ-COD-001〜002, REQ-TST-001, REQ-TRA-001

---

## 3. アーキテクチャ設計

### 3.1 プロジェクト構成（Article VII準拠：3プロジェクト以内）

```
musubix/
├── packages/
│   ├── core/                    # Project 1: Core Library
│   │   ├── src/
│   │   │   ├── integrator/      # Neuro-Symbolic Integration
│   │   │   ├── requirements/    # Requirements Analysis
│   │   │   ├── design/          # Design Generation
│   │   │   ├── codegen/         # Code Generation
│   │   │   ├── testing/         # Test Generation
│   │   │   ├── traceability/    # Traceability Management
│   │   │   └── explanation/     # Explanation Generation
│   │   ├── bin/                 # CLI entry points
│   │   ├── tests/
│   │   └── package.json
│   │
│   ├── mcp-server/              # Project 2: MCP Server
│   │   ├── src/
│   │   │   ├── tools/           # MCP Tools
│   │   │   ├── prompts/         # MCP Prompts
│   │   │   ├── resources/       # MCP Resources
│   │   │   └── transport/       # stdio/SSE handlers
│   │   ├── bin/
│   │   ├── tests/
│   │   └── package.json
│   │
│   └── yata-client/             # Project 3: YATA Client
│       ├── src/
│       │   ├── knowledge/       # Knowledge Graph queries
│       │   ├── reasoning/       # Symbolic reasoning
│       │   └── mcp/             # MCP client
│       ├── bin/
│       ├── tests/
│       └── package.json
│
├── steering/                    # Project Memory (Article VI)
├── storage/                     # Local data storage
└── package.json                 # Monorepo root
```

**トレーサビリティ**: REQ-ARC-001  
**憲法準拠**: Article I（Library-First）, Article VII（Simplicity Gate - 3プロジェクト）

---

### 3.2 CLIインターフェース設計

#### 3.2.1 コマンド体系

```bash
# Core Library CLI
musubix <command> [options]

# Main Commands
musubix requirements <subcommand>   # Requirements analysis
musubix design <subcommand>         # Design generation
musubix codegen <subcommand>        # Code generation
musubix test <subcommand>           # Test generation
musubix trace <subcommand>          # Traceability management
musubix explain <subcommand>        # Explanation generation

# Global Options
--help, -h          # Show help
--version, -v       # Show version
--verbose           # Verbose output
--json              # JSON output format
--config <path>     # Config file path
```

#### 3.2.2 サブコマンド詳細

```bash
# Requirements Commands
musubix requirements analyze <input>     # Analyze natural language → EARS
musubix requirements validate <file>     # Validate EARS syntax
musubix requirements map <file>          # Map to ontology
musubix requirements search <query>      # Search related requirements

# Design Commands
musubix design generate <req-file>       # Generate design from requirements
musubix design patterns <context>        # Detect applicable patterns
musubix design validate <file>           # Validate SOLID compliance
musubix design c4 <file>                 # Generate C4 diagrams
musubix design adr <decision>            # Generate ADR

# Code Generation Commands
musubix codegen generate <design-file>   # Generate code from design
musubix codegen analyze <code-file>      # Static analysis
musubix codegen security <code-file>     # Security scan

# Test Commands
musubix test generate <code-file>        # Generate tests
musubix test coverage <test-dir>         # Measure coverage

# Traceability Commands
musubix trace matrix                     # Generate traceability matrix
musubix trace impact <req-id>            # Impact analysis
musubix trace validate                   # Validate links

# Explanation Commands
musubix explain why <artifact-id>        # Explain reasoning
musubix explain graph <artifact-id>      # Generate reasoning graph
```

#### 3.2.3 終了コード規約

| コード | 意味 |
|--------|------|
| 0 | 成功 |
| 1 | 一般エラー |
| 2 | 引数エラー |
| 3 | ファイル未発見 |
| 4 | 検証エラー |
| 5 | 外部サービスエラー |

**トレーサビリティ**: REQ-ARC-002  
**憲法準拠**: Article II（CLI Interface Mandate）

---

## 4. 統合レイヤー設計

### 4.1 NeuroSymbolicIntegrator

```typescript
// DES-INT-001: NeuroSymbolicIntegrator
// Traces to: REQ-INT-001

interface IntegrationResult {
  neuralResult: NeuralInferenceResult;
  symbolicResult: SymbolicReasoningResult;
  finalResult: MergedResult;
  confidence: number;
  reasoning: ReasoningChain;
}

interface NeuralInferenceResult {
  output: string;
  confidence: number;
  model: string;
  tokens: number;
}

interface SymbolicReasoningResult {
  output: string;
  valid: boolean;
  violations: Violation[];
  patterns: DetectedPattern[];
}

class NeuroSymbolicIntegrator {
  private confidenceEvaluator: ConfidenceEvaluator;
  private contradictionDetector: ContradictionDetector;
  private yataClient: YataClient;
  private llmClient: LLMClient;

  /**
   * Integrate neural and symbolic inference
   * @param query User query or requirement
   * @param context Additional context
   * @returns Integration result with confidence and reasoning
   */
  async integrate(
    query: string,
    context: IntegrationContext
  ): Promise<IntegrationResult> {
    // 1. Parallel inference
    const [neuralResult, symbolicResult] = await Promise.all([
      this.llmClient.infer(query, context),
      this.yataClient.reason(query, context)
    ]);

    // 2. Detect contradictions
    const contradictions = this.contradictionDetector.detect(
      neuralResult,
      symbolicResult
    );

    // 3. Evaluate confidence and decide
    const decision = this.confidenceEvaluator.evaluate(
      neuralResult,
      symbolicResult,
      contradictions
    );

    // 4. Build reasoning chain
    const reasoning = this.buildReasoningChain(
      neuralResult,
      symbolicResult,
      decision
    );

    return {
      neuralResult,
      symbolicResult,
      finalResult: decision.result,
      confidence: decision.confidence,
      reasoning
    };
  }
}
```

**トレーサビリティ**: REQ-INT-001

---

### 4.2 ConfidenceEvaluator

```typescript
// DES-INT-002: ConfidenceEvaluator
// Traces to: REQ-INT-002

interface ConfidenceDecision {
  result: MergedResult;
  confidence: number;
  source: 'neural' | 'symbolic' | 'merged';
  rationale: string;
}

class ConfidenceEvaluator {
  private readonly NEURAL_THRESHOLD = 0.8;

  /**
   * Evaluate confidence and decide final result
   * Decision rules (from REQ-INT-002):
   * - symbolic=invalid → reject neural
   * - symbolic=valid && neural≥0.8 → adopt neural
   * - symbolic=valid && neural<0.8 → prefer symbolic
   */
  evaluate(
    neural: NeuralInferenceResult,
    symbolic: SymbolicReasoningResult,
    contradictions: Contradiction[]
  ): ConfidenceDecision {
    // Rule 1: Symbolic invalid → reject neural
    if (!symbolic.valid) {
      return {
        result: this.buildSymbolicResult(symbolic),
        confidence: this.calculateSymbolicConfidence(symbolic),
        source: 'symbolic',
        rationale: `Neural result rejected: symbolic validation failed with ${symbolic.violations.length} violations`
      };
    }

    // Rule 2: Valid + high neural confidence → adopt neural
    if (neural.confidence >= this.NEURAL_THRESHOLD) {
      return {
        result: this.buildNeuralResult(neural),
        confidence: neural.confidence,
        source: 'neural',
        rationale: `Neural result adopted: confidence ${neural.confidence} >= ${this.NEURAL_THRESHOLD}`
      };
    }

    // Rule 3: Valid + low neural confidence → prefer symbolic
    return {
      result: this.buildSymbolicResult(symbolic),
      confidence: this.calculateMergedConfidence(neural, symbolic),
      source: 'symbolic',
      rationale: `Symbolic result preferred: neural confidence ${neural.confidence} < ${this.NEURAL_THRESHOLD}`
    };
  }
}
```

**トレーサビリティ**: REQ-INT-002

---

### 4.3 ContradictionDetector

```typescript
// DES-INT-003: ContradictionDetector
// Traces to: REQ-INT-003

enum ContradictionType {
  LOGICAL = 'logical',           // 論理的矛盾
  CONSTRAINT = 'constraint',     // 制約違反
  PATTERN = 'pattern',           // パターン不一致
  TYPE = 'type'                  // 型不整合
}

interface Contradiction {
  type: ContradictionType;
  location: string;
  neuralClaim: string;
  symbolicClaim: string;
  severity: 'error' | 'warning';
  resolution: ResolutionProposal;
}

interface ResolutionProposal {
  action: 'adopt_neural' | 'adopt_symbolic' | 'manual_review';
  suggestion: string;
  confidence: number;
}

class ContradictionDetector {
  private readonly KNOWN_PATTERNS = 10; // 既知の矛盾パターン10種類

  /**
   * Detect contradictions between neural and symbolic results
   * Must detect 100% of known contradiction patterns (REQ-INT-003)
   */
  detect(
    neural: NeuralInferenceResult,
    symbolic: SymbolicReasoningResult
  ): Contradiction[] {
    const contradictions: Contradiction[] = [];

    // 1. Logical contradictions
    contradictions.push(...this.detectLogicalContradictions(neural, symbolic));

    // 2. Constraint violations
    contradictions.push(...this.detectConstraintViolations(neural, symbolic));

    // 3. Pattern mismatches
    contradictions.push(...this.detectPatternMismatches(neural, symbolic));

    // 4. Type inconsistencies
    contradictions.push(...this.detectTypeInconsistencies(neural, symbolic));

    // Generate resolution proposals
    return contradictions.map(c => ({
      ...c,
      resolution: this.proposeResolution(c)
    }));
  }

  /**
   * Propose resolution with 80%+ validity rate (REQ-INT-003)
   */
  private proposeResolution(contradiction: Contradiction): ResolutionProposal {
    // Resolution logic based on contradiction type and severity
    switch (contradiction.type) {
      case ContradictionType.LOGICAL:
        return {
          action: 'adopt_symbolic',
          suggestion: 'Symbolic reasoning provides logically consistent result',
          confidence: 0.9
        };
      case ContradictionType.CONSTRAINT:
        return {
          action: 'adopt_symbolic',
          suggestion: 'Constraint violation must be resolved using symbolic rules',
          confidence: 0.95
        };
      case ContradictionType.PATTERN:
        return {
          action: 'manual_review',
          suggestion: 'Pattern mismatch requires human review',
          confidence: 0.7
        };
      case ContradictionType.TYPE:
        return {
          action: 'adopt_symbolic',
          suggestion: 'Type system provides definitive answer',
          confidence: 0.98
        };
    }
  }
}
```

**トレーサビリティ**: REQ-INT-003

---

## 5. 要求分析設計

### 5.1 EARSValidator

```typescript
// DES-RA-001: EARSValidator
// Traces to: REQ-RA-001

enum EARSPattern {
  UBIQUITOUS = 'ubiquitous',     // THE system SHALL...
  EVENT_DRIVEN = 'event-driven', // WHEN <event>, THE system SHALL...
  STATE_DRIVEN = 'state-driven', // WHILE <state>, THE system SHALL...
  UNWANTED = 'unwanted',         // THE system SHALL NOT...
  OPTIONAL = 'optional'          // IF <condition>, THEN THE system SHALL...
}

interface EARSValidationResult {
  valid: boolean;
  pattern: EARSPattern | null;
  errors: SyntaxError[];
  suggestions: string[];
  correctedText?: string;
}

interface EARSRequirement {
  id: string;
  pattern: EARSPattern;
  trigger?: string;      // WHEN/WHILE/IF clause
  subject: string;       // THE system
  action: string;        // SHALL/SHALL NOT
  response: string;      // What the system does
  conditions?: string[]; // AND clauses
}

class EARSValidator {
  private readonly PATTERNS: RegExp[] = [
    // UBIQUITOUS: THE <system> SHALL <response>
    /^THE\s+(\w+)\s+SHALL\s+(.+)$/i,
    // EVENT-DRIVEN: WHEN <event>, THE <system> SHALL <response>
    /^WHEN\s+(.+),\s*THE\s+(\w+)\s+SHALL\s+(.+)$/i,
    // STATE-DRIVEN: WHILE <state>, THE <system> SHALL <response>
    /^WHILE\s+(.+),\s*THE\s+(\w+)\s+SHALL\s+(.+)$/i,
    // UNWANTED: THE <system> SHALL NOT <response>
    /^THE\s+(\w+)\s+SHALL\s+NOT\s+(.+)$/i,
    // OPTIONAL: IF <condition>, THEN THE <system> SHALL <response>
    /^IF\s+(.+),\s*THEN\s+THE\s+(\w+)\s+SHALL\s+(.+)$/i
  ];

  /**
   * Validate EARS syntax with 95%+ accuracy (REQ-RA-001)
   */
  validate(text: string): EARSValidationResult {
    const normalized = this.normalize(text);
    
    for (const [index, pattern] of this.PATTERNS.entries()) {
      const match = normalized.match(pattern);
      if (match) {
        return {
          valid: true,
          pattern: this.indexToPattern(index),
          errors: [],
          suggestions: []
        };
      }
    }

    // Generate correction suggestions
    const suggestions = this.generateSuggestions(normalized);
    return {
      valid: false,
      pattern: null,
      errors: [{ message: 'Does not match any EARS pattern', position: 0 }],
      suggestions,
      correctedText: suggestions[0]
    };
  }

  /**
   * Convert natural language to EARS format using LLM
   */
  async convertToEARS(
    naturalLanguage: string,
    llmClient: LLMClient
  ): Promise<EARSRequirement> {
    const prompt = this.buildConversionPrompt(naturalLanguage);
    const result = await llmClient.infer(prompt, {
      systemPrompt: EARS_CONVERSION_SYSTEM_PROMPT
    });
    
    const parsed = this.parseEARSFromLLM(result.output);
    const validation = this.validate(parsed.text);
    
    if (!validation.valid) {
      // Retry with suggestions
      return this.retryConversion(naturalLanguage, validation.suggestions, llmClient);
    }
    
    return parsed;
  }
}
```

**トレーサビリティ**: REQ-RA-001

---

### 5.2 OntologyMapper

```typescript
// DES-RA-002: OntologyMapper
// Traces to: REQ-RA-002

interface OntologyMapping {
  requirementId: string;
  concepts: OntologyConcept[];
  relations: OntologyRelation[];
  validationResult: OntologyValidationResult;
}

interface OntologyValidationResult {
  consistent: boolean;
  conflicts: ConflictingRequirement[];
  coverage: number;
  report: ValidationReport;
}

class OntologyMapper {
  private yataClient: YataClient;

  /**
   * Map requirement to ontology with 95%+ success rate (REQ-RA-002)
   */
  async map(requirement: EARSRequirement): Promise<OntologyMapping> {
    // 1. Extract concepts from requirement
    const concepts = await this.extractConcepts(requirement);

    // 2. Query YATA for ontology mapping
    const ontologyMapping = await this.yataClient.mapToOntology(concepts);

    // 3. Validate consistency
    const validation = await this.validateConsistency(
      requirement,
      ontologyMapping
    );

    // 4. Generate report
    const report = this.generateReport(requirement, ontologyMapping, validation);

    return {
      requirementId: requirement.id,
      concepts: ontologyMapping.concepts,
      relations: ontologyMapping.relations,
      validationResult: {
        consistent: validation.conflicts.length === 0,
        conflicts: validation.conflicts,
        coverage: validation.coverage,
        report
      }
    };
  }

  /**
   * Detect conflicts with existing requirements (95%+ accuracy)
   */
  private async validateConsistency(
    requirement: EARSRequirement,
    mapping: OntologyMapping
  ): Promise<{ conflicts: ConflictingRequirement[]; coverage: number }> {
    // Query existing requirements from knowledge graph
    const existingRequirements = await this.yataClient.queryRelatedRequirements(
      mapping.concepts
    );

    const conflicts: ConflictingRequirement[] = [];
    
    for (const existing of existingRequirements) {
      const conflict = await this.detectConflict(requirement, existing);
      if (conflict) {
        conflicts.push(conflict);
      }
    }

    const coverage = this.calculateCoverage(mapping);
    return { conflicts, coverage };
  }
}
```

**トレーサビリティ**: REQ-RA-002

---

### 5.3 RelatedRequirementsFinder

```typescript
// DES-RA-003: RelatedRequirementsFinder
// Traces to: REQ-RA-003

interface RelatedRequirement {
  id: string;
  text: string;
  relevanceScore: number;  // 0.0-1.0
  relationship: 'depends_on' | 'conflicts_with' | 'extends' | 'similar_to';
}

interface SearchResult {
  query: EARSRequirement;
  related: RelatedRequirement[];
  searchTime: number;  // milliseconds
}

class RelatedRequirementsFinder {
  private yataClient: YataClient;
  private readonly RELEVANCE_THRESHOLD = 0.7;
  private readonly SEARCH_TIMEOUT = 5000; // 5 seconds (REQ-RA-003)

  /**
   * Search related requirements using YATA knowledge graph
   * Must complete within 5 seconds (REQ-RA-003)
   */
  async search(requirement: EARSRequirement): Promise<SearchResult> {
    const startTime = Date.now();

    // 1. Extract concepts from requirement
    const concepts = await this.extractConcepts(requirement);

    // 2. Query YATA for related requirements
    const candidates = await this.yataClient.queryRelatedRequirements(
      concepts,
      { timeout: this.SEARCH_TIMEOUT }
    );

    // 3. Calculate relevance scores
    const scored = await Promise.all(
      candidates.map(async (candidate) => ({
        ...candidate,
        relevanceScore: await this.calculateRelevance(requirement, candidate)
      }))
    );

    // 4. Filter by threshold (0.7+)
    const related = scored
      .filter(r => r.relevanceScore >= this.RELEVANCE_THRESHOLD)
      .sort((a, b) => b.relevanceScore - a.relevanceScore);

    return {
      query: requirement,
      related,
      searchTime: Date.now() - startTime
    };
  }

  /**
   * Determine relationship type between requirements
   */
  private async determineRelationship(
    source: EARSRequirement,
    target: EARSRequirement
  ): Promise<RelatedRequirement['relationship']> {
    const analysis = await this.yataClient.analyzeRelationship(source, target);
    return analysis.type;
  }
}
```

**トレーサビリティ**: REQ-RA-003

---

### 5.4 RequirementsDecomposer

```typescript
// DES-RA-004: RequirementsDecomposer
// Traces to: REQ-RA-004

interface DecomposedRequirement {
  parentId: string;
  children: SubRequirement[];
  decompositionGraph: DecompositionGraph;
}

interface SubRequirement {
  id: string;          // Auto-generated: {parentId}-{index}
  text: string;        // EARS format
  pattern: EARSPattern;
  parentId: string;
}

interface DecompositionGraph {
  nodes: GraphNode[];
  edges: GraphEdge[];
}

class RequirementsDecomposer {
  private llmClient: LLMClient;
  private earsValidator: EARSValidator;

  /**
   * Decompose complex requirement into sub-requirements
   * Each sub-requirement gets unique ID and EARS format validation
   */
  async decompose(requirement: EARSRequirement): Promise<DecomposedRequirement> {
    // 1. Use LLM to identify decomposition points
    const decompositionPlan = await this.llmClient.infer(
      this.buildDecompositionPrompt(requirement),
      { systemPrompt: DECOMPOSITION_SYSTEM_PROMPT }
    );

    // 2. Generate sub-requirements
    const children: SubRequirement[] = [];
    const parsedPlan = this.parseDecompositionPlan(decompositionPlan.output);

    for (let i = 0; i < parsedPlan.subRequirements.length; i++) {
      const subReqText = parsedPlan.subRequirements[i];
      const validation = this.earsValidator.validate(subReqText);

      if (!validation.valid) {
        // Auto-correct to EARS format
        const corrected = await this.earsValidator.convertToEARS(
          subReqText,
          this.llmClient
        );
        children.push({
          id: `${requirement.id}-${i + 1}`,
          text: corrected.text,
          pattern: corrected.pattern,
          parentId: requirement.id
        });
      } else {
        children.push({
          id: `${requirement.id}-${i + 1}`,
          text: subReqText,
          pattern: validation.pattern!,
          parentId: requirement.id
        });
      }
    }

    // 3. Build decomposition graph
    const graph = this.buildGraph(requirement, children);

    return {
      parentId: requirement.id,
      children,
      decompositionGraph: graph
    };
  }

  /**
   * Store parent-child relationships in knowledge graph
   */
  private buildGraph(
    parent: EARSRequirement,
    children: SubRequirement[]
  ): DecompositionGraph {
    const nodes: GraphNode[] = [
      { id: parent.id, type: 'parent', label: parent.response },
      ...children.map(c => ({ id: c.id, type: 'child' as const, label: c.text }))
    ];

    const edges: GraphEdge[] = children.map(c => ({
      source: parent.id,
      target: c.id,
      relationship: 'decomposes_to'
    }));

    return { nodes, edges };
  }
}
```

**トレーサビリティ**: REQ-RA-004

---

## 6. 設計生成設計

### 6.1 PatternDetector

```typescript
// DES-DES-001: PatternDetector
// Traces to: REQ-DES-001

interface PatternDetectionResult {
  patterns: DetectedPattern[];
  recommendations: PatternRecommendation[];
}

interface DetectedPattern {
  name: string;
  type: 'creational' | 'structural' | 'behavioral';
  applicabilityScore: number;  // 0.0-1.0
  rationale: string;
  codeExample: string;
}

class PatternDetector {
  // 10+ design patterns (REQ-DES-001)
  private readonly PATTERNS = [
    'Singleton', 'Factory', 'AbstractFactory', 'Builder', 'Prototype',
    'Adapter', 'Bridge', 'Composite', 'Decorator', 'Facade', 'Proxy',
    'ChainOfResponsibility', 'Command', 'Observer', 'Strategy', 'Template'
  ];

  private readonly RECOMMENDATION_THRESHOLD = 0.8;

  /**
   * Detect applicable patterns with 90%+ accuracy (REQ-DES-001)
   */
  async detect(
    requirements: EARSRequirement[],
    context: DesignContext
  ): Promise<PatternDetectionResult> {
    const detectedPatterns: DetectedPattern[] = [];

    for (const patternName of this.PATTERNS) {
      const score = await this.calculateApplicability(
        patternName,
        requirements,
        context
      );

      if (score > 0) {
        detectedPatterns.push({
          name: patternName,
          type: this.getPatternType(patternName),
          applicabilityScore: score,
          rationale: await this.generateRationale(patternName, requirements),
          codeExample: await this.generateCodeExample(patternName, context)
        });
      }
    }

    // Sort by score and filter recommendations
    const sorted = detectedPatterns.sort(
      (a, b) => b.applicabilityScore - a.applicabilityScore
    );

    const recommendations = sorted
      .filter(p => p.applicabilityScore >= this.RECOMMENDATION_THRESHOLD)
      .map(p => ({
        pattern: p,
        priority: this.calculatePriority(p, requirements)
      }));

    return { patterns: sorted, recommendations };
  }
}
```

**トレーサビリティ**: REQ-DES-001

---

### 6.2 SOLIDValidator

```typescript
// DES-DES-003: SOLIDValidator
// Traces to: REQ-DES-003

interface SOLIDValidationResult {
  compliant: boolean;
  violations: SOLIDViolation[];
  suggestions: SOLIDSuggestion[];
  score: number;  // 0-100
}

interface SOLIDViolation {
  principle: 'S' | 'O' | 'L' | 'I' | 'D';
  location: CodeLocation;
  description: string;
  severity: 'error' | 'warning';
}

class SOLIDValidator {
  /**
   * Validate SOLID compliance with 95%+ violation detection (REQ-DES-003)
   */
  async validate(design: DesignDocument): Promise<SOLIDValidationResult> {
    const violations: SOLIDViolation[] = [];
    const suggestions: SOLIDSuggestion[] = [];

    // S - Single Responsibility
    violations.push(...this.validateSingleResponsibility(design));

    // O - Open/Closed
    violations.push(...this.validateOpenClosed(design));

    // L - Liskov Substitution
    violations.push(...this.validateLiskovSubstitution(design));

    // I - Interface Segregation
    violations.push(...this.validateInterfaceSegregation(design));

    // D - Dependency Inversion
    violations.push(...this.validateDependencyInversion(design));

    // Generate fix suggestions
    for (const violation of violations) {
      suggestions.push(await this.generateSuggestion(violation, design));
    }

    const score = this.calculateScore(violations, design);

    return {
      compliant: violations.filter(v => v.severity === 'error').length === 0,
      violations,
      suggestions,
      score
    };
  }
}
```

**トレーサビリティ**: REQ-DES-003

---

### 6.3 FrameworkOptimizer

```typescript
// DES-DES-002: FrameworkOptimizer
// Traces to: REQ-DES-002

interface FrameworkOptimizationResult {
  framework: string;
  version: string;
  bestPractices: BestPractice[];
  patterns: RecommendedPattern[];
  codeExamples: CodeExample[];
}

interface BestPractice {
  category: string;
  description: string;
  rationale: string;
  priority: 'must' | 'should' | 'may';
}

class FrameworkOptimizer {
  // 26 frameworks supported (REQ-DES-002)
  private readonly SUPPORTED_FRAMEWORKS = [
    'react', 'vue', 'angular', 'svelte', 'next.js', 'nuxt',
    'express', 'fastify', 'nestjs', 'koa',
    'django', 'flask', 'fastapi',
    'spring-boot', 'quarkus',
    'rails', 'sinatra',
    'laravel', 'symfony',
    'gin', 'echo', 'fiber',
    'actix', 'axum', 'rocket',
    'phoenix'
  ];

  private yataClient: YataClient;

  /**
   * Optimize design for specific framework
   * Uses YATA's 26 framework knowledge base (REQ-DES-002)
   */
  async optimize(
    design: DesignDocument,
    framework: string
  ): Promise<FrameworkOptimizationResult> {
    if (!this.SUPPORTED_FRAMEWORKS.includes(framework.toLowerCase())) {
      throw new UnsupportedFrameworkError(framework);
    }

    // 1. Query YATA for framework knowledge
    const frameworkKnowledge = await this.yataClient.queryFrameworkKnowledge(
      framework
    );

    // 2. Extract best practices
    const bestPractices = this.extractBestPractices(frameworkKnowledge);

    // 3. Recommend patterns for framework
    const patterns = await this.recommendPatterns(design, frameworkKnowledge);

    // 4. Generate code examples
    const codeExamples = await this.generateCodeExamples(
      design,
      patterns,
      frameworkKnowledge
    );

    return {
      framework,
      version: frameworkKnowledge.latestVersion,
      bestPractices,
      patterns,
      codeExamples
    };
  }

  /**
   * Validate code against framework best practices
   * 90%+ application rate (REQ-DES-002)
   */
  async validateBestPractices(
    code: string,
    framework: string
  ): Promise<ValidationResult> {
    const frameworkKnowledge = await this.yataClient.queryFrameworkKnowledge(
      framework
    );

    const violations: BestPracticeViolation[] = [];
    
    for (const practice of frameworkKnowledge.bestPractices) {
      const compliant = await this.checkCompliance(code, practice);
      if (!compliant) {
        violations.push({
          practice,
          location: await this.findViolationLocation(code, practice),
          suggestion: await this.generateFixSuggestion(code, practice)
        });
      }
    }

    const complianceRate = 1 - (violations.length / frameworkKnowledge.bestPractices.length);

    return {
      compliant: complianceRate >= 0.9,
      complianceRate,
      violations
    };
  }
}
```

**トレーサビリティ**: REQ-DES-002

---

### 6.4 C4ModelGenerator

```typescript
// DES-DES-004: C4ModelGenerator
// Traces to: REQ-DES-004

interface C4Model {
  context: C4ContextDiagram;
  container: C4ContainerDiagram;
  component: C4ComponentDiagram;
  code: C4CodeDiagram[];
  plantUML: string;
  traceabilityLinks: TraceabilityLink[];
}

class C4ModelGenerator {
  /**
   * Generate complete C4 model from design
   * Outputs PlantUML with traceability IDs (REQ-DES-004)
   */
  async generate(design: DesignDocument): Promise<C4Model> {
    // Level 1: System Context
    const context = await this.generateContextDiagram(design);

    // Level 2: Container
    const container = await this.generateContainerDiagram(design);

    // Level 3: Component
    const component = await this.generateComponentDiagram(design);

    // Level 4: Code (optional, per component)
    const code = await this.generateCodeDiagrams(design);

    // Generate PlantUML output
    const plantUML = this.renderToPlantUML(context, container, component, code);

    // Embed traceability links
    const traceabilityLinks = this.generateTraceabilityLinks(design);

    return {
      context,
      container,
      component,
      code,
      plantUML,
      traceabilityLinks
    };
  }

  /**
   * Render C4 diagrams to PlantUML format
   */
  private renderToPlantUML(
    context: C4ContextDiagram,
    container: C4ContainerDiagram,
    component: C4ComponentDiagram,
    code: C4CodeDiagram[]
  ): string {
    const sections: string[] = [];

    // Context diagram
    sections.push(this.renderContextToPlantUML(context));

    // Container diagram
    sections.push(this.renderContainerToPlantUML(container));

    // Component diagram
    sections.push(this.renderComponentToPlantUML(component));

    // Code diagrams
    for (const codeDiagram of code) {
      sections.push(this.renderCodeToPlantUML(codeDiagram));
    }

    return sections.join('\n\n');
  }
}
```

**トレーサビリティ**: REQ-DES-004

---

### 6.5 ADRGenerator

```typescript
// DES-DES-005: ADRGenerator
// Traces to: REQ-DES-005

interface ADR {
  id: string;
  title: string;
  status: 'proposed' | 'accepted' | 'deprecated' | 'superseded';
  date: string;
  context: string;
  decision: string;
  consequences: string[];
  alternatives: Alternative[];
  traceability: string[];
  markdown: string;
}

interface Alternative {
  option: string;
  pros: string[];
  cons: string[];
  rejectionReason: string;
}

class ADRGenerator {
  private llmClient: LLMClient;
  private adrCounter: number = 0;

  /**
   * Generate ADR for design decision (REQ-DES-005)
   * Outputs Markdown format with full rationale
   */
  async generate(decision: DesignDecision): Promise<ADR> {
    this.adrCounter++;
    const id = `ADR-${String(this.adrCounter).padStart(3, '0')}`;

    // 1. Generate context description
    const context = await this.generateContext(decision);

    // 2. Document alternatives considered
    const alternatives = await this.documentAlternatives(decision);

    // 3. Generate consequences
    const consequences = await this.analyzeConsequences(decision);

    // 4. Build ADR structure
    const adr: ADR = {
      id,
      title: decision.title,
      status: 'accepted',
      date: new Date().toISOString().split('T')[0],
      context,
      decision: decision.description,
      consequences,
      alternatives,
      traceability: decision.relatedRequirements,
      markdown: ''
    };

    // 5. Render to Markdown
    adr.markdown = this.renderToMarkdown(adr);

    // 6. Save to file
    await this.saveADR(adr);

    return adr;
  }

  /**
   * Render ADR to Markdown format
   */
  private renderToMarkdown(adr: ADR): string {
    return `# ${adr.id}: ${adr.title}

**Status**: ${adr.status}  
**Date**: ${adr.date}

## Context

${adr.context}

## Decision

${adr.decision}

## Consequences

${adr.consequences.map(c => `- ${c}`).join('\n')}

## Alternatives Considered

${adr.alternatives.map(alt => `
### ${alt.option}

**Pros**: ${alt.pros.join(', ')}  
**Cons**: ${alt.cons.join(', ')}  
**Rejection Reason**: ${alt.rejectionReason}
`).join('\n')}

## Traceability

${adr.traceability.map(t => `- ${t}`).join('\n')}
`;
  }
}
```

**トレーサビリティ**: REQ-DES-005

---

## 7. コード生成設計

### 7.1 CodeGenerator

```typescript
// DES-COD-001: CodeGenerator
// Traces to: REQ-COD-001

interface CodeGenerationResult {
  files: GeneratedFile[];
  metrics: CodeMetrics;
  designAlignment: DesignAlignmentResult;
  securityScan: SecurityScanResult;
}

interface GeneratedFile {
  path: string;
  content: string;
  language: string;
  requirementIds: string[];  // Traceability
  designComponentIds: string[];
}

class CodeGenerator {
  private llmClient: LLMClient;
  private yataClient: YataClient;
  private staticAnalyzer: StaticAnalyzer;
  private securityScanner: SecurityScanner;

  /**
   * Generate code with 95%+ success rate (REQ-COD-001)
   * Syntax error rate <5%
   * Design alignment 95%+
   */
  async generate(design: DesignDocument): Promise<CodeGenerationResult> {
    const files: GeneratedFile[] = [];

    for (const component of design.components) {
      // 1. Generate code using LLM
      const code = await this.generateComponentCode(component);

      // 2. Validate with YATA
      const validation = await this.yataClient.validateCode(code);

      // 3. Static analysis
      const metrics = await this.staticAnalyzer.analyze(code);

      // 4. Security scan (REQ-COD-006)
      const security = await this.securityScanner.scan(code);

      if (security.vulnerabilities.length > 0) {
        throw new SecurityViolationError(security.vulnerabilities);
      }

      // 5. Retry if quality issues
      if (!this.meetsQualityStandards(metrics)) {
        const improved = await this.improveCode(code, metrics);
        files.push(improved);
      } else {
        files.push({
          path: this.buildPath(component),
          content: code,
          language: design.language,
          requirementIds: component.requirementIds,
          designComponentIds: [component.id]
        });
      }
    }

    return {
      files,
      metrics: this.aggregateMetrics(files),
      designAlignment: await this.checkDesignAlignment(files, design),
      securityScan: await this.securityScanner.scanAll(files)
    };
  }
}
```

**トレーサビリティ**: REQ-COD-001, REQ-COD-002, REQ-COD-006

---

### 7.2 SecurityScanner

```typescript
// DES-COD-006: SecurityScanner
// Traces to: REQ-COD-006

enum VulnerabilityType {
  SQL_INJECTION = 'sql_injection',
  XSS = 'xss',
  HARDCODED_CREDENTIALS = 'hardcoded_credentials',
  INSECURE_CRYPTO = 'insecure_crypto',
  PATH_TRAVERSAL = 'path_traversal',
  COMMAND_INJECTION = 'command_injection',
  INSECURE_DESERIALIZATION = 'insecure_deserialization',
  XXE = 'xxe',
  SSRF = 'ssrf',
  OPEN_REDIRECT = 'open_redirect'
}

interface Vulnerability {
  type: VulnerabilityType;
  severity: 'critical' | 'high' | 'medium' | 'low';
  location: CodeLocation;
  description: string;
  remediation: string;
  cweId: string;
}

class SecurityScanner {
  // 98%+ detection rate for major vulnerabilities (REQ-COD-006)
  // <10% false positive rate

  async scan(code: string): Promise<SecurityScanResult> {
    const vulnerabilities: Vulnerability[] = [];

    // Check all 10 vulnerability types
    vulnerabilities.push(...await this.detectSQLInjection(code));
    vulnerabilities.push(...await this.detectXSS(code));
    vulnerabilities.push(...await this.detectHardcodedCredentials(code));
    vulnerabilities.push(...await this.detectInsecureCrypto(code));
    vulnerabilities.push(...await this.detectPathTraversal(code));
    vulnerabilities.push(...await this.detectCommandInjection(code));
    vulnerabilities.push(...await this.detectInsecureDeserialization(code));
    vulnerabilities.push(...await this.detectXXE(code));
    vulnerabilities.push(...await this.detectSSRF(code));
    vulnerabilities.push(...await this.detectOpenRedirect(code));

    return {
      vulnerabilities,
      passed: vulnerabilities.length === 0,
      report: this.generateReport(vulnerabilities)
    };
  }
}
```

**トレーサビリティ**: REQ-COD-006

---

### 7.3 StaticAnalyzer

```typescript
// DES-COD-002: StaticAnalyzer
// Traces to: REQ-COD-002, REQ-QUA-001

interface StaticAnalysisResult {
  ast: AST;
  metrics: CodeMetrics;
  issues: CodeIssue[];
  qualityScore: number;
}

interface CodeMetrics {
  cyclomaticComplexity: number;     // Target: ≤10 (REQ-QUA-001)
  linesPerFunction: number;         // Target: ≤50 (REQ-QUA-001)
  linesPerClass: number;            // Target: ≤300 (REQ-QUA-001)
  duplicateCodePercentage: number;  // Target: ≤5% (REQ-QUA-001)
  maintainabilityIndex: number;
}

class StaticAnalyzer {
  private treeSitter: TreeSitter;

  /**
   * Analyze code using Tree-sitter AST
   * 100% AST parsing success rate (REQ-COD-002)
   */
  async analyze(code: string, language: string): Promise<StaticAnalysisResult> {
    // 1. Parse AST using Tree-sitter
    const ast = await this.treeSitter.parse(code, language);

    if (!ast) {
      throw new ASTParseError(`Failed to parse ${language} code`);
    }

    // 2. Calculate quality metrics
    const metrics = this.calculateMetrics(ast);

    // 3. Detect code issues
    const issues = this.detectIssues(ast, metrics);

    // 4. Calculate overall quality score
    const qualityScore = this.calculateQualityScore(metrics, issues);

    return { ast, metrics, issues, qualityScore };
  }

  /**
   * Calculate code quality metrics (REQ-QUA-001)
   */
  private calculateMetrics(ast: AST): CodeMetrics {
    return {
      cyclomaticComplexity: this.calculateCyclomaticComplexity(ast),
      linesPerFunction: this.calculateLinesPerFunction(ast),
      linesPerClass: this.calculateLinesPerClass(ast),
      duplicateCodePercentage: this.calculateDuplicateCode(ast),
      maintainabilityIndex: this.calculateMaintainabilityIndex(ast)
    };
  }

  /**
   * Check if metrics meet quality standards
   */
  meetsQualityStandards(metrics: CodeMetrics): boolean {
    return (
      metrics.cyclomaticComplexity <= 10 &&
      metrics.linesPerFunction <= 50 &&
      metrics.linesPerClass <= 300 &&
      metrics.duplicateCodePercentage <= 5
    );
  }
}
```

**トレーサビリティ**: REQ-COD-002, REQ-QUA-001

---

### 7.4 PatternConformanceChecker

```typescript
// DES-COD-003: PatternConformanceChecker
// Traces to: REQ-COD-003

interface ConformanceResult {
  pattern: string;
  conformant: boolean;
  violations: PatternViolation[];
  autoFixAttempts: number;
  finalCode?: string;
}

interface PatternViolation {
  element: string;
  expected: string;
  actual: string;
  location: CodeLocation;
}

class PatternConformanceChecker {
  private readonly MAX_FIX_ATTEMPTS = 3;  // REQ-COD-003

  /**
   * Verify code conforms to specified design pattern
   * 90%+ verification accuracy (REQ-COD-003)
   */
  async checkConformance(
    code: string,
    pattern: string,
    language: string
  ): Promise<ConformanceResult> {
    const patternDefinition = this.loadPatternDefinition(pattern);
    const violations: PatternViolation[] = [];

    // Check each pattern element
    for (const element of patternDefinition.requiredElements) {
      const found = await this.findElement(code, element, language);
      if (!found) {
        violations.push({
          element: element.name,
          expected: element.description,
          actual: 'Not found',
          location: { line: 0, column: 0 }
        });
      } else if (!this.matchesSignature(found, element)) {
        violations.push({
          element: element.name,
          expected: element.signature,
          actual: found.signature,
          location: found.location
        });
      }
    }

    // If violations, attempt auto-fix
    if (violations.length > 0) {
      const fixResult = await this.attemptAutoFix(
        code,
        violations,
        patternDefinition,
        language
      );
      return fixResult;
    }

    return {
      pattern,
      conformant: true,
      violations: [],
      autoFixAttempts: 0
    };
  }

  /**
   * Auto-fix pattern violations (80%+ success rate)
   * Maximum 3 attempts before error report (REQ-COD-003)
   */
  private async attemptAutoFix(
    code: string,
    violations: PatternViolation[],
    pattern: PatternDefinition,
    language: string
  ): Promise<ConformanceResult> {
    let currentCode = code;
    let attempts = 0;

    while (attempts < this.MAX_FIX_ATTEMPTS) {
      attempts++;
      currentCode = await this.applyFix(currentCode, violations, pattern, language);
      
      const recheckViolations = await this.checkViolations(
        currentCode,
        pattern,
        language
      );

      if (recheckViolations.length === 0) {
        return {
          pattern: pattern.name,
          conformant: true,
          violations: [],
          autoFixAttempts: attempts,
          finalCode: currentCode
        };
      }
    }

    // Max attempts reached, report error
    return {
      pattern: pattern.name,
      conformant: false,
      violations,
      autoFixAttempts: this.MAX_FIX_ATTEMPTS
    };
  }
}
```

**トレーサビリティ**: REQ-COD-003

---

### 7.5 DependencyAnalyzer

```typescript
// DES-COD-004: DependencyAnalyzer
// Traces to: REQ-COD-004

interface DependencyAnalysisResult {
  dependencies: Dependency[];
  circularDependencies: CircularDependency[];
  unresolvedDependencies: UnresolvedDependency[];
  dependencyGraph: DependencyGraph;
}

interface CircularDependency {
  cycle: string[];       // Module names in cycle
  severity: 'error' | 'warning';
}

interface UnresolvedDependency {
  module: string;
  importedBy: string;
  suggestions: string[];
}

class DependencyAnalyzer {
  private yataClient: YataClient;

  /**
   * Analyze dependencies using YATA knowledge graph
   * 100% circular dependency detection (REQ-COD-004)
   */
  async analyze(code: GeneratedFile[]): Promise<DependencyAnalysisResult> {
    // 1. Extract dependencies from all files
    const dependencies = await this.extractDependencies(code);

    // 2. Build dependency graph
    const graph = this.buildDependencyGraph(dependencies);

    // 3. Detect circular dependencies (100% detection rate)
    const circularDependencies = this.detectCircularDependencies(graph);

    // 4. Find unresolved dependencies (95%+ accuracy)
    const unresolvedDependencies = await this.findUnresolvedDependencies(
      dependencies,
      graph
    );

    return {
      dependencies,
      circularDependencies,
      unresolvedDependencies,
      dependencyGraph: graph
    };
  }

  /**
   * Detect circular dependencies using Tarjan's algorithm
   * Must achieve 100% detection rate (REQ-COD-004)
   */
  private detectCircularDependencies(
    graph: DependencyGraph
  ): CircularDependency[] {
    const sccs = this.tarjanSCC(graph);
    const circular: CircularDependency[] = [];

    for (const scc of sccs) {
      if (scc.length > 1) {
        circular.push({
          cycle: scc,
          severity: 'error'
        });
      } else if (this.hasSelfLoop(graph, scc[0])) {
        circular.push({
          cycle: [scc[0], scc[0]],
          severity: 'error'
        });
      }
    }

    return circular;
  }

  /**
   * Find unresolved dependencies with suggestions
   * 95%+ accuracy (REQ-COD-004)
   */
  private async findUnresolvedDependencies(
    dependencies: Dependency[],
    graph: DependencyGraph
  ): Promise<UnresolvedDependency[]> {
    const unresolved: UnresolvedDependency[] = [];

    for (const dep of dependencies) {
      if (!this.canResolve(dep, graph)) {
        const suggestions = await this.yataClient.suggestPackages(dep.name);
        unresolved.push({
          module: dep.name,
          importedBy: dep.importedBy,
          suggestions
        });
      }
    }

    return unresolved;
  }
}
```

**トレーサビリティ**: REQ-COD-004

---

### 7.6 CodingStandardsChecker

```typescript
// DES-COD-005: CodingStandardsChecker
// Traces to: REQ-COD-005

interface StandardsCheckResult {
  compliant: boolean;
  violations: StandardViolation[];
  autoFixedCount: number;
  report: StandardsReport;
}

interface StandardViolation {
  rule: string;
  category: 'naming' | 'indentation' | 'comments' | 'formatting';
  location: CodeLocation;
  message: string;
  autoFixable: boolean;
}

class CodingStandardsChecker {
  /**
   * Check and auto-fix coding standards
   * 95%+ violation detection, 90%+ auto-fix success (REQ-COD-005)
   */
  async check(
    code: string,
    language: string,
    projectConfig?: CodingStandardsConfig
  ): Promise<StandardsCheckResult> {
    const config = projectConfig || await this.loadDefaultConfig(language);
    const violations: StandardViolation[] = [];

    // 1. Check naming conventions
    violations.push(...this.checkNamingConventions(code, config.naming));

    // 2. Check indentation
    violations.push(...this.checkIndentation(code, config.indentation));

    // 3. Check comments
    violations.push(...this.checkComments(code, config.comments));

    // 4. Check formatting
    violations.push(...this.checkFormatting(code, config.formatting));

    // 5. Auto-fix violations
    const autoFixable = violations.filter(v => v.autoFixable);
    let fixedCode = code;
    let autoFixedCount = 0;

    for (const violation of autoFixable) {
      try {
        fixedCode = await this.autoFix(fixedCode, violation);
        autoFixedCount++;
      } catch (e) {
        // Continue with next violation
      }
    }

    return {
      compliant: violations.length === autoFixedCount,
      violations,
      autoFixedCount,
      report: this.generateReport(violations, autoFixedCount)
    };
  }

  /**
   * Apply project-specific coding standards from steering files
   */
  private async loadDefaultConfig(language: string): Promise<CodingStandardsConfig> {
    // Load from steering/tech.md if available
    const techConfig = await this.loadSteeringTech();
    return techConfig.codingStandards[language] || this.getLanguageDefaults(language);
  }
}
```

**トレーサビリティ**: REQ-COD-005

---

## 8. テスト生成設計

### 8.1 UnitTestGenerator

```typescript
// DES-TST-001: UnitTestGenerator
// Traces to: REQ-TST-001

interface TestGenerationResult {
  testFiles: GeneratedTestFile[];
  coverage: CoverageEstimate;
  requirementMapping: RequirementTestMapping[];
}

class UnitTestGenerator {
  /**
   * Generate unit tests with 90%+ success rate (REQ-TST-001)
   * Target 80%+ coverage
   * 100% requirement mapping
   */
  async generate(code: GeneratedFile[]): Promise<TestGenerationResult> {
    const testFiles: GeneratedTestFile[] = [];
    const mappings: RequirementTestMapping[] = [];

    for (const file of code) {
      // Parse functions/methods
      const functions = await this.parseFunctions(file);

      for (const func of functions) {
        // Generate test cases
        const testCases = await this.generateTestCases(func);

        // Map to requirements (100% mapping required)
        for (const reqId of file.requirementIds) {
          mappings.push({
            requirementId: reqId,
            testCaseIds: testCases.map(t => t.id)
          });
        }

        testFiles.push({
          path: this.buildTestPath(file),
          content: this.buildTestFile(testCases),
          targetFile: file.path,
          testCases
        });
      }
    }

    return {
      testFiles,
      coverage: this.estimateCoverage(testFiles, code),
      requirementMapping: mappings
    };
  }
}
```

**トレーサビリティ**: REQ-TST-001

---

### 8.2 IntegrationTestGenerator

```typescript
// DES-TST-002: IntegrationTestGenerator
// Traces to: REQ-TST-002
// 憲法準拠: Article IX (Integration-First Testing)

interface IntegrationTestConfig {
  useRealDatabase: boolean;    // Must be true (Article IX)
  useSandboxAPIs: boolean;     // Must be true for external APIs
  mockJustification?: string;  // Required if mocks used
}

class IntegrationTestGenerator {
  /**
   * Generate integration tests using real services (Article IX)
   * Mocks only allowed with documented justification
   */
  async generate(
    components: DesignComponent[],
    config: IntegrationTestConfig
  ): Promise<IntegrationTestResult> {
    // Validate Article IX compliance
    if (!config.useRealDatabase) {
      throw new ConstitutionViolationError(
        'Article IX requires real database for integration tests'
      );
    }

    const testScenarios: IntegrationTestScenario[] = [];

    for (const interaction of this.findInteractions(components)) {
      const scenario = await this.generateScenario(interaction);

      // Docker Compose setup for real services
      const dockerConfig = this.generateDockerConfig(interaction);

      // Cleanup automation
      const cleanup = this.generateCleanupScript(interaction);

      testScenarios.push({
        ...scenario,
        dockerConfig,
        cleanup,
        mockJustification: config.mockJustification
      });
    }

    return {
      scenarios: testScenarios,
      dockerCompose: this.aggregateDockerConfig(testScenarios),
      cleanupScript: this.aggregateCleanup(testScenarios)
    };
  }
}
```

**トレーサビリティ**: REQ-TST-002  
**憲法準拠**: Article IX（Integration-First Testing）

---

### 8.3 CoverageReporter

```typescript
// DES-QUA-002: CoverageReporter
// Traces to: REQ-QUA-002

interface CoverageReport {
  summary: CoverageSummary;
  files: FileCoverage[];
  uncoveredLines: UncoveredLine[];
  requirementCoverage: RequirementCoverage[];
}

interface CoverageSummary {
  lineCoverage: number;      // Target: ≥80% (REQ-QUA-002)
  branchCoverage: number;    // Target: ≥75% (REQ-QUA-002)
  functionCoverage: number;  // Target: ≥90% (REQ-QUA-002)
  overallScore: number;
  meetsTargets: boolean;
}

class CoverageReporter {
  private readonly TARGETS = {
    line: 80,
    branch: 75,
    function: 90
  };

  /**
   * Generate comprehensive coverage report
   * Validates against REQ-QUA-002 targets
   */
  async generateReport(testResults: TestResults): Promise<CoverageReport> {
    // 1. Calculate coverage metrics
    const lineCoverage = this.calculateLineCoverage(testResults);
    const branchCoverage = this.calculateBranchCoverage(testResults);
    const functionCoverage = this.calculateFunctionCoverage(testResults);

    // 2. Check if targets met
    const meetsTargets = (
      lineCoverage >= this.TARGETS.line &&
      branchCoverage >= this.TARGETS.branch &&
      functionCoverage >= this.TARGETS.function
    );

    // 3. Identify uncovered lines
    const uncoveredLines = this.findUncoveredLines(testResults);

    // 4. Map to requirements
    const requirementCoverage = await this.mapToRequirements(testResults);

    return {
      summary: {
        lineCoverage,
        branchCoverage,
        functionCoverage,
        overallScore: (lineCoverage + branchCoverage + functionCoverage) / 3,
        meetsTargets
      },
      files: testResults.files,
      uncoveredLines,
      requirementCoverage
    };
  }

  /**
   * Output coverage report in multiple formats
   */
  async export(
    report: CoverageReport,
    formats: ('html' | 'json' | 'lcov' | 'cobertura')[]
  ): Promise<ExportResult[]> {
    const results: ExportResult[] = [];

    for (const format of formats) {
      const exported = await this.exportFormat(report, format);
      results.push(exported);
    }

    return results;
  }
}
```

**トレーサビリティ**: REQ-QUA-002

---

## 9. トレーサビリティ設計

### 9.1 TraceabilityManager

```typescript
// DES-TRA-001: TraceabilityManager
// Traces to: REQ-TRA-001, REQ-TRA-002
// 憲法準拠: Article V (Traceability Mandate)

interface TraceabilityMatrix {
  requirements: RequirementTrace[];
  designs: DesignTrace[];
  code: CodeTrace[];
  tests: TestTrace[];
  coverage: {
    requirementsCovered: number;
    designsCovered: number;
    codeCovered: number;
    testsCovered: number;
    total: number;  // Must be 100% (REQ-TRA-001)
  };
  brokenLinks: BrokenLink[];
}

interface RequirementTrace {
  id: string;
  designIds: string[];
  codeIds: string[];
  testIds: string[];
  status: 'complete' | 'partial' | 'missing';
}

class TraceabilityManager {
  /**
   * Generate traceability matrix with 100% coverage (REQ-TRA-001)
   * Zero broken links required
   */
  async generateMatrix(): Promise<TraceabilityMatrix> {
    const requirements = await this.loadRequirements();
    const designs = await this.loadDesigns();
    const code = await this.loadCode();
    const tests = await this.loadTests();

    const matrix: TraceabilityMatrix = {
      requirements: [],
      designs: [],
      code: [],
      tests: [],
      coverage: { requirementsCovered: 0, designsCovered: 0, codeCovered: 0, testsCovered: 0, total: 0 },
      brokenLinks: []
    };

    // Build bidirectional links
    for (const req of requirements) {
      const trace = this.traceRequirement(req, designs, code, tests);
      matrix.requirements.push(trace);

      // Check for broken links
      if (trace.status !== 'complete') {
        matrix.brokenLinks.push(...this.findBrokenLinks(trace));
      }
    }

    // Calculate coverage
    matrix.coverage = this.calculateCoverage(matrix);

    // Validate 100% coverage requirement
    if (matrix.coverage.total < 100) {
      console.warn(`Coverage ${matrix.coverage.total}% < 100% required by Article V`);
    }

    return matrix;
  }

  /**
   * Impact analysis for requirement changes (REQ-TRA-002)
   * 95%+ accuracy in identifying affected artifacts
   */
  async analyzeImpact(requirementId: string): Promise<ImpactAnalysisResult> {
    const matrix = await this.generateMatrix();
    const requirement = matrix.requirements.find(r => r.id === requirementId);

    if (!requirement) {
      throw new Error(`Requirement ${requirementId} not found`);
    }

    const affectedDesigns = await this.findAffectedDesigns(requirement);
    const affectedCode = await this.findAffectedCode(requirement);
    const affectedTests = await this.findAffectedTests(requirement);

    return {
      requirementId,
      affectedDesigns,
      affectedCode,
      affectedTests,
      recommendations: this.generateChangeRecommendations(
        requirement,
        affectedDesigns,
        affectedCode,
        affectedTests
      ),
      report: this.generateImpactReport(requirement, affectedDesigns, affectedCode, affectedTests)
    };
  }
}
```

**トレーサビリティ**: REQ-TRA-001, REQ-TRA-002  
**憲法準拠**: Article V（Traceability Mandate）

---

## 10. エラーリカバリ設計

### 10.1 GracefulDegradation

```typescript
// DES-ERR-001: GracefulDegradation
// Traces to: REQ-ERR-001

enum SystemMode {
  FULL = 'full',                    // MUSUBI + YATA
  NEURAL_ONLY = 'neural_only',      // LLM only (fallback)
  SYMBOLIC_ONLY = 'symbolic_only',  // YATA only (fallback)
  OFFLINE = 'offline'               // Cached data only
}

interface SystemStatus {
  mode: SystemMode;
  yataAvailable: boolean;
  llmAvailable: boolean;
  lastYataCheck: Date;
  degradationReason?: string;
}

class GracefulDegradation {
  private readonly RECONNECT_INTERVAL = 30000; // 30 seconds (REQ-ERR-001)
  private currentMode: SystemMode = SystemMode.FULL;
  private reconnectTimer?: NodeJS.Timer;

  /**
   * Handle YATA server unavailability
   * Fallback to LLM-only mode with user notification
   */
  async handleYataFailure(error: Error): Promise<void> {
    // 1. Switch to neural-only mode
    this.currentMode = SystemMode.NEURAL_ONLY;

    // 2. Notify user of degraded functionality
    await this.notifyUser({
      type: 'warning',
      title: 'Degraded Mode Active',
      message: 'YATA server unavailable. Running in LLM-only mode with limited symbolic reasoning.',
      affectedFeatures: [
        'Ontology validation',
        'Pattern detection accuracy may be reduced',
        'Contradiction detection limited'
      ]
    });

    // 3. Start reconnection attempts
    this.startReconnectionAttempts();
  }

  private startReconnectionAttempts(): void {
    this.reconnectTimer = setInterval(async () => {
      try {
        const yataStatus = await this.checkYataAvailability();
        if (yataStatus.available) {
          await this.restoreFullMode();
        }
      } catch (e) {
        // Continue in degraded mode
      }
    }, this.RECONNECT_INTERVAL);
  }

  private async restoreFullMode(): Promise<void> {
    this.currentMode = SystemMode.FULL;
    clearInterval(this.reconnectTimer);

    await this.notifyUser({
      type: 'success',
      title: 'Full Mode Restored',
      message: 'YATA server connection restored. All features available.'
    });
  }
}
```

**トレーサビリティ**: REQ-ERR-001

---

### 10.2 DataPersistence

```typescript
// DES-ERR-002: DataPersistence
// Traces to: REQ-ERR-002

interface PersistenceConfig {
  backupInterval: number;  // 1 hour (REQ-ERR-002)
  maxBackups: number;
  storageDir: string;
}

class DataPersistence {
  private readonly BACKUP_INTERVAL = 3600000; // 1 hour in ms

  /**
   * Persist all inference results and design decisions
   * Enable recovery from last stable state
   */
  async persist(data: PersistableData): Promise<void> {
    const timestamp = Date.now();
    const checkpoint = {
      timestamp,
      data,
      checksum: this.calculateChecksum(data)
    };

    // Write to primary storage
    await this.writeCheckpoint(checkpoint);

    // Write to backup
    await this.writeBackup(checkpoint);
  }

  /**
   * Recover from last stable state after system failure
   * Maximum data loss: 1 hour
   */
  async recover(): Promise<RecoveryResult> {
    const checkpoints = await this.loadCheckpoints();
    const latest = this.findLatestValid(checkpoints);

    if (!latest) {
      return { success: false, reason: 'No valid checkpoint found' };
    }

    const dataLoss = Date.now() - latest.timestamp;
    const dataLossHours = dataLoss / 3600000;

    if (dataLossHours > 1) {
      console.warn(`Data loss exceeds 1 hour: ${dataLossHours.toFixed(2)} hours`);
    }

    return {
      success: true,
      restoredFrom: latest.timestamp,
      dataLoss: dataLossHours,
      data: latest.data
    };
  }

  /**
   * Automatic backup every hour
   */
  startAutomaticBackup(): void {
    setInterval(async () => {
      const currentState = await this.getCurrentState();
      await this.persist(currentState);
    }, this.BACKUP_INTERVAL);
  }
}
```

**トレーサビリティ**: REQ-ERR-002

---

### 10.3 VersionCompatibility

```typescript
// DES-ERR-003: VersionCompatibility
// Traces to: REQ-ERR-003

interface CompatibilityResult {
  compatible: boolean;
  currentVersion: string;
  dataVersion: string;
  migrationRequired: boolean;
  migrationPlan?: MigrationPlan;
  warnings: CompatibilityWarning[];
}

interface MigrationPlan {
  steps: MigrationStep[];
  estimatedTime: number;
  backupRequired: boolean;
  rollbackSupported: boolean;
}

class VersionCompatibility {
  private readonly CURRENT_VERSION = '1.0.0';

  /**
   * Check backward compatibility with existing project data
   * Provide migration scripts when needed (REQ-ERR-003)
   */
  async checkCompatibility(projectPath: string): Promise<CompatibilityResult> {
    // 1. Read project data version
    const dataVersion = await this.readDataVersion(projectPath);

    // 2. Compare versions
    const comparison = this.compareVersions(dataVersion, this.CURRENT_VERSION);

    // 3. Determine if migration needed
    const migrationRequired = comparison < 0;
    const warnings: CompatibilityWarning[] = [];

    if (migrationRequired) {
      // 4. Generate migration plan
      const migrationPlan = await this.generateMigrationPlan(
        dataVersion,
        this.CURRENT_VERSION
      );

      // 5. Check for breaking changes
      const breakingChanges = this.detectBreakingChanges(
        dataVersion,
        this.CURRENT_VERSION
      );

      if (breakingChanges.length > 0) {
        warnings.push({
          type: 'breaking_change',
          message: `Breaking changes detected: ${breakingChanges.join(', ')}`,
          severity: 'error'
        });
      }

      return {
        compatible: false,
        currentVersion: this.CURRENT_VERSION,
        dataVersion,
        migrationRequired: true,
        migrationPlan,
        warnings
      };
    }

    return {
      compatible: true,
      currentVersion: this.CURRENT_VERSION,
      dataVersion,
      migrationRequired: false,
      warnings
    };
  }

  /**
   * Execute migration with automatic backup
   */
  async migrate(
    projectPath: string,
    plan: MigrationPlan
  ): Promise<MigrationResult> {
    // 1. Create backup
    if (plan.backupRequired) {
      await this.createBackup(projectPath);
    }

    // 2. Execute migration steps
    for (const step of plan.steps) {
      try {
        await this.executeStep(projectPath, step);
      } catch (error) {
        // Rollback on failure
        if (plan.rollbackSupported) {
          await this.rollback(projectPath);
        }
        throw new MigrationError(step, error);
      }
    }

    // 3. Update version marker
    await this.updateDataVersion(projectPath, this.CURRENT_VERSION);

    return { success: true, newVersion: this.CURRENT_VERSION };
  }
}
```

**トレーサビリティ**: REQ-ERR-003

---

## 11. MCP Server設計

### 11.1 MCPサーバー構成

```typescript
// DES-INT-102: MCPServer
// Traces to: REQ-INT-102

interface MCPServerConfig {
  transport: 'stdio' | 'sse';
  tools: MCPTool[];
  prompts: MCPPrompt[];
  resources: MCPResource[];
}

const MUSUBIX_MCP_CONFIG: MCPServerConfig = {
  transport: 'stdio', // Also supports 'sse'
  
  tools: [
    // Requirements Tools
    { name: 'analyze_requirements', handler: analyzeRequirements },
    { name: 'validate_ears', handler: validateEARS },
    { name: 'map_ontology', handler: mapOntology },
    
    // Design Tools
    { name: 'generate_design', handler: generateDesign },
    { name: 'detect_patterns', handler: detectPatterns },
    { name: 'validate_solid', handler: validateSOLID },
    { name: 'generate_c4', handler: generateC4 },
    
    // Code Tools
    { name: 'generate_code', handler: generateCode },
    { name: 'analyze_code', handler: analyzeCode },
    { name: 'scan_security', handler: scanSecurity },
    
    // Test Tools
    { name: 'generate_tests', handler: generateTests },
    { name: 'measure_coverage', handler: measureCoverage },
    
    // Traceability Tools
    { name: 'trace_matrix', handler: generateTraceMatrix },
    { name: 'impact_analysis', handler: analyzeImpact },
    
    // Explanation Tools
    { name: 'explain', handler: explain },
    { name: 'reasoning_graph', handler: generateReasoningGraph }
  ],
  
  prompts: [
    { name: 'requirements_prompt', template: REQUIREMENTS_TEMPLATE },
    { name: 'design_prompt', template: DESIGN_TEMPLATE },
    { name: 'code_prompt', template: CODE_TEMPLATE }
  ],
  
  resources: [
    { uri: 'musubix://steering/structure', handler: loadStructure },
    { uri: 'musubix://steering/tech', handler: loadTech },
    { uri: 'musubix://steering/product', handler: loadProduct },
    { uri: 'musubix://requirements/{id}', handler: loadRequirement },
    { uri: 'musubix://design/{id}', handler: loadDesign }
  ]
};
```

**トレーサビリティ**: REQ-INT-102

---

## 11-B. 説明生成設計

### 12.1 ReasoningChainRecorder

```typescript
// DES-EXP-001: ReasoningChainRecorder
// Traces to: REQ-EXP-001

interface ReasoningChain {
  id: string;
  timestamp: Date;
  steps: ReasoningStep[];
  neuralDecisions: NeuralDecision[];
  symbolicDecisions: SymbolicDecision[];
  finalOutcome: Outcome;
}

interface ReasoningStep {
  stepNumber: number;
  timestamp: Date;
  type: 'neural' | 'symbolic' | 'merge';
  input: any;
  output: any;
  rationale: string;
  confidence: number;
}

class ReasoningChainRecorder {
  private currentChain: ReasoningChain | null = null;

  /**
   * Record all reasoning steps (100% recording rate)
   * Preserves both neural and symbolic decision rationales (REQ-EXP-001)
   */
  startRecording(id: string): void {
    this.currentChain = {
      id,
      timestamp: new Date(),
      steps: [],
      neuralDecisions: [],
      symbolicDecisions: [],
      finalOutcome: null as any
    };
  }

  /**
   * Record a reasoning step with full context
   */
  recordStep(step: Omit<ReasoningStep, 'stepNumber' | 'timestamp'>): void {
    if (!this.currentChain) {
      throw new Error('Recording not started');
    }

    this.currentChain.steps.push({
      ...step,
      stepNumber: this.currentChain.steps.length + 1,
      timestamp: new Date()
    });

    // Categorize by type
    if (step.type === 'neural') {
      this.currentChain.neuralDecisions.push({
        step: this.currentChain.steps.length,
        decision: step.output,
        rationale: step.rationale,
        confidence: step.confidence
      });
    } else if (step.type === 'symbolic') {
      this.currentChain.symbolicDecisions.push({
        step: this.currentChain.steps.length,
        decision: step.output,
        rationale: step.rationale,
        valid: step.confidence === 1.0
      });
    }
  }

  /**
   * Finalize and persist reasoning chain
   */
  async finalize(outcome: Outcome): Promise<ReasoningChain> {
    if (!this.currentChain) {
      throw new Error('Recording not started');
    }

    this.currentChain.finalOutcome = outcome;
    const chain = this.currentChain;

    // Persist to storage
    await this.persist(chain);

    this.currentChain = null;
    return chain;
  }

  /**
   * Generate structured log in chronological order
   */
  generateLog(chain: ReasoningChain): StructuredLog {
    return {
      id: chain.id,
      timestamp: chain.timestamp.toISOString(),
      duration: this.calculateDuration(chain),
      steps: chain.steps.map(s => ({
        step: s.stepNumber,
        time: s.timestamp.toISOString(),
        type: s.type,
        summary: s.rationale,
        confidence: s.confidence
      })),
      outcome: chain.finalOutcome
    };
  }
}
```

**トレーサビリティ**: REQ-EXP-001

---

### 12.2 ExplanationGenerator

```typescript
// DES-EXP-002: ExplanationGenerator
// Traces to: REQ-EXP-002

interface Explanation {
  summary: string;
  whyRequired: string;
  whyDesign: string;
  patternsApplied: PatternExplanation[];
  constraintsSatisfied: ConstraintExplanation[];
  readabilityScore: number;  // Target: 4.0/5.0+ (REQ-EXP-002)
}

class ExplanationGenerator {
  private llmClient: LLMClient;
  private readonly MIN_READABILITY = 4.0;

  /**
   * Generate natural language explanation from reasoning chain
   * 95%+ generation success rate (REQ-EXP-002)
   */
  async generate(chain: ReasoningChain): Promise<Explanation> {
    // 1. Generate "Why required?" explanation
    const whyRequired = await this.explainRequirement(chain);

    // 2. Generate "Why this design?" explanation
    const whyDesign = await this.explainDesignChoice(chain);

    // 3. Explain applied patterns
    const patternsApplied = await this.explainPatterns(chain);

    // 4. Explain satisfied constraints
    const constraintsSatisfied = await this.explainConstraints(chain);

    // 5. Generate summary
    const summary = await this.generateSummary(
      whyRequired,
      whyDesign,
      patternsApplied,
      constraintsSatisfied
    );

    // 6. Evaluate readability
    const readabilityScore = await this.evaluateReadability(summary);

    // 7. Improve if below threshold
    if (readabilityScore < this.MIN_READABILITY) {
      return this.improveReadability({
        summary,
        whyRequired,
        whyDesign,
        patternsApplied,
        constraintsSatisfied,
        readabilityScore
      });
    }

    return {
      summary,
      whyRequired,
      whyDesign,
      patternsApplied,
      constraintsSatisfied,
      readabilityScore
    };
  }

  /**
   * Explain why a requirement is necessary
   */
  private async explainRequirement(chain: ReasoningChain): Promise<string> {
    const relevantSteps = chain.steps.filter(s => 
      s.rationale.includes('requirement') || s.type === 'symbolic'
    );

    const prompt = this.buildRequirementExplanationPrompt(relevantSteps);
    const result = await this.llmClient.infer(prompt, {
      systemPrompt: EXPLANATION_SYSTEM_PROMPT
    });

    return result.output;
  }

  /**
   * Explain why a particular design was chosen
   */
  private async explainDesignChoice(chain: ReasoningChain): Promise<string> {
    const designSteps = chain.steps.filter(s => 
      s.rationale.includes('design') || s.rationale.includes('pattern')
    );

    const alternatives = await this.identifyAlternatives(designSteps);
    const prompt = this.buildDesignExplanationPrompt(designSteps, alternatives);
    
    return (await this.llmClient.infer(prompt, {
      systemPrompt: EXPLANATION_SYSTEM_PROMPT
    })).output;
  }
}
```

**トレーサビリティ**: REQ-EXP-002

---

### 12.3 VisualExplanationGenerator

```typescript
// DES-EXP-003: VisualExplanationGenerator
// Traces to: REQ-EXP-003

interface VisualExplanation {
  graph: ReasoningGraph;
  graphvizDot: string;
  svgOutput: string;
  interactiveHtml: string;
}

interface ReasoningGraph {
  nodes: ReasoningNode[];
  edges: ReasoningEdge[];
}

interface ReasoningNode {
  id: string;
  type: 'decision' | 'input' | 'output' | 'constraint';
  label: string;
  details: string;
  style: NodeStyle;
}

interface ReasoningEdge {
  source: string;
  target: string;
  label: string;
  type: 'inference' | 'validation' | 'merge';
}

class VisualExplanationGenerator {
  /**
   * Generate visual reasoning graph using Graphviz
   * Interactive exploration support (REQ-EXP-003)
   */
  async generate(chain: ReasoningChain): Promise<VisualExplanation> {
    // 1. Build reasoning graph from chain
    const graph = this.buildGraph(chain);

    // 2. Generate Graphviz DOT format
    const graphvizDot = this.renderToDot(graph);

    // 3. Generate SVG output
    const svgOutput = await this.renderToSvg(graphvizDot);

    // 4. Generate interactive HTML
    const interactiveHtml = this.generateInteractiveHtml(graph, svgOutput);

    return {
      graph,
      graphvizDot,
      svgOutput,
      interactiveHtml
    };
  }

  /**
   * Build reasoning graph from chain
   */
  private buildGraph(chain: ReasoningChain): ReasoningGraph {
    const nodes: ReasoningNode[] = [];
    const edges: ReasoningEdge[] = [];

    // Add nodes for each step
    for (const step of chain.steps) {
      nodes.push({
        id: `step_${step.stepNumber}`,
        type: 'decision',
        label: `Step ${step.stepNumber}`,
        details: step.rationale,
        style: this.getNodeStyle(step.type, step.confidence)
      });

      // Add edge from previous step
      if (step.stepNumber > 1) {
        edges.push({
          source: `step_${step.stepNumber - 1}`,
          target: `step_${step.stepNumber}`,
          label: step.type,
          type: step.type === 'merge' ? 'merge' : 'inference'
        });
      }
    }

    return { nodes, edges };
  }

  /**
   * Render graph to Graphviz DOT format
   */
  private renderToDot(graph: ReasoningGraph): string {
    let dot = 'digraph reasoning {\n';
    dot += '  rankdir=TB;\n';
    dot += '  node [shape=box, style=rounded];\n\n';

    // Nodes
    for (const node of graph.nodes) {
      dot += `  ${node.id} [label="${node.label}\\n${node.details.substring(0, 50)}..."];\n`;
    }

    dot += '\n';

    // Edges
    for (const edge of graph.edges) {
      dot += `  ${edge.source} -> ${edge.target} [label="${edge.label}"];\n`;
    }

    dot += '}\n';
    return dot;
  }
}
```

**トレーサビリティ**: REQ-EXP-003

---

## 12. パフォーマンス設計

### 12.1 PerformanceProfile

```typescript
// DES-PER-001: PerformanceProfile
// Traces to: REQ-PER-001

interface PerformanceProfile {
  responseTimeTargets: ResponseTimeTarget[];
  currentMetrics: PerformanceMetrics;
  optimizations: OptimizationRecommendation[];
}

interface ResponseTimeTarget {
  operation: string;
  targetMs: number;
  currentMs: number;
  status: 'met' | 'warning' | 'exceeded';
}

class PerformanceProfiler {
  // Response time targets (REQ-PER-001)
  private readonly TARGETS = {
    requirementsAnalysis: 10000,   // 10 seconds
    designGeneration: 30000,       // 30 seconds
    codeGeneration: 60000,         // 60 seconds
    explanationGeneration: 5000    // 5 seconds
  };

  /**
   * Profile operation performance and validate against targets
   */
  async profile(operation: string, fn: () => Promise<any>): Promise<ProfilingResult> {
    const start = performance.now();
    const result = await fn();
    const duration = performance.now() - start;

    const target = this.TARGETS[operation as keyof typeof this.TARGETS];
    const status = duration <= target ? 'met' : 
                   duration <= target * 1.2 ? 'warning' : 'exceeded';

    return {
      operation,
      duration,
      target,
      status,
      result
    };
  }

  /**
   * Generate optimization recommendations
   */
  async recommend(metrics: PerformanceMetrics): Promise<OptimizationRecommendation[]> {
    const recommendations: OptimizationRecommendation[] = [];

    for (const metric of metrics.operations) {
      if (metric.status !== 'met') {
        recommendations.push({
          operation: metric.operation,
          issue: `Response time ${metric.currentMs}ms exceeds target ${metric.targetMs}ms`,
          suggestions: await this.generateSuggestions(metric)
        });
      }
    }

    return recommendations;
  }
}
```

**トレーサビリティ**: REQ-PER-001

---

### 12.2 ScalabilityDesign

```typescript
// DES-PER-002: ScalabilityDesign
// Traces to: REQ-PER-002

interface ScalabilityConfig {
  maxConcurrentUsers: number;      // 100 users (REQ-PER-002)
  maxResponseDegradation: number;  // 20% (REQ-PER-002)
  connectionPoolSize: number;
  cacheConfig: CacheConfig;
}

class ScalabilityDesign {
  private readonly config: ScalabilityConfig = {
    maxConcurrentUsers: 100,
    maxResponseDegradation: 0.20,
    connectionPoolSize: 50,
    cacheConfig: {
      enabled: true,
      maxSize: 1000,
      ttlSeconds: 3600
    }
  };

  /**
   * Design scalability mechanisms for 100 concurrent users
   * Response degradation ≤20% (REQ-PER-002)
   */
  getArchitectureRecommendations(): ScalabilityRecommendation[] {
    return [
      {
        area: 'Connection Pooling',
        recommendation: `Use connection pool size of ${this.config.connectionPoolSize}`,
        rationale: 'Prevents connection exhaustion under load'
      },
      {
        area: 'Caching',
        recommendation: 'Cache YATA query results and LLM responses',
        rationale: 'Reduces latency for repeated queries'
      },
      {
        area: 'Request Queuing',
        recommendation: 'Implement request queue with priority',
        rationale: 'Prevents overload and ensures fair processing'
      },
      {
        area: 'Circuit Breaker',
        recommendation: 'Add circuit breaker for external services',
        rationale: 'Prevents cascade failures'
      }
    ];
  }
}
```

**トレーサビリティ**: REQ-PER-002

---

## 13. セキュリティ設計

### 13.1 DataProtector

```typescript
// DES-SEC-001: DataProtector
// Traces to: REQ-SEC-001

interface DataProtectionConfig {
  encryptionAlgorithm: 'AES-256-GCM';
  localProcessingOnly: boolean;      // true (REQ-SEC-001)
  allowedExternalConnections: string[]; // Only LLM API
}

class DataProtector {
  private readonly config: DataProtectionConfig = {
    encryptionAlgorithm: 'AES-256-GCM',
    localProcessingOnly: true,
    allowedExternalConnections: ['api.openai.com', 'api.anthropic.com']
  };

  /**
   * Encrypt user data before storage (REQ-SEC-001)
   */
  async encrypt(data: any): Promise<EncryptedData> {
    const key = await this.getEncryptionKey();
    const iv = crypto.randomBytes(16);
    const cipher = crypto.createCipheriv(
      this.config.encryptionAlgorithm,
      key,
      iv
    );

    const encrypted = Buffer.concat([
      cipher.update(JSON.stringify(data), 'utf8'),
      cipher.final()
    ]);

    return {
      encrypted: encrypted.toString('base64'),
      iv: iv.toString('base64'),
      algorithm: this.config.encryptionAlgorithm
    };
  }

  /**
   * Validate no unauthorized external connections
   */
  validateConnection(url: string): boolean {
    const hostname = new URL(url).hostname;
    return this.config.allowedExternalConnections.includes(hostname);
  }
}
```

**トレーサビリティ**: REQ-SEC-001

---

### 13.2 AuthManager

```typescript
// DES-SEC-002: AuthManager
// Traces to: REQ-SEC-002

interface AuthConfig {
  enabled: boolean;
  roles: Role[];
  auditLogEnabled: boolean;
}

interface Role {
  name: string;
  permissions: Permission[];
}

class AuthManager {
  /**
   * Role-based access control for multi-user environments (REQ-SEC-002)
   */
  private readonly roles: Role[] = [
    {
      name: 'admin',
      permissions: ['read', 'write', 'delete', 'configure']
    },
    {
      name: 'developer',
      permissions: ['read', 'write']
    },
    {
      name: 'viewer',
      permissions: ['read']
    }
  ];

  /**
   * Authenticate user and return session
   */
  async authenticate(credentials: Credentials): Promise<AuthSession> {
    const user = await this.validateCredentials(credentials);
    const session = await this.createSession(user);
    
    await this.auditLog({
      event: 'authentication',
      user: user.id,
      timestamp: new Date(),
      success: true
    });

    return session;
  }

  /**
   * Check if user has permission for operation
   */
  async authorize(session: AuthSession, permission: Permission): Promise<boolean> {
    const role = this.roles.find(r => r.name === session.role);
    const authorized = role?.permissions.includes(permission) ?? false;

    await this.auditLog({
      event: 'authorization',
      user: session.userId,
      permission,
      authorized,
      timestamp: new Date()
    });

    return authorized;
  }
}
```

**トレーサビリティ**: REQ-SEC-002

---

## 14. プラットフォーム互換設計

### 14.1 PlatformAdapter

```typescript
// DES-INT-101: PlatformAdapter
// Traces to: REQ-INT-101

type SupportedPlatform = 
  | 'claude-code'
  | 'github-copilot'
  | 'cursor'
  | 'gemini-cli'
  | 'codex-cli'
  | 'qwen-code'
  | 'windsurf';

interface PlatformConfig {
  platform: SupportedPlatform;
  mcpTransport: 'stdio' | 'sse';
  capabilities: PlatformCapabilities;
}

class PlatformAdapter {
  // 7 platforms supported (REQ-INT-101)
  private readonly PLATFORMS: Map<SupportedPlatform, PlatformConfig> = new Map([
    ['claude-code', { platform: 'claude-code', mcpTransport: 'stdio', capabilities: { streaming: true, tools: true, prompts: true } }],
    ['github-copilot', { platform: 'github-copilot', mcpTransport: 'stdio', capabilities: { streaming: true, tools: true, prompts: false } }],
    ['cursor', { platform: 'cursor', mcpTransport: 'stdio', capabilities: { streaming: true, tools: true, prompts: true } }],
    ['gemini-cli', { platform: 'gemini-cli', mcpTransport: 'stdio', capabilities: { streaming: true, tools: true, prompts: true } }],
    ['codex-cli', { platform: 'codex-cli', mcpTransport: 'stdio', capabilities: { streaming: true, tools: true, prompts: false } }],
    ['qwen-code', { platform: 'qwen-code', mcpTransport: 'stdio', capabilities: { streaming: true, tools: true, prompts: true } }],
    ['windsurf', { platform: 'windsurf', mcpTransport: 'stdio', capabilities: { streaming: true, tools: true, prompts: true } }]
  ]);

  /**
   * Get configuration for specific platform
   */
  getConfig(platform: SupportedPlatform): PlatformConfig {
    const config = this.PLATFORMS.get(platform);
    if (!config) {
      throw new UnsupportedPlatformError(platform);
    }
    return config;
  }

  /**
   * Adapt MCP response for platform-specific requirements
   */
  adaptResponse(response: MCPResponse, platform: SupportedPlatform): AdaptedResponse {
    const config = this.getConfig(platform);
    
    if (!config.capabilities.prompts && response.type === 'prompt') {
      return this.convertPromptToTool(response);
    }

    return response;
  }
}
```

**トレーサビリティ**: REQ-INT-101

---

## 15. 保守性設計

### 15.1 Logger

```typescript
// DES-MNT-001: Logger
// Traces to: REQ-MNT-001

type LogLevel = 'DEBUG' | 'INFO' | 'WARN' | 'ERROR';

interface StructuredLog {
  timestamp: string;
  level: LogLevel;
  message: string;
  context: Record<string, any>;
  correlationId?: string;
}

class Logger {
  private level: LogLevel = 'INFO';

  /**
   * Log structured JSON output (REQ-MNT-001)
   */
  log(level: LogLevel, message: string, context: Record<string, any> = {}): void {
    if (!this.shouldLog(level)) return;

    const log: StructuredLog = {
      timestamp: new Date().toISOString(),
      level,
      message,
      context
    };

    console.log(JSON.stringify(log));
  }

  debug(message: string, context?: Record<string, any>): void {
    this.log('DEBUG', message, context);
  }

  info(message: string, context?: Record<string, any>): void {
    this.log('INFO', message, context);
  }

  warn(message: string, context?: Record<string, any>): void {
    this.log('WARN', message, context);
  }

  error(message: string, context?: Record<string, any>): void {
    this.log('ERROR', message, context);
  }
}
```

**トレーサビリティ**: REQ-MNT-001

---

### 15.2 ErrorHandler

```typescript
// DES-MNT-002: ErrorHandler
// Traces to: REQ-MNT-002

interface ErrorHandlingResult {
  handled: boolean;
  recovered: boolean;
  userMessage: string;
  technicalDetails: ErrorDetails;
}

class ErrorHandler {
  private logger: Logger;

  /**
   * Handle errors with user-friendly messages and auto-recovery
   * 100% error catch rate, 80%+ recovery rate (REQ-MNT-002)
   */
  async handle(error: Error, context: ErrorContext): Promise<ErrorHandlingResult> {
    this.logger.error(error.message, {
      stack: error.stack,
      context,
      timestamp: new Date().toISOString()
    });

    const recoveryResult = await this.attemptRecovery(error, context);
    const userMessage = this.generateUserMessage(error, recoveryResult);

    return {
      handled: true,
      recovered: recoveryResult.success,
      userMessage,
      technicalDetails: {
        errorType: error.constructor.name,
        message: error.message,
        stack: error.stack,
        context
      }
    };
  }

  /**
   * Attempt automatic recovery based on error type
   */
  private async attemptRecovery(
    error: Error,
    context: ErrorContext
  ): Promise<RecoveryResult> {
    const strategy = this.getRecoveryStrategy(error);
    
    if (!strategy) {
      return { success: false, reason: 'No recovery strategy available' };
    }

    try {
      await strategy.execute(context);
      return { success: true };
    } catch (recoveryError) {
      return { success: false, reason: (recoveryError as Error).message };
    }
  }

  /**
   * Generate user-friendly error message
   */
  private generateUserMessage(error: Error, recovery: RecoveryResult): string {
    if (recovery.success) {
      return 'An issue occurred but was automatically resolved. You can continue working.';
    }

    const userMessages: Record<string, string> = {
      'YATAConnectionError': 'Knowledge graph service is temporarily unavailable. Running in limited mode.',
      'LLMRateLimitError': 'AI service rate limit reached. Please wait a moment and try again.',
      'ValidationError': 'Input validation failed. Please check your input and try again.',
      'default': 'An unexpected error occurred. Please try again or contact support.'
    };

    return userMessages[error.constructor.name] || userMessages.default;
  }
}
```

**トレーサビリティ**: REQ-MNT-002

---

## 16. 国際化設計

### 16.1 I18nManager

```typescript
// DES-I18N-001: I18nManager
// Traces to: REQ-I18N-001

type SupportedLocale = 'ja' | 'en';

interface I18nConfig {
  defaultLocale: SupportedLocale;
  supportedLocales: SupportedLocale[];
  fallbackLocale: SupportedLocale;
}

class I18nManager {
  private currentLocale: SupportedLocale = 'ja';
  private translations: Map<SupportedLocale, Record<string, string>> = new Map();

  /**
   * Initialize with supported locales (REQ-I18N-001)
   */
  async initialize(): Promise<void> {
    this.translations.set('ja', await this.loadTranslations('ja'));
    this.translations.set('en', await this.loadTranslations('en'));
  }

  /**
   * Set current locale
   */
  setLocale(locale: SupportedLocale): void {
    if (!this.translations.has(locale)) {
      throw new UnsupportedLocaleError(locale);
    }
    this.currentLocale = locale;
  }

  /**
   * Get translated string
   */
  t(key: string, params?: Record<string, string>): string {
    const translations = this.translations.get(this.currentLocale);
    let text = translations?.[key] || key;

    if (params) {
      for (const [param, value] of Object.entries(params)) {
        text = text.replace(`{${param}}`, value);
      }
    }

    return text;
  }

  /**
   * Get translated error message
   */
  getErrorMessage(errorCode: string): string {
    return this.t(`errors.${errorCode}`);
  }
}
```

**トレーサビリティ**: REQ-I18N-001

---

## 17. Test-First設計ガイドライン（Article III準拠）

### 17.1 Red-Green-Blue サイクル

```typescript
// Test-First Implementation Pattern
// 憲法準拠: Article III (Test-First Imperative)

/**
 * Phase 1: RED - Write failing test first
 */
describe('NeuroSymbolicIntegrator', () => {
  it('should integrate neural and symbolic results', async () => {
    const integrator = new NeuroSymbolicIntegrator();
    const query = 'Generate EARS requirement for user authentication';
    
    const result = await integrator.integrate(query, {});
    
    expect(result.confidence).toBeGreaterThan(0.8);
    expect(result.reasoning).toBeDefined();
  });
});

/**
 * Phase 2: GREEN - Write minimal code to pass
 */
class NeuroSymbolicIntegrator {
  async integrate(query: string, context: any) {
    return {
      confidence: 0.85,
      reasoning: { steps: [] }
    };
  }
}

/**
 * Phase 3: BLUE - Refactor with confidence
 */
class NeuroSymbolicIntegratorRefactored {
  private confidenceEvaluator: ConfidenceEvaluator;
  
  async integrate(query: string, context: IntegrationContext) {
    // Full implementation after tests pass
  }
}
```

### 17.2 テスト構造テンプレート

```typescript
/**
 * Standard test structure for all components
 * Ensures Article III compliance
 */

// 1. Unit Tests - For each class/function
describe('ComponentName', () => {
  describe('methodName', () => {
    it('should [expected behavior] when [condition]', () => {
      // REQ-XXX-NNN mapping in test description
    });
  });
});

// 2. Integration Tests - For component interactions
describe('Integration: ComponentA + ComponentB', () => {
  // Use real services (Article IX)
  // Mock only with documented justification
});

// 3. Requirement Mapping
/**
 * @requirement REQ-INT-001
 * @covers Neural-Symbolic integration
 */
it('should integrate neural and symbolic inference', () => {
  // Test implementation
});
```

### 17.3 テストカバレッジ要件

| カバレッジ種別 | 目標値 | 検証方法 |
|---------------|--------|---------|
| ラインカバレッジ | ≥80% | Jest/Istanbul |
| ブランチカバレッジ | ≥75% | Jest/Istanbul |
| 関数カバレッジ | ≥90% | Jest/Istanbul |
| 要件カバレッジ | 100% | Traceability Matrix |

**トレーサビリティ**: REQ-TST-001, REQ-QUA-002  
**憲法準拠**: Article III（Test-First Imperative）

---

## 18. ADR（アーキテクチャ決定記録）

### ADR-001: 3プロジェクト構成の採用

**ステータス**: Accepted  
**日付**: 2026-01-01  
**コンテキスト**: MUSUBIXシステムのプロジェクト構成を決定する必要がある  
**決定**: core, mcp-server, yata-clientの3プロジェクト構成を採用  
**理由**:
- Article VII（Simplicity Gate）に準拠
- 関心の分離（統合ロジック / MCP通信 / YATA連携）
- 独立したテストと配布が可能

**影響**:
- プロジェクト間の依存関係管理が必要
- モノレポ構成でパッケージ管理を統一

**トレーサビリティ**: REQ-ARC-001

---

### ADR-002: フレームワーク直接使用

**ステータス**: Accepted  
**日付**: 2026-01-01  
**コンテキスト**: 外部フレームワーク（MCP SDK, Tree-sitter等）の使用方針  
**決定**: フレームワークAPIを直接使用し、カスタム抽象化レイヤーを作成しない  
**理由**:
- Article VIII（Anti-Abstraction Gate）に準拠
- フレームワークのベストプラクティスを活用
- メンテナンス負担の軽減

**例外**:
- 複数フレームワーク対応が必要な場合は Phase -1 Gate で承認を得る

**トレーサビリティ**: REQ-ARC-001（Article VIII関連）

---

### ADR-003: 統合テストでのモック制限

**ステータス**: Accepted  
**日付**: 2026-01-01  
**コンテキスト**: 統合テストにおけるモックの使用方針  
**決定**: 実サービスを原則使用し、モックは正当な理由がある場合のみ許可  
**理由**:
- Article IX（Integration-First Testing）に準拠
- 実際のサービス連携の問題を早期発見
- 本番環境との挙動の一致性

**許可されるモック使用**:
- 外部サービスがテスト環境で利用不可
- 使用制限/コストがある
- テスト環境がない

**トレーサビリティ**: REQ-TST-002

---

## 19. 設計検証チェックリスト

### 20.1 憲法準拠チェック

| Article | チェック項目 | 状態 |
|---------|-------------|------|
| I | 全機能がライブラリとして分離されている | ✅ |
| II | 全ライブラリにCLIエントリーポイントがある | ✅ |
| III | テスト駆動開発を前提とした設計 | ✅ |
| IV | 要件がEARS形式で記述されている | ✅ |
| V | 100%トレーサビリティを確保 | ✅ |
| VI | steeringファイルを参照する設計 | ✅ |
| VII | 3プロジェクト以内 | ✅ |
| VIII | フレームワーク直接使用 | ✅ |
| IX | 実サービスでの統合テスト | ✅ |

### 20.2 要件カバレッジ

| カテゴリ | 要件数 | 設計済み | カバレッジ |
|---------|--------|----------|-----------|
| アーキテクチャ | 2 | 2 | 100% |
| 統合レイヤー | 4 | 4 | 100% |
| 要求分析 | 4 | 4 | 100% |
| 設計生成 | 5 | 5 | 100% |
| コード生成 | 6 | 6 | 100% |
| テスト生成 | 2 | 2 | 100% |
| 説明生成 | 3 | 3 | 100% |
| トレーサビリティ | 2 | 2 | 100% |
| エラーリカバリ | 3 | 3 | 100% |
| 品質保証 | 2 | 2 | 100% |
| パフォーマンス | 2 | 2 | 100% |
| セキュリティ | 2 | 2 | 100% |
| 保守性 | 2 | 2 | 100% |
| 国際化 | 1 | 1 | 100% |
| **合計** | **41** | **41** | **100%** |

---

## 20. 次ステップ

1. **タスク分解**: 設計を実装タスクに分解
2. **テスト計画**: テストケース設計
3. **実装**: Article III（Test-First）に従い実装
4. **検証**: トレーサビリティ監査

---

## 21. 承認

| 役割 | 氏名 | 署名 | 日付 |
|------|------|------|------|
| リードアーキテクト | MUSUBIX Team | ✅ | 2026-01-01 |
| テックリード | MUSUBIX Team | ✅ | 2026-01-01 |
| QAリード | MUSUBIX Team | ✅ | 2026-01-01 |

**レビュースコア**: 99%  
**承認理由**: 全41要件100%カバレッジ、9憲法条項100%準拠

---

## 改訂履歴

| バージョン | 日付 | 変更内容 | 作成者 |
|-----------|------|---------|--------|
| 1.0 | 2026-01-01 | 初版作成 | MUSUBIX |
| 1.1 | 2026-01-01 | レビュー反映: 全41要件の設計追加、Test-First設計ガイドライン追加、CLI設計拡充、ADRトレーサビリティ修正 | MUSUBIX |

---

**文書ID**: DES-MUSUBIX-001  
**バージョン**: 1.1  
**最終更新**: 2026-01-01  
**次回レビュー**: 2026-01-08
