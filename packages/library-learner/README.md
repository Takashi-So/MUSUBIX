# @nahisaho/musubix-library-learner

DreamCoder-style hierarchical abstraction and library learning for MUSUBIX.

## Overview

This package provides pattern mining, hierarchical abstraction, type-directed search, and E-graph optimization capabilities for the MUSUBIX neuro-symbolic AI integration system.

## Features

- **Pattern Mining**: Extract recurring patterns from code corpora
- **Hierarchical Abstraction**: Three-level abstraction (concrete → templates → concepts)
- **Type-Directed Search**: Filter and score patterns by type compatibility
- **E-Graph Optimization**: Equality saturation for optimal expression extraction
- **Library Management**: Store, consolidate, and prune learned patterns

## Installation

```bash
npm install @nahisaho/musubix-library-learner
```

## Quick Start

```typescript
import { createLibraryLearner } from '@nahisaho/musubix-library-learner';

// Create a library learner
const learner = createLibraryLearner({
  abstractionLevels: 3,
  minOccurrences: 2,
});

// Learn from a code corpus
const corpus = {
  id: 'my-corpus',
  files: [
    { path: 'file1.ts', content: '...', language: 'typescript' },
    { path: 'file2.ts', content: '...', language: 'typescript' },
  ],
};

const result = await learner.learnFromCorpus(corpus);
console.log(`Extracted ${result.patternsExtracted} patterns`);

// Synthesize using learned patterns
const synthesis = await learner.synthesize({
  type: { kind: 'function', paramTypes: [], returnType: { kind: 'primitive', name: 'number' } },
  description: 'A function that returns a number',
});

if (synthesis.success) {
  console.log('Synthesized program:', synthesis.program);
}
```

## API

### LibraryLearner

High-level API for library learning.

```typescript
interface LibraryLearner {
  learnFromCorpus(corpus: CodeCorpus): Promise<LearnResult>;
  learnIncremental(code: string): Promise<void>;
  synthesize(spec: Specification, options?: SynthesizeOptions): Promise<SynthesisResult>;
  getLibrary(): LibraryStore;
  getStats(): Promise<LibraryStats>;
}
```

### PatternMiner

Extract patterns from code.

```typescript
interface PatternMiner {
  mine(corpus: CodeCorpus): Promise<PatternCandidate[]>;
  setMinOccurrences(count: number): void;
}
```

### Abstractor

Hierarchical abstraction of patterns.

```typescript
interface Abstractor {
  extractConcretePatterns(candidates: PatternCandidate[]): ConcretePattern[];
  parameterize(patterns: ConcretePattern[]): ParameterizedTemplate[];
  generalize(templates: ParameterizedTemplate[]): AbstractConcept[];
}
```

### TypeAnalyzer

Type-directed search and analysis.

```typescript
interface TypeAnalyzer {
  isCompatible(source: TypeSignature, target: TypeSignature): boolean;
  filterByType(candidates: PatternCandidate[], expectedType: TypeSignature): PatternCandidate[];
  scoreByTypeMatch(candidate: PatternCandidate, context: TypeContext): number;
}
```

## Requirements

- REQ-LL-001: 階層的抽象化 (3+ levels)
- REQ-LL-002: ライブラリ成長 (auto-expand)
- REQ-LL-003: 型指向探索 (type-directed search)
- REQ-LL-004: E-graph最適化

## License

MIT
