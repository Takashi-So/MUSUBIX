# @nahisaho/musubix-synthesis

DSL-based program synthesis with PBE (Programming by Example) and rule learning.

## Features

- **DSL Framework**: Declarative DSL definition with operators, types, and semantics
- **PBE Synthesis**: Programming by Example using enumeration and neural guidance
- **Witness Functions**: Deductive synthesis with inverse semantics
- **Version Space**: Efficient representation of candidate programs
- **Rule Learning**: Meta-learning from successful synthesis

## Installation

```bash
npm install @nahisaho/musubix-synthesis
```

## Usage

### DSL Definition

```typescript
import { DSLBuilder } from '@nahisaho/musubix-synthesis';

const dsl = new DSLBuilder('string-transform')
  .addType('string', { kind: 'primitive' })
  .addType('int', { kind: 'primitive' })
  .addOperator('concat', ['string', 'string'], 'string', (a, b) => a + b)
  .addOperator('substring', ['string', 'int', 'int'], 'string', (s, i, j) => s.slice(i, j))
  .addOperator('length', ['string'], 'int', (s) => s.length)
  .addConstant('empty', 'string', '')
  .build();
```

### PBE Synthesis

```typescript
import { PBESynthesizer } from '@nahisaho/musubix-synthesis';

const synthesizer = new PBESynthesizer();

const result = await synthesizer.synthesize(dsl, [
  { input: 'hello', output: 'HELLO' },
  { input: 'world', output: 'WORLD' },
]);

if (result.success) {
  console.log('Synthesized program:', result.program);
}
```

### Rule Learning

```typescript
import { RuleLibrary, MetaLearner } from '@nahisaho/musubix-synthesis';

const library = new RuleLibrary();
const learner = new MetaLearner(library);

// Learn from successful synthesis
await learner.learn(result, usedRules);

// Apply learned rules for future synthesis
const rules = await library.match(newSpec);
```

## API Reference

### DSL Framework

- `DSLBuilder` - Declarative DSL definition
- `TypeSystem` - Type checking and inference
- `Semantics` - Execution semantics

### Synthesis Engine

- `PBESynthesizer` - Programming by example
- `WitnessEngine` - Deductive synthesis
- `VersionSpace` - Candidate program representation
- `Enumerator` - Exhaustive enumeration

### Rule Learning

- `RuleExtractor` - Extract rules from synthesis
- `RuleLibrary` - Store and query rules
- `MetaLearner` - Continuous rule improvement

## Requirements

| Requirement | Description |
|-------------|-------------|
| REQ-SYN-001 | DSL Definition Framework |
| REQ-SYN-002 | Witness Functions |
| REQ-SYN-003 | PBE Synthesis |
| REQ-SYN-004 | Rule Learning |

## License

MIT
