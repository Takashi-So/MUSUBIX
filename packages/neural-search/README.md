# @nahisaho/musubix-neural-search

Neural search engine with embedding-based scoring and learning-based pruning for MUSUBIX code synthesis.

## Features

- **Neural Scorer**: Embedding-based code and specification scoring
- **Search Engine**: Beam search and best-first search algorithms
- **Learning Module**: Online learning from search trajectories

## Installation

```bash
npm install @nahisaho/musubix-neural-search
```

## Requirements

- REQ-NS-001: Branch Scoring with neural embeddings
- REQ-NS-002: Search prioritization based on scores
- REQ-NS-003: Learning-based pruning
- REQ-NS-004: Search trajectory learning

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                   Neural Search Engine                   │
├─────────────────┬─────────────────┬────────────────────┤
│  Neural Scorer  │  Search Engine  │  Learning Module   │
├─────────────────┼─────────────────┼────────────────────┤
│ EmbeddingModel  │ BeamSearch      │ TrajectoryLog      │
│ BranchScorer    │ BestFirstSearch │ OnlineLearner      │
│ ContextEncoder  │ PruningManager  │ ModelUpdater       │
└─────────────────┴─────────────────┴────────────────────┘
```

## Usage

```typescript
import { BeamSearch, BranchScorer, OnlineLearner } from '@nahisaho/musubix-neural-search';

// Create scorer
const scorer = new BranchScorer();

// Create search
const search = new BeamSearch({ beamWidth: 5 });

// Execute search
const results = await search.search(initialState, scorer);
```

## License

MIT
