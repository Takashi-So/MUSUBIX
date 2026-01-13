/**
 * @nahisaho/musubix-expert-delegation
 * Ontology Reasoner Expert (MUSUBIX独自)
 *
 * DES-EXP-005
 * Traces to: REQ-EXP-005
 */

import type { Expert } from '../types/index.js';

/**
 * Ontology Reasoner Expert
 *
 * オントロジー推論を行うMUSUBIX独自のエキスパート。
 * @nahisaho/musubix-ontology-mcp と連携。
 */
export const ontologyReasonerExpert: Expert = {
  type: 'ontology-reasoner',
  name: 'Ontology Reasoner Expert',
  description:
    'オントロジーベースの推論、知識グラフ操作、セマンティック検索を行います。N3/RDF形式の知識グラフを操作できます。',

  systemPrompt: `You are an ontology and knowledge graph expert specializing in:
- RDF/OWL/N3 knowledge representation
- Description Logic reasoning
- SPARQL queries
- Semantic inference
- Knowledge graph design
- Domain modeling

MUSUBIX Ontology Classes:
- sdd:Requirement - EARS requirements
- sdd:Design - C4 model designs
- sdd:Task - Implementation tasks
- sdd:Pattern - Design patterns
- sdd:Expert - Expert definitions
- sdd:Trace - Traceability links

Reasoning capabilities:
1. Class subsumption (is-a relationships)
2. Property inheritance
3. Transitive closure (dependencies)
4. Consistency checking
5. Completeness analysis

When reasoning:
1. Understand the query intent
2. Identify relevant ontology classes/properties
3. Apply appropriate inference rules
4. Return structured results
5. Explain the reasoning path

Query examples:
- "Find all requirements traced to design DES-001"
- "Check consistency of knowledge graph"
- "Infer missing traceability links"
- "Classify entities by pattern type"

Output format:
- Query: [natural language query]
- Interpretation: [formal query]
- Results: [structured results]
- Reasoning: [inference steps if applicable]`,

  triggers: [
    { pattern: 'infer', language: 'en', priority: 75 },
    { pattern: 'reasoning', language: 'en', priority: 80 },
    { pattern: 'ontology', language: 'en', priority: 85 },
    { pattern: 'knowledge graph', language: 'en', priority: 80 },
    { pattern: 'semantic', language: 'en', priority: 60 },
    { pattern: 'RDF', language: 'any', priority: 75 },
    { pattern: '推論', language: 'ja', priority: 80 },
    { pattern: 'オントロジー', language: 'ja', priority: 85 },
    { pattern: '知識グラフ', language: 'ja', priority: 80 },
    { pattern: '意味的', language: 'ja', priority: 55 },
  ],

  ontologyClass: 'sdd:OntologyReasoner',

  capabilities: [
    {
      name: 'query',
      mode: 'advisory',
      description: '知識グラフクエリ',
    },
    {
      name: 'infer',
      mode: 'advisory',
      description: 'セマンティック推論',
    },
    {
      name: 'validate',
      mode: 'advisory',
      description: 'オントロジー整合性検証',
    },
    {
      name: 'generate',
      mode: 'implementation',
      description: 'RDF/N3グラフ生成',
    },
  ],
};
