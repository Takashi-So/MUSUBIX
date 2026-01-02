/**
 * Explain Command
 *
 * CLI commands for explanation and visualization
 *
 * @packageDocumentation
 * @module cli/commands/explain
 *
 * @see REQ-CLI-006 - Explain CLI
 * @see REQ-EXP-001 - Explanation Generation
 * @see REQ-EXP-002 - Visualization
 * @see DES-MUSUBIX-001 Section 16-C.6 - explainコマンド設計
 * @see TSK-079〜080 - Explain CLI実装
 */

import type { Command } from 'commander';
import { readFile, writeFile, readdir, mkdir } from 'fs/promises';
import { resolve, join, dirname } from 'path';
import { ExitCode, getGlobalOptions, outputResult } from '../base.js';

/**
 * Explain command options
 */
export interface ExplainOptions {
  output?: string;
  format?: 'text' | 'markdown' | 'json' | 'mermaid';
  verbose?: boolean;
  depth?: number;
}

/**
 * Decision factor
 */
export interface DecisionFactor {
  type: 'requirement' | 'constraint' | 'pattern' | 'principle' | 'tradeoff';
  id?: string;
  description: string;
  weight: number;
  source?: string;
}

/**
 * Decision explanation
 */
export interface DecisionExplanation {
  id: string;
  decision: string;
  rationale: string;
  factors: DecisionFactor[];
  alternatives: Array<{
    description: string;
    rejected: string;
  }>;
  confidence: number;
  references: string[];
}

/**
 * Why result
 */
export interface WhyResult {
  success: boolean;
  explanation: DecisionExplanation;
  relatedDecisions: string[];
  message: string;
}

/**
 * Graph node
 */
export interface GraphNode {
  id: string;
  label: string;
  type: 'decision' | 'requirement' | 'design' | 'code' | 'test' | 'factor';
  metadata?: Record<string, string>;
}

/**
 * Graph edge
 */
export interface GraphEdge {
  source: string;
  target: string;
  label: string;
  type: 'implements' | 'derives' | 'supports' | 'constrains' | 'influences';
}

/**
 * Reasoning graph
 */
export interface ReasoningGraph {
  nodes: GraphNode[];
  edges: GraphEdge[];
  rootId: string;
  depth: number;
}

/**
 * Graph result
 */
export interface GraphResult {
  success: boolean;
  graph: ReasoningGraph;
  visualization: string;
  message: string;
}

/**
 * ID patterns
 */
const ID_PATTERNS = {
  requirement: /REQ-[A-Z]+-\d+/,
  design: /DES-[A-Z]+-\d+/,
  task: /TSK-[A-Z]*-?\d+/,
  adr: /ADR-\d+/,
};

/**
 * Register explain command
 */
export function registerExplainCommand(program: Command): void {
  const explain = program
    .command('explain')
    .description('Explanation and visualization');

  // explain why
  explain
    .command('why <id>')
    .description('Explain why a decision was made')
    .option('-f, --format <format>', 'Output format', 'markdown')
    .option('-o, --output <file>', 'Output file')
    .action(async (id: string, options: ExplainOptions) => {
      const globalOpts = getGlobalOptions(program);

      try {
        // Find and analyze the artifact
        const explanation = await analyzeDecision(id);

        const result: WhyResult = {
          success: true,
          explanation,
          relatedDecisions: explanation.references.filter(r => r.match(/^(ADR|DES)-/)),
          message: `Generated explanation for ${id}`,
        };

        // Output
        if (options.output) {
          const outputPath = resolve(process.cwd(), options.output);
          await mkdir(dirname(outputPath), { recursive: true });

          let content: string;
          if (options.format === 'json' || globalOpts.json) {
            content = JSON.stringify(result, null, 2);
          } else {
            content = generateExplanationMarkdown(explanation);
          }

          await writeFile(outputPath, content, 'utf-8');
          if (!globalOpts.quiet) {
            console.log(`✅ Explanation saved to ${outputPath}`);
          }
        } else if (globalOpts.json) {
          outputResult(result, globalOpts);
        } else {
          console.log(generateExplanationText(explanation));
        }

        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Explanation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // explain graph
  explain
    .command('graph <id>')
    .description('Generate reasoning graph')
    .option('-f, --format <format>', 'Output format (mermaid|json)', 'mermaid')
    .option('-o, --output <file>', 'Output file')
    .option('-d, --depth <number>', 'Graph depth', '3')
    .action(async (id: string, options: ExplainOptions) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const depth = options.depth ?? 3;
        const graph = await buildReasoningGraph(id, depth);
        const visualization = options.format === 'json' 
          ? JSON.stringify(graph, null, 2)
          : generateMermaidGraph(graph);

        const result: GraphResult = {
          success: true,
          graph,
          visualization,
          message: `Generated reasoning graph with ${graph.nodes.length} nodes and ${graph.edges.length} edges`,
        };

        // Output
        if (options.output) {
          const outputPath = resolve(process.cwd(), options.output);
          await mkdir(dirname(outputPath), { recursive: true });
          await writeFile(outputPath, visualization, 'utf-8');
          if (!globalOpts.quiet) {
            console.log(`✅ Graph saved to ${outputPath}`);
          }
        } else if (globalOpts.json) {
          outputResult(result, globalOpts);
        } else {
          console.log(visualization);
        }

        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Graph generation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });
}

/**
 * Analyze decision
 */
async function analyzeDecision(id: string): Promise<DecisionExplanation> {
  const specsDir = resolve(process.cwd(), 'storage/specs');
  const adrDir = resolve(process.cwd(), 'docs/adr');

  // Determine type
  let artifactType: 'requirement' | 'design' | 'task' | 'adr' | 'unknown' = 'unknown';
  for (const [type, pattern] of Object.entries(ID_PATTERNS)) {
    if (pattern.test(id)) {
      artifactType = type as typeof artifactType;
      break;
    }
  }

  // Search for the artifact
  let content = '';

  // Search in specs
  try {
    const files = await readdir(specsDir);
    for (const file of files) {
      if (!file.endsWith('.md')) continue;
      const fileContent = await readFile(join(specsDir, file), 'utf-8');
      if (fileContent.includes(id)) {
        content = fileContent;
        break;
      }
    }
  } catch {
    // Specs dir doesn't exist
  }

  // Search in ADR
  if (!content) {
    try {
      const files = await readdir(adrDir);
      for (const file of files) {
        if (!file.endsWith('.md')) continue;
        const fileContent = await readFile(join(adrDir, file), 'utf-8');
        if (fileContent.includes(id)) {
          content = fileContent;
          artifactType = 'adr';
          break;
        }
      }
    } catch {
      // ADR dir doesn't exist
    }
  }

  // Extract information
  const factors: DecisionFactor[] = [];
  const alternatives: DecisionExplanation['alternatives'] = [];
  const references: string[] = [];

  // Find related IDs
  for (const pattern of Object.values(ID_PATTERNS)) {
    const matches = content.match(new RegExp(pattern.source, 'g')) || [];
    for (const match of matches) {
      if (match !== id) {
        references.push(match);
      }
    }
  }

  // Extract factors from content
  if (content.includes('SOLID')) {
    factors.push({
      type: 'principle',
      description: 'SOLID principles compliance',
      weight: 0.8,
      source: 'Architecture guidelines',
    });
  }

  if (content.includes('security') || content.includes('Security')) {
    factors.push({
      type: 'constraint',
      description: 'Security requirements',
      weight: 0.9,
      source: 'Non-functional requirements',
    });
  }

  if (content.includes('performance') || content.includes('Performance')) {
    factors.push({
      type: 'constraint',
      description: 'Performance requirements',
      weight: 0.7,
      source: 'Non-functional requirements',
    });
  }

  // Pattern detection
  const patterns = ['Factory', 'Singleton', 'Observer', 'Strategy', 'Adapter'];
  for (const pattern of patterns) {
    if (content.includes(pattern)) {
      factors.push({
        type: 'pattern',
        description: `${pattern} pattern applied`,
        weight: 0.6,
        source: 'Design patterns catalog',
      });
    }
  }

  // Extract description and rationale
  const titleMatch = content.match(/^#+\s*(.+)$/m);
  const decision = titleMatch?.[1] || id;

  const rationaleMatch = content.match(/(?:Rationale|理由|Why|なぜ)[:\s]*\n([^\n]+)/i);
  const rationale = rationaleMatch?.[1] || 'Decision based on requirements analysis and design principles';

  // Calculate confidence
  const confidence = Math.min(0.95, 0.5 + factors.length * 0.1 + references.length * 0.05);

  return {
    id,
    decision,
    rationale,
    factors,
    alternatives,
    confidence,
    references: [...new Set(references)],
  };
}

/**
 * Build reasoning graph
 */
async function buildReasoningGraph(rootId: string, maxDepth: number): Promise<ReasoningGraph> {
  const nodes: GraphNode[] = [];
  const edges: GraphEdge[] = [];
  const visited = new Set<string>();

  async function traverse(id: string, depth: number): Promise<void> {
    if (depth > maxDepth || visited.has(id)) return;
    visited.add(id);

    // Determine node type
    let nodeType: GraphNode['type'] = 'decision';
    if (id.startsWith('REQ-')) nodeType = 'requirement';
    else if (id.startsWith('DES-')) nodeType = 'design';
    else if (id.startsWith('TSK-')) nodeType = 'code';
    else if (id.startsWith('TEST-')) nodeType = 'test';

    nodes.push({
      id,
      label: id,
      type: nodeType,
    });

    // Find related artifacts
    const explanation = await analyzeDecision(id);
    
    for (const ref of explanation.references) {
      if (!visited.has(ref)) {
        // Determine edge type
        let edgeType: GraphEdge['type'] = 'influences';
        if (ref.startsWith('REQ-')) edgeType = 'derives';
        else if (ref.startsWith('DES-')) edgeType = 'implements';
        else if (ref.startsWith('TSK-')) edgeType = 'implements';

        edges.push({
          source: id,
          target: ref,
          label: edgeType,
          type: edgeType,
        });

        await traverse(ref, depth + 1);
      }
    }

    // Add factors as nodes
    for (const factor of explanation.factors) {
      const factorId = `factor-${nodes.length}`;
      nodes.push({
        id: factorId,
        label: factor.description,
        type: 'factor',
        metadata: {
          weight: factor.weight.toString(),
          source: factor.source || '',
        },
      });
      edges.push({
        source: factorId,
        target: id,
        label: 'supports',
        type: 'supports',
      });
    }
  }

  await traverse(rootId, 0);

  return {
    nodes,
    edges,
    rootId,
    depth: maxDepth,
  };
}

/**
 * Generate Mermaid graph
 */
function generateMermaidGraph(graph: ReasoningGraph): string {
  let output = '```mermaid\nflowchart TB\n';

  // Define node styles
  output += '  classDef requirement fill:#e3f2fd,stroke:#1976d2\n';
  output += '  classDef design fill:#e8f5e9,stroke:#388e3c\n';
  output += '  classDef code fill:#fff3e0,stroke:#f57c00\n';
  output += '  classDef test fill:#fce4ec,stroke:#c2185b\n';
  output += '  classDef factor fill:#f3e5f5,stroke:#7b1fa2\n';
  output += '  classDef decision fill:#fffde7,stroke:#fbc02d\n\n';

  // Add nodes
  for (const node of graph.nodes) {
    const shape = node.type === 'factor' ? '{{' : node.type === 'requirement' ? '([' : '[';
    const closeShape = node.type === 'factor' ? '}}' : node.type === 'requirement' ? '])' : ']';
    const label = node.label.length > 30 ? node.label.slice(0, 30) + '...' : node.label;
    output += `  ${node.id.replace(/-/g, '_')}${shape}"${label}"${closeShape}\n`;
  }

  output += '\n';

  // Add edges
  for (const edge of graph.edges) {
    const sourceId = edge.source.replace(/-/g, '_');
    const targetId = edge.target.replace(/-/g, '_');
    output += `  ${sourceId} -->|${edge.label}| ${targetId}\n`;
  }

  output += '\n';

  // Apply styles
  for (const node of graph.nodes) {
    const nodeId = node.id.replace(/-/g, '_');
    output += `  class ${nodeId} ${node.type}\n`;
  }

  output += '```\n';
  return output;
}

/**
 * Generate explanation markdown
 */
function generateExplanationMarkdown(explanation: DecisionExplanation): string {
  let output = `# Explanation: ${explanation.id}\n\n`;

  output += `## Decision\n\n${explanation.decision}\n\n`;
  output += `## Rationale\n\n${explanation.rationale}\n\n`;

  if (explanation.factors.length > 0) {
    output += `## Contributing Factors\n\n`;
    output += `| Type | Description | Weight | Source |\n`;
    output += `|------|-------------|--------|--------|\n`;
    for (const factor of explanation.factors) {
      output += `| ${factor.type} | ${factor.description} | ${(factor.weight * 100).toFixed(0)}% | ${factor.source || '-'} |\n`;
    }
    output += '\n';
  }

  if (explanation.alternatives.length > 0) {
    output += `## Alternatives Considered\n\n`;
    for (const alt of explanation.alternatives) {
      output += `- **${alt.description}**: Rejected because ${alt.rejected}\n`;
    }
    output += '\n';
  }

  if (explanation.references.length > 0) {
    output += `## References\n\n`;
    for (const ref of explanation.references) {
      output += `- ${ref}\n`;
    }
    output += '\n';
  }

  output += `---\n\n`;
  output += `*Confidence: ${(explanation.confidence * 100).toFixed(0)}%*\n`;
  output += `*Generated: ${new Date().toISOString()}*\n`;

  return output;
}

/**
 * Generate explanation text
 */
function generateExplanationText(explanation: DecisionExplanation): string {
  let output = `\n📋 Explanation for ${explanation.id}\n`;
  output += '═'.repeat(50) + '\n\n';

  output += `📌 Decision: ${explanation.decision}\n\n`;
  output += `💡 Rationale:\n   ${explanation.rationale}\n\n`;

  if (explanation.factors.length > 0) {
    output += `🔍 Contributing Factors:\n`;
    for (const factor of explanation.factors) {
      const bar = '█'.repeat(Math.floor(factor.weight * 10)) + '░'.repeat(10 - Math.floor(factor.weight * 10));
      output += `   • [${factor.type}] ${factor.description}\n`;
      output += `     ${bar} ${(factor.weight * 100).toFixed(0)}%\n`;
    }
    output += '\n';
  }

  if (explanation.references.length > 0) {
    output += `📚 Related:\n`;
    for (const ref of explanation.references) {
      output += `   → ${ref}\n`;
    }
    output += '\n';
  }

  output += `📊 Confidence: ${(explanation.confidence * 100).toFixed(0)}%\n`;

  return output;
}

export {
  analyzeDecision,
  buildReasoningGraph,
  generateMermaidGraph,
  generateExplanationMarkdown,
};
