/**
 * @fileoverview CLI commands for ontology operations
 * @traceability REQ-INT-003
 */

import type { Command } from 'commander';
import { ConsistencyValidator, N3Store } from '@nahisaho/musubix-ontology-mcp';
import type { Triple, ConsistencyViolation } from '@nahisaho/musubix-ontology-mcp';
import * as fs from 'fs';
import * as path from 'path';

/**
 * Parse JSON file with triples
 */
function parseTripleFile(filePath: string): Triple[] {
  const absolutePath = path.resolve(filePath);
  if (!fs.existsSync(absolutePath)) {
    throw new Error(`File not found: ${absolutePath}`);
  }
  
  const content = fs.readFileSync(absolutePath, 'utf-8');
  const data = JSON.parse(content);
  
  if (Array.isArray(data)) {
    return data;
  }
  
  if (data.triples && Array.isArray(data.triples)) {
    return data.triples;
  }
  
  throw new Error('Invalid file format. Expected array of triples or object with "triples" array.');
}

/**
 * Ontology subcommand handlers
 */
const handlers = {
  validate: async (options: Record<string, unknown>) => {
    try {
      const validator = new ConsistencyValidator();
      const store = new N3Store();
      
      let triples: Triple[] = [];
      
      // Load from file or use single triple
      if (options.file) {
        triples = parseTripleFile(options.file as string);
        console.log(`Loaded ${triples.length} triples from ${options.file}`);
      } else if (options.subject && options.predicate && options.object) {
        triples = [{
          subject: options.subject as string,
          predicate: options.predicate as string,
          object: options.object as string,
        }];
      } else {
        console.error('Error: Provide either --file or --subject, --predicate, --object');
        process.exit(1);
      }
      
      // Add triples to store for validation
      for (const t of triples) {
        store.addTriple(t);
      }
      
      // Run validation
      const result = validator.validate(store);
      
      if (options.json) {
        console.log(JSON.stringify(result, null, 2));
      } else {
        console.log('\n╔════════════════════════════════════════╗');
        console.log('║    Ontology Consistency Validation     ║');
        console.log('╚════════════════════════════════════════╝\n');
        
        console.log(`Status: ${result.consistent ? '✅ VALID' : '❌ INVALID'}`);
        console.log(`Total triples: ${triples.length}`);
        console.log(`Errors: ${result.violations.filter((v: ConsistencyViolation) => v.severity === 'error').length}`);
        console.log(`Warnings: ${result.violations.filter((v: ConsistencyViolation) => v.severity === 'warning').length}`);
        
        if (result.violations.length > 0) {
          console.log('\nViolations:');
          for (const v of result.violations) {
            const icon = v.severity === 'error' ? '❌' : v.severity === 'warning' ? '⚠️' : 'ℹ️';
            console.log(`  ${icon} [${v.type}] ${v.message}`);
          }
        }
        
        // Show suggestions if available
        if (result.suggestions && result.suggestions.length > 0) {
          console.log('\nSuggestions:');
          for (const s of result.suggestions) {
            console.log(`  💡 ${s.suggestion}`);
          }
        }
      }
      
      process.exit(result.consistent ? 0 : 1);
    } catch (error) {
      console.error(`Error: ${error instanceof Error ? error.message : error}`);
      process.exit(1);
    }
  },

  checkCircular: async (options: Record<string, unknown>) => {
    try {
      if (!options.file) {
        console.error('Error: --file is required');
        process.exit(1);
      }
      
      const relationships = parseTripleFile(options.file as string);
      
      // Build graph and detect cycles
      const graph = new Map<string, string[]>();
      for (const r of relationships) {
        if (!graph.has(r.subject)) {
          graph.set(r.subject, []);
        }
        graph.get(r.subject)!.push(r.object);
      }
      
      // DFS cycle detection
      const cycles: string[][] = [];
      const visited = new Set<string>();
      const inStack = new Set<string>();
      
      function dfs(node: string, path: string[]): void {
        visited.add(node);
        inStack.add(node);
        
        const neighbors = graph.get(node) || [];
        for (const neighbor of neighbors) {
          if (!visited.has(neighbor)) {
            dfs(neighbor, [...path, node]);
          } else if (inStack.has(neighbor)) {
            cycles.push([...path, node, neighbor]);
          }
        }
        
        inStack.delete(node);
      }
      
      for (const node of graph.keys()) {
        if (!visited.has(node)) {
          dfs(node, []);
        }
      }
      
      if (options.json) {
        console.log(JSON.stringify({ hasCycles: cycles.length > 0, cycles }, null, 2));
      } else {
        console.log('\n╔════════════════════════════════════════╗');
        console.log('║     Circular Dependency Check          ║');
        console.log('╚════════════════════════════════════════╝\n');
        
        if (cycles.length === 0) {
          console.log('✅ No circular dependencies detected.');
        } else {
          console.log(`❌ Found ${cycles.length} cycle(s):\n`);
          for (let i = 0; i < cycles.length; i++) {
            console.log(`  Cycle ${i + 1}: ${cycles[i].join(' → ')}`);
          }
          console.log('\n💡 Remove one relationship from each cycle to break the dependency.');
        }
      }
      
      process.exit(cycles.length === 0 ? 0 : 1);
    } catch (error) {
      console.error(`Error: ${error instanceof Error ? error.message : error}`);
      process.exit(1);
    }
  },

  stats: async (options: Record<string, unknown>) => {
    try {
      if (!options.file) {
        console.error('Error: --file is required');
        process.exit(1);
      }
      
      const triples = parseTripleFile(options.file as string);
      
      // Calculate statistics
      const subjects = new Set(triples.map(t => t.subject));
      const predicates = new Set(triples.map(t => t.predicate));
      const objects = new Set(triples.map(t => t.object));
      const entities = new Set([...subjects, ...objects]);
      
      // Predicate frequency
      const predicateCount = new Map<string, number>();
      for (const t of triples) {
        predicateCount.set(t.predicate, (predicateCount.get(t.predicate) || 0) + 1);
      }
      
      const stats = {
        totalTriples: triples.length,
        uniqueSubjects: subjects.size,
        uniquePredicates: predicates.size,
        uniqueObjects: objects.size,
        uniqueEntities: entities.size,
        predicateDistribution: Object.fromEntries(
          [...predicateCount.entries()].sort((a, b) => b[1] - a[1])
        ),
      };
      
      if (options.json) {
        console.log(JSON.stringify(stats, null, 2));
      } else {
        console.log('\n╔════════════════════════════════════════╗');
        console.log('║       Knowledge Graph Statistics       ║');
        console.log('╚════════════════════════════════════════╝\n');
        
        console.log(`📊 Total Triples:      ${stats.totalTriples}`);
        console.log(`👤 Unique Subjects:    ${stats.uniqueSubjects}`);
        console.log(`🔗 Unique Predicates:  ${stats.uniquePredicates}`);
        console.log(`📦 Unique Objects:     ${stats.uniqueObjects}`);
        console.log(`🔢 Unique Entities:    ${stats.uniqueEntities}`);
        
        console.log('\n📈 Predicate Distribution:');
        const topPredicates = [...predicateCount.entries()]
          .sort((a, b) => b[1] - a[1])
          .slice(0, 10);
        for (const [pred, count] of topPredicates) {
          const bar = '█'.repeat(Math.min(20, Math.round(count / stats.totalTriples * 50)));
          console.log(`  ${pred.padEnd(30)} ${count.toString().padStart(5)} ${bar}`);
        }
      }
    } catch (error) {
      console.error(`Error: ${error instanceof Error ? error.message : error}`);
      process.exit(1);
    }
  },
};

/**
 * Register ontology command with Commander
 */
export function registerOntologyCommand(program: Command): void {
  const ontology = program
    .command('ontology')
    .description('Ontology operations - knowledge graph management and validation');

  // validate subcommand
  ontology
    .command('validate')
    .description('Validate knowledge graph consistency')
    .option('-f, --file <path>', 'JSON file with triples to validate')
    .option('-s, --subject <value>', 'Subject for single triple validation')
    .option('-p, --predicate <value>', 'Predicate for single triple validation')
    .option('-o, --object <value>', 'Object for single triple validation')
    .option('-c, --checks <types>', 'Comma-separated check types')
    .option('--json', 'Output as JSON')
    .action(async (options) => {
      await handlers.validate(options);
    });

  // check-circular subcommand
  ontology
    .command('check-circular')
    .description('Check for circular dependencies')
    .option('-f, --file <path>', 'JSON file with relationships')
    .option('--json', 'Output as JSON')
    .action(async (options) => {
      await handlers.checkCircular(options);
    });

  // stats subcommand
  ontology
    .command('stats')
    .description('Show knowledge graph statistics')
    .option('-f, --file <path>', 'JSON file with triples')
    .option('--json', 'Output as JSON')
    .action(async (options) => {
      await handlers.stats(options);
    });
}
