#!/usr/bin/env node
/**
 * MUSUBIX DFG CLI
 * Data Flow Graph and Control Flow Graph analysis
 * 
 * @packageDocumentation
 */

import { program } from 'commander';
import { createDFGAnalyzer, createCFGAnalyzer } from '../dist/index.js';
import { readFileSync, writeFileSync } from 'fs';
import { resolve } from 'path';

const VERSION = '3.4.6';

program
  .name('musubix-dfg')
  .description('MUSUBIX Data Flow Graph and Control Flow Graph analysis')
  .version(VERSION);

program
  .command('analyze')
  .description('Analyze code and generate DFG/CFG')
  .argument('<file>', 'Source file to analyze')
  .option('-t, --type <type>', 'Analysis type (dfg|cfg|both)', 'both')
  .option('-o, --output <file>', 'Output file (default: stdout)')
  .option('-f, --format <format>', 'Output format (json|dot|mermaid)', 'json')
  .action(async (file, options) => {
    try {
      const filePath = resolve(process.cwd(), file);
      const code = readFileSync(filePath, 'utf-8');
      
      const results = {};
      
      if (options.type === 'dfg' || options.type === 'both') {
        const dfgAnalyzer = createDFGAnalyzer();
        results.dfg = await dfgAnalyzer.analyze(code, { filePath });
      }
      
      if (options.type === 'cfg' || options.type === 'both') {
        const cfgAnalyzer = createCFGAnalyzer();
        results.cfg = await cfgAnalyzer.analyze(code, { filePath });
      }
      
      let output;
      switch (options.format) {
        case 'json':
          output = JSON.stringify(results, null, 2);
          break;
        case 'dot':
          output = formatAsDot(results);
          break;
        case 'mermaid':
          output = formatAsMermaid(results);
          break;
        default:
          output = JSON.stringify(results, null, 2);
      }
      
      if (options.output) {
        writeFileSync(options.output, output);
        console.log(`Output written to ${options.output}`);
      } else {
        console.log(output);
      }
    } catch (error) {
      console.error(`Error: ${error.message}`);
      process.exit(1);
    }
  });

program
  .command('dependencies')
  .description('Extract variable dependencies from code')
  .argument('<file>', 'Source file to analyze')
  .option('-v, --variable <name>', 'Focus on specific variable')
  .action(async (file, options) => {
    try {
      const filePath = resolve(process.cwd(), file);
      const code = readFileSync(filePath, 'utf-8');
      
      const dfgAnalyzer = createDFGAnalyzer();
      const dfg = await dfgAnalyzer.analyze(code, { filePath });
      
      if (options.variable) {
        const deps = dfg.getDependencies(options.variable);
        console.log(`Dependencies for '${options.variable}':`);
        deps.forEach(dep => console.log(`  - ${dep}`));
      } else {
        console.log('All dependencies:');
        console.log(JSON.stringify(dfg.getAllDependencies(), null, 2));
      }
    } catch (error) {
      console.error(`Error: ${error.message}`);
      process.exit(1);
    }
  });

function formatAsDot(results) {
  const lines = ['digraph G {'];
  
  if (results.dfg) {
    lines.push('  subgraph cluster_dfg {');
    lines.push('    label = "Data Flow Graph";');
    results.dfg.nodes?.forEach(node => {
      lines.push(`    "${node.id}" [label="${node.label || node.id}"];`);
    });
    results.dfg.edges?.forEach(edge => {
      lines.push(`    "${edge.source}" -> "${edge.target}";`);
    });
    lines.push('  }');
  }
  
  if (results.cfg) {
    lines.push('  subgraph cluster_cfg {');
    lines.push('    label = "Control Flow Graph";');
    results.cfg.nodes?.forEach(node => {
      lines.push(`    "${node.id}" [label="${node.label || node.id}"];`);
    });
    results.cfg.edges?.forEach(edge => {
      lines.push(`    "${edge.source}" -> "${edge.target}";`);
    });
    lines.push('  }');
  }
  
  lines.push('}');
  return lines.join('\n');
}

function formatAsMermaid(results) {
  const lines = ['flowchart TD'];
  
  if (results.dfg) {
    lines.push('  subgraph DFG["Data Flow Graph"]');
    results.dfg.nodes?.forEach(node => {
      lines.push(`    ${node.id}["${node.label || node.id}"]`);
    });
    results.dfg.edges?.forEach(edge => {
      lines.push(`    ${edge.source} --> ${edge.target}`);
    });
    lines.push('  end');
  }
  
  if (results.cfg) {
    lines.push('  subgraph CFG["Control Flow Graph"]');
    results.cfg.nodes?.forEach(node => {
      lines.push(`    ${node.id}["${node.label || node.id}"]`);
    });
    results.cfg.edges?.forEach(edge => {
      lines.push(`    ${edge.source} --> ${edge.target}`);
    });
    lines.push('  end');
  }
  
  return lines.join('\n');
}

program.parse();
