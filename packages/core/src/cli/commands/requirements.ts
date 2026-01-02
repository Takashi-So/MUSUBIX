/**
 * Requirements Command
 *
 * CLI commands for requirements analysis and validation
 *
 * @packageDocumentation
 * @module cli/commands/requirements
 *
 * @see REQ-CLI-001 - Requirements CLI
 * @see REQ-RA-001 - EARS Pattern Recognition
 * @see REQ-RA-002 - Ontology Mapping
 * @see DES-MUSUBIX-001 Section 16-C.1 - requirementsコマンド設計
 * @see TSK-062〜065 - Requirements CLI実装
 */

import type { Command } from 'commander';
import { readFile, writeFile, access } from 'fs/promises';
import { resolve } from 'path';
import { ExitCode, getGlobalOptions, outputResult } from '../base.js';
import {
  createEARSValidator,
  type EARSPatternMatch,
  type EARSValidatorOptions,
  DEFAULT_EARS_OPTIONS,
} from '../../validators/ears-validator.js';

/**
 * Requirements command options
 */
export interface RequirementsOptions {
  output?: string;
  format?: 'markdown' | 'json' | 'yaml';
  verbose?: boolean;
  ontology?: string;
}

/**
 * EARS requirement
 */
export interface EARSRequirement {
  id: string;
  pattern: string;
  text: string;
  priority: 'P0' | 'P1' | 'P2';
  rationale?: string;
  relatedRequirements?: string[];
}

/**
 * Analysis result
 */
export interface AnalysisResult {
  success: boolean;
  requirements: EARSRequirement[];
  summary: {
    total: number;
    byPattern: Record<string, number>;
    byPriority: Record<string, number>;
  };
  message: string;
}

/**
 * Validation result
 */
export interface ValidationResult {
  success: boolean;
  valid: boolean;
  issues: Array<{
    line?: number;
    requirement?: string;
    severity: 'error' | 'warning' | 'info';
    message: string;
  }>;
  summary: {
    errors: number;
    warnings: number;
    info: number;
  };
  message: string;
}

/**
 * Mapping result
 */
export interface MappingResult {
  success: boolean;
  mappings: Array<{
    requirement: string;
    concepts: string[];
    patterns: string[];
    relatedRequirements: string[];
  }>;
  message: string;
}

/**
 * Search result
 */
export interface SearchResult {
  success: boolean;
  matches: Array<{
    id: string;
    text: string;
    score: number;
    context?: string;
  }>;
  message: string;
}

/**
 * Parse EARS requirements from text
 */
function parseEARSRequirements(content: string): string[] {
  const lines = content.split('\n');
  const requirements: string[] = [];
  let currentReq = '';

  for (const line of lines) {
    const trimmed = line.trim();
    
    // Skip empty lines and comments
    if (!trimmed || trimmed.startsWith('#') || trimmed.startsWith('//')) {
      if (currentReq) {
        requirements.push(currentReq.trim());
        currentReq = '';
      }
      continue;
    }

    // Check for EARS keywords
    if (
      trimmed.match(/^(THE|WHEN|WHILE|IF|WHERE)\s/i) ||
      trimmed.match(/^-\s*(THE|WHEN|WHILE|IF|WHERE)\s/i)
    ) {
      if (currentReq) {
        requirements.push(currentReq.trim());
      }
      currentReq = trimmed.replace(/^-\s*/, '');
    } else if (currentReq && trimmed.match(/^(AND|OR)\s/i)) {
      currentReq += ' ' + trimmed;
    } else if (currentReq) {
      currentReq += ' ' + trimmed;
    }
  }

  if (currentReq) {
    requirements.push(currentReq.trim());
  }

  return requirements;
}

/**
 * Generate requirement ID
 */
function generateReqId(index: number, pattern: string): string {
  const patternPrefix = pattern.substring(0, 3).toUpperCase();
  return `REQ-${patternPrefix}-${String(index + 1).padStart(3, '0')}`;
}

/**
 * Determine priority based on pattern and content
 */
function determinePriority(match: EARSPatternMatch): 'P0' | 'P1' | 'P2' {
  // Security, error handling, core functionality = P0
  const p0Keywords = ['SHALL', 'MUST', 'security', 'error', 'fail', 'critical'];
  const p2Keywords = ['SHOULD', 'MAY', 'optional', 'nice-to-have'];

  const text = match.original.toLowerCase();
  
  if (p0Keywords.some(kw => text.includes(kw.toLowerCase()))) {
    return 'P0';
  }
  if (p2Keywords.some(kw => text.includes(kw.toLowerCase()))) {
    return 'P2';
  }
  return 'P1';
}

/**
 * Register requirements command
 */
export function registerRequirementsCommand(program: Command): void {
  const requirements = program
    .command('requirements')
    .description('Requirements analysis and validation');

  // requirements analyze
  requirements
    .command('analyze <input>')
    .description('Analyze natural language to EARS requirements')
    .option('-o, --output <file>', 'Output file')
    .option('-f, --format <format>', 'Output format (markdown|json|yaml)', 'markdown')
    .action(async (input: string, options: RequirementsOptions) => {
      const globalOpts = getGlobalOptions(program);

      try {
        // Read input
        let content: string;
        const inputPath = resolve(process.cwd(), input);
        
        try {
          await access(inputPath);
          content = await readFile(inputPath, 'utf-8');
        } catch {
          // Treat as direct text input
          content = input;
        }

        // Create validator
        const validator = createEARSValidator();

        // Parse and analyze requirements
        const rawRequirements = parseEARSRequirements(content);
        const requirements: EARSRequirement[] = [];
        const byPattern: Record<string, number> = {};
        const byPriority: Record<string, number> = { P0: 0, P1: 0, P2: 0 };

        for (let i = 0; i < rawRequirements.length; i++) {
          const reqText = rawRequirements[i];
          const match = validator.validateRequirement(reqText);

          if (match.valid && match.patternMatch) {
            const pattern = match.patternMatch.type;
            const priority = determinePriority(match.patternMatch);
            const id = generateReqId(i, pattern);

            requirements.push({
              id,
              pattern,
              text: reqText,
              priority,
              rationale: `Detected ${pattern} pattern with ${Math.round(match.patternMatch.confidence * 100)}% confidence`,
            });

            byPattern[pattern] = (byPattern[pattern] || 0) + 1;
            byPriority[priority]++;
          } else {
            // Non-conforming requirement
            requirements.push({
              id: generateReqId(i, 'UNK'),
              pattern: 'unknown',
              text: reqText,
              priority: 'P1',
              rationale: match.issues.map(i => i.message).join('; '),
            });
            byPattern['unknown'] = (byPattern['unknown'] || 0) + 1;
            byPriority['P1']++;
          }
        }

        const result: AnalysisResult = {
          success: true,
          requirements,
          summary: {
            total: requirements.length,
            byPattern,
            byPriority,
          },
          message: `Analyzed ${requirements.length} requirements`,
        };

        // Output
        if (options.output) {
          const outputPath = resolve(process.cwd(), options.output);
          let outputContent: string;

          if (options.format === 'json' || globalOpts.json) {
            outputContent = JSON.stringify(result, null, 2);
          } else if (options.format === 'yaml') {
            const yaml = await import('yaml');
            outputContent = yaml.stringify(result);
          } else {
            // Markdown format
            outputContent = generateMarkdownOutput(result);
          }

          await writeFile(outputPath, outputContent, 'utf-8');
          if (!globalOpts.quiet) {
            console.log(`✅ Analysis saved to ${outputPath}`);
          }
        } else {
          outputResult(result, globalOpts);
        }

        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Analysis failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // requirements validate
  requirements
    .command('validate <file>')
    .description('Validate EARS syntax')
    .option('--strict', 'Enable strict mode', false)
    .action(async (file: string, options: { strict?: boolean }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const filePath = resolve(process.cwd(), file);
        const content = await readFile(filePath, 'utf-8');

        // Create validator
        const validatorOptions: EARSValidatorOptions = {
          ...DEFAULT_EARS_OPTIONS,
          strictMode: options.strict ?? false,
        };
        const validator = createEARSValidator(validatorOptions);

        // Parse and validate
        const rawRequirements = parseEARSRequirements(content);
        const issues: ValidationResult['issues'] = [];

        for (let i = 0; i < rawRequirements.length; i++) {
          const reqText = rawRequirements[i];
          const result = validator.validateRequirement(reqText);

          for (const issue of result.issues) {
            issues.push({
              line: i + 1,
              requirement: reqText.substring(0, 50) + (reqText.length > 50 ? '...' : ''),
              severity: issue.severity,
              message: issue.message,
            });
          }
        }

        const errors = issues.filter(i => i.severity === 'error').length;
        const warnings = issues.filter(i => i.severity === 'warning').length;
        const info = issues.filter(i => i.severity === 'info').length;

        const result: ValidationResult = {
          success: true,
          valid: errors === 0,
          issues,
          summary: { errors, warnings, info },
          message: errors === 0 
            ? `✅ All ${rawRequirements.length} requirements are valid`
            : `❌ Found ${errors} errors, ${warnings} warnings`,
        };

        outputResult(result, globalOpts);
        process.exit(errors === 0 ? ExitCode.SUCCESS : ExitCode.VALIDATION_ERROR);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Validation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // requirements map
  requirements
    .command('map <file>')
    .description('Map requirements to ontology')
    .option('--ontology <path>', 'Custom ontology file')
    .action(async (file: string, _options: RequirementsOptions) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const filePath = resolve(process.cwd(), file);
        const content = await readFile(filePath, 'utf-8');

        // Parse requirements
        const rawRequirements = parseEARSRequirements(content);
        const validator = createEARSValidator();

        // Map to concepts (simplified implementation)
        const mappings: MappingResult['mappings'] = [];

        for (const reqText of rawRequirements) {
          const result = validator.validateRequirement(reqText);
          
          // Extract concepts from components
          const concepts: string[] = [];
          const patterns: string[] = [];
          
          if (result.patternMatch) {
            const comp = result.patternMatch.components;
            if (comp.system) concepts.push(`Actor:${comp.system}`);
            if (comp.action) concepts.push(`Action:${comp.action}`);
            if (comp.trigger) concepts.push(`Event:${comp.trigger}`);
            if (comp.state) concepts.push(`State:${comp.state}`);
            if (comp.condition) concepts.push(`Condition:${comp.condition}`);
            
            patterns.push(result.patternMatch.type);
          }

          mappings.push({
            requirement: reqText.substring(0, 80) + (reqText.length > 80 ? '...' : ''),
            concepts,
            patterns,
            relatedRequirements: [], // Would need knowledge graph for actual implementation
          });
        }

        const result: MappingResult = {
          success: true,
          mappings,
          message: `Mapped ${mappings.length} requirements to ontology concepts`,
        };

        outputResult(result, globalOpts);
        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Mapping failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // requirements search
  requirements
    .command('search <query>')
    .description('Search related requirements')
    .option('--dir <path>', 'Search directory', 'storage/specs')
    .action(async (query: string, options: { dir?: string }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const searchDir = resolve(process.cwd(), options.dir ?? 'storage/specs');
        
        // Simple search implementation
        const matches: SearchResult['matches'] = [];
        const queryLower = query.toLowerCase();

        try {
          const { readdir } = await import('fs/promises');
          const files = await readdir(searchDir);
          
          for (const file of files) {
            if (!file.endsWith('.md')) continue;
            
            const filePath = resolve(searchDir, file);
            const content = await readFile(filePath, 'utf-8');
            const lines = content.split('\n');

            for (let i = 0; i < lines.length; i++) {
              const line = lines[i];
              if (line.toLowerCase().includes(queryLower)) {
                // Extract requirement ID if present
                const idMatch = line.match(/REQ-[A-Z]+-\d+/);
                
                matches.push({
                  id: idMatch?.[0] ?? `${file}:${i + 1}`,
                  text: line.trim().substring(0, 100),
                  score: calculateMatchScore(line, query),
                  context: lines.slice(Math.max(0, i - 1), i + 2).join('\n'),
                });
              }
            }
          }
        } catch (err) {
          // Directory doesn't exist or is empty
        }

        // Sort by score
        matches.sort((a, b) => b.score - a.score);

        const result: SearchResult = {
          success: true,
          matches: matches.slice(0, 20), // Top 20 matches
          message: `Found ${matches.length} matches for "${query}"`,
        };

        outputResult(result, globalOpts);
        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Search failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });
}

/**
 * Calculate match score
 */
function calculateMatchScore(text: string, query: string): number {
  const textLower = text.toLowerCase();
  const queryLower = query.toLowerCase();
  const queryWords = queryLower.split(/\s+/);
  
  let score = 0;
  
  // Exact match bonus
  if (textLower.includes(queryLower)) {
    score += 1.0;
  }
  
  // Word match bonus
  for (const word of queryWords) {
    if (textLower.includes(word)) {
      score += 0.3;
    }
  }
  
  // EARS keyword bonus
  if (text.match(/\b(SHALL|WHEN|WHILE|IF|THE)\b/i)) {
    score += 0.2;
  }
  
  return Math.min(score, 2.0);
}

/**
 * Generate markdown output
 */
function generateMarkdownOutput(result: AnalysisResult): string {
  let output = '# Requirements Analysis\n\n';
  
  output += '## Summary\n\n';
  output += `- **Total Requirements**: ${result.summary.total}\n`;
  output += '- **By Pattern**:\n';
  for (const [pattern, count] of Object.entries(result.summary.byPattern)) {
    output += `  - ${pattern}: ${count}\n`;
  }
  output += '- **By Priority**:\n';
  for (const [priority, count] of Object.entries(result.summary.byPriority)) {
    output += `  - ${priority}: ${count}\n`;
  }
  
  output += '\n## Requirements\n\n';
  
  for (const req of result.requirements) {
    output += `### ${req.id} (${req.priority})\n\n`;
    output += `**Pattern**: ${req.pattern}\n\n`;
    output += `> ${req.text}\n\n`;
    if (req.rationale) {
      output += `*${req.rationale}*\n\n`;
    }
    output += '---\n\n';
  }
  
  return output;
}

export { parseEARSRequirements };
