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
import { readFile, writeFile, access, mkdir } from 'fs/promises';
import { resolve, join } from 'path';
import { createInterface } from 'readline';
import { ExitCode, getGlobalOptions, outputResult } from '../base.js';
import {
  createEARSValidator,
  type EARSPatternMatch,
  type EARSValidatorOptions,
  DEFAULT_EARS_OPTIONS,
} from '../../validators/ears-validator.js';
import { VERSION } from '../../version.js';

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
 * Supports both English and Japanese EARS format
 */
function parseEARSRequirements(content: string): string[] {
  const lines = content.split('\n');
  const requirements: string[] = [];
  let currentReq = '';
  let inRequirementSection = false;

  // EARS keywords in English and Japanese
  const startKeywords = /^(THE|WHEN|WHILE|IF|WHERE)\s/i;
  const startKeywordsJa = /^(システム|THE\s*システム)/i;
  const bulletStartKeywords = /^[-*]\s*(THE|WHEN|WHILE|IF|WHERE)\s/i;
  const continueKeywords = /^(AND|OR)\s/i;
  const continueKeywordsJa = /^(AND\s+THE|かつ|または)/i;
  
  // Japanese EARS pattern detection
  const jaEarsStart = /^(WHEN|WHILE|IF)\s+.+[,、]$/i;
  const jaEarsSystem = /^THE\s+(システム|system)/i;

  for (let i = 0; i < lines.length; i++) {
    const trimmed = lines[i].trim();
    
    // Skip empty lines, comments, and markdown headers
    if (!trimmed || 
        trimmed.startsWith('#') || 
        trimmed.startsWith('//') ||
        trimmed.startsWith('**') ||
        trimmed.startsWith('|') ||
        trimmed.startsWith('---')) {
      if (currentReq && containsEarsKeyword(currentReq)) {
        requirements.push(normalizeEarsRequirement(currentReq));
        currentReq = '';
      }
      continue;
    }

    // Detect EARS section markers
    if (trimmed.match(/種別|pattern|パターン/i)) {
      inRequirementSection = true;
      continue;
    }

    // Check for EARS start keywords
    if (
      trimmed.match(startKeywords) ||
      trimmed.match(startKeywordsJa) ||
      trimmed.match(bulletStartKeywords) ||
      trimmed.match(jaEarsStart)
    ) {
      // Save previous requirement if exists
      if (currentReq && containsEarsKeyword(currentReq)) {
        requirements.push(normalizeEarsRequirement(currentReq));
      }
      currentReq = trimmed.replace(/^[-*]\s*/, '');
      inRequirementSection = true;
    } 
    // Check for Japanese multi-line EARS (e.g., "THE システム SHALL")
    else if (currentReq && trimmed.match(jaEarsSystem)) {
      currentReq += ' ' + trimmed;
    }
    // Check for continuation keywords (AND, OR, etc.)
    else if (currentReq && (trimmed.match(continueKeywords) || trimmed.match(continueKeywordsJa))) {
      currentReq += ' ' + trimmed;
    }
    // Continue building multi-line requirement
    else if (currentReq && !trimmed.match(/^REQ-|^###|^\*\*/) && inRequirementSection) {
      // Check if this line completes the EARS pattern
      if (trimmed.includes('SHALL') || trimmed.includes('する')) {
        currentReq += ' ' + trimmed;
      }
    }
  }

  // Don't forget the last requirement
  if (currentReq && containsEarsKeyword(currentReq)) {
    requirements.push(normalizeEarsRequirement(currentReq));
  }

  return requirements;
}

/**
 * Check if text contains EARS keywords
 */
function containsEarsKeyword(text: string): boolean {
  return /SHALL|すべきである|しなければならない/i.test(text);
}

/**
 * Normalize EARS requirement text
 * Combines multi-line Japanese EARS into single line
 */
function normalizeEarsRequirement(text: string): string {
  return text
    .replace(/\s+/g, ' ')
    .replace(/[、,]\s+/g, ', ')
    .trim();
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

  // requirements new (interactive)
  requirements
    .command('new <feature>')
    .description('Create new requirements through interactive dialogue')
    .option('-i, --interactive', 'Enable interactive mode (default)', true)
    .option('-o, --output <file>', 'Output file path')
    .option('--no-interactive', 'Skip interactive mode')
    .action(async (feature: string, options: { interactive?: boolean; output?: string }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        if (options.interactive !== false) {
          await runInteractiveHearing(feature, options.output, globalOpts);
        } else {
          // Generate minimal template without interaction
          const outputPath = options.output ?? `storage/specs/REQ-${feature.toUpperCase()}-001.md`;
          await generateMinimalTemplate(feature, outputPath, globalOpts);
        }
        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

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

// ============================================================================
// Interactive Hearing System
// ============================================================================

/**
 * Interactive hearing questions for requirements gathering
 */
interface HearingContext {
  feature: string;
  purpose: string;        // WHY
  targetUser: string;     // WHO
  successState: string;   // WHAT-IF
  constraints: string;    // CONSTRAINT
  successCriteria: string; // SUCCESS CRITERIA
  additionalContext: string[];
}

/**
 * Hearing question definition
 */
interface HearingQuestion {
  id: keyof Omit<HearingContext, 'feature' | 'additionalContext'>;
  questionJa: string;
  questionEn: string;
  required: boolean;
  followUp?: string;
}

/**
 * Predefined hearing questions (1問1答)
 */
const HEARING_QUESTIONS: HearingQuestion[] = [
  {
    id: 'purpose',
    questionJa: 'この機能で解決したい「本当の課題」は何ですか？',
    questionEn: 'What is the TRUE problem you want to solve with this feature?',
    required: true,
    followUp: '具体的なシナリオがあれば教えてください。',
  },
  {
    id: 'targetUser',
    questionJa: 'この機能を最も必要としているのは誰ですか？（ユーザー種別）',
    questionEn: 'Who needs this feature the most? (user type)',
    required: true,
    followUp: 'そのユーザーの技術レベルは？',
  },
  {
    id: 'successState',
    questionJa: 'もしこの機能が完璧に動作したら、何が変わりますか？',
    questionEn: 'If this feature works perfectly, what changes?',
    required: true,
  },
  {
    id: 'constraints',
    questionJa: 'この機能で「絶対にやってはいけないこと」はありますか？',
    questionEn: 'Are there any things this feature must NEVER do?',
    required: true,
    followUp: 'セキュリティやパフォーマンスの制約は？',
  },
  {
    id: 'successCriteria',
    questionJa: 'この機能が「成功した」と言えるのはどんな状態ですか？',
    questionEn: 'What state indicates this feature is "successful"?',
    required: true,
    followUp: '測定可能な指標はありますか？',
  },
];

/**
 * Ask a single question and wait for response
 */
async function askQuestion(rl: ReturnType<typeof createInterface>, question: string): Promise<string> {
  return new Promise((resolve) => {
    rl.question(question, (answer) => {
      resolve(answer.trim());
    });
  });
}

/**
 * Read all input lines from pipe (non-TTY mode)
 */
async function readPipeInput(): Promise<string[]> {
  return new Promise((resolve) => {
    const lines: string[] = [];
    const rl = createInterface({
      input: process.stdin,
      output: process.stdout,
      terminal: false,
    });

    rl.on('line', (line) => {
      lines.push(line.trim());
    });

    rl.on('close', () => {
      resolve(lines);
    });
  });
}

/**
 * Run interactive hearing session
 * Supports both TTY (interactive) and pipe (batch) input
 */
async function runInteractiveHearing(
  feature: string,
  outputPath: string | undefined,
  globalOpts: { json?: boolean; quiet?: boolean; verbose?: boolean }
): Promise<void> {
  const isTTY = process.stdin.isTTY;

  const context: HearingContext = {
    feature,
    purpose: '',
    targetUser: '',
    successState: '',
    constraints: '',
    successCriteria: '',
    additionalContext: [],
  };

  if (!isTTY) {
    // Pipe input mode - read all lines at once
    if (!globalOpts.quiet) {
      console.log('📋 MUSUBIX Requirements - Batch Input Mode');
      console.log(`🎯 Feature: ${feature}\n`);
    }

    const lines = await readPipeInput();
    
    // Map lines to questions (5 main questions + additional)
    HEARING_QUESTIONS.forEach((q, i) => {
      if (lines[i]) {
        context[q.id] = lines[i];
        if (!globalOpts.quiet) {
          console.log(`✓ ${q.id}: ${lines[i]}`);
        }
      }
    });

    // Remaining lines are additional context
    for (let i = HEARING_QUESTIONS.length; i < lines.length; i++) {
      if (lines[i]) {
        context.additionalContext.push(lines[i]);
      }
    }

  } else {
    // TTY mode - interactive questioning
    const rl = createInterface({
      input: process.stdin,
      output: process.stdout,
    });

    console.log('\n' + '═'.repeat(60));
    console.log('📋 MUSUBIX Requirements - Interactive Hearing');
    console.log('═'.repeat(60));
    console.log(`\n🎯 Feature: ${feature}\n`);
    console.log('1問1答で要件を明確化します。');
    console.log('空欄でEnterを押すとスキップします。\n');
    console.log('─'.repeat(60) + '\n');

    try {
      // Ask each question one by one
      for (let i = 0; i < HEARING_QUESTIONS.length; i++) {
        const q = HEARING_QUESTIONS[i];
        const questionNum = `[${i + 1}/${HEARING_QUESTIONS.length}]`;
        
        console.log(`${questionNum} ${q.questionJa}`);
        console.log(`    (${q.questionEn})`);
        
        const answer = await askQuestion(rl, '\n→ あなたの回答: ');
        
        if (answer) {
          context[q.id] = answer;
          console.log(`✓ 記録しました\n`);
          
          // Ask follow-up if provided and answer was given
          if (q.followUp) {
            console.log(`   補足質問: ${q.followUp}`);
            const followUpAnswer = await askQuestion(rl, '   → (任意): ');
            if (followUpAnswer) {
              context.additionalContext.push(`${q.id}: ${followUpAnswer}`);
            }
          }
        } else if (q.required) {
          console.log('⚠️  この質問は重要ですが、後で追記できます。\n');
        }
        
        console.log('');
      }

      // Ask for additional requirements
      console.log('─'.repeat(60));
      console.log('\n追加の要件や考慮事項はありますか？（完了するには空欄でEnter）\n');
      
      let additionalCount = 1;
      while (true) {
        const additional = await askQuestion(rl, `追加要件 ${additionalCount}: `);
        if (!additional) break;
        context.additionalContext.push(additional);
        additionalCount++;
      }

      rl.close();
    } catch (error) {
      rl.close();
      throw error;
    }
  }

  // Generate EARS requirements from context
  if (!globalOpts.quiet) {
    console.log('\n' + '═'.repeat(60));
    console.log('📝 EARS要件を生成中...');
    console.log('═'.repeat(60) + '\n');
  }

  const requirements = generateEARSFromContext(context);
  const document = generateRequirementsDocument(context, requirements);

  // Determine output path
  const finalOutputPath = outputPath ?? join('storage', 'specs', `REQ-${feature.toUpperCase()}-001.md`);
  const fullPath = resolve(process.cwd(), finalOutputPath);

  // Ensure directory exists
  const dir = resolve(fullPath, '..');
  await mkdir(dir, { recursive: true });

  // Write document
  await writeFile(fullPath, document, 'utf-8');

  console.log(`✅ 要件ドキュメントを生成しました: ${finalOutputPath}`);
  console.log(`\n生成された要件数: ${requirements.length}\n`);

  // Show preview
  if (!globalOpts.quiet) {
    console.log('─'.repeat(60));
    console.log('📄 プレビュー:\n');
    console.log(requirements.map((r, i) => `  ${i + 1}. ${r.text.substring(0, 70)}...`).join('\n'));
    console.log('\n' + '─'.repeat(60));
  }

  // Automatic requirements review (Article IV & IX compliance)
  console.log('\n' + '═'.repeat(60));
  console.log('🔍 要件レビューを実行中...');
  console.log('═'.repeat(60) + '\n');

  const reviewResult = await reviewRequirements(requirements, context);
  displayReviewResult(reviewResult, globalOpts.quiet ?? false);

  // Save review result
  const reviewPath = finalOutputPath.replace('.md', '-REVIEW.md');
  await writeFile(resolve(process.cwd(), reviewPath), generateReviewDocument(reviewResult), 'utf-8');
  console.log(`📋 レビュー結果を保存しました: ${reviewPath}`);

  if (globalOpts.json) {
    outputResult({
      success: true,
      outputPath: finalOutputPath,
      requirements: requirements.length,
      context,
      review: reviewResult,
    }, globalOpts);
  }
}

/**
 * Generate EARS requirements from hearing context
 */
function generateEARSFromContext(context: HearingContext): EARSRequirement[] {
  const requirements: EARSRequirement[] = [];
  const feature = context.feature.toLowerCase();
  let reqIndex = 1;

  const genId = () => `REQ-${context.feature.toUpperCase()}-${String(reqIndex++).padStart(3, '0')}`;

  // Generate from purpose (WHY) - Core functionality
  if (context.purpose) {
    requirements.push({
      id: genId(),
      pattern: 'ubiquitous',
      text: `The system SHALL provide ${feature} functionality to ${context.purpose}`,
      priority: 'P0',
      rationale: `Core purpose: ${context.purpose}`,
    });
  }

  // Generate from target user (WHO) - User-centric requirements
  if (context.targetUser) {
    requirements.push({
      id: genId(),
      pattern: 'event-driven',
      text: `WHEN ${context.targetUser} accesses the ${feature}, the system SHALL respond within acceptable time`,
      priority: 'P1',
      rationale: `Target user: ${context.targetUser}`,
    });
  }

  // Generate from success state (WHAT-IF) - Expected outcomes
  if (context.successState) {
    requirements.push({
      id: genId(),
      pattern: 'state-driven',
      text: `WHILE the ${feature} is active, the system SHALL maintain ${context.successState}`,
      priority: 'P1',
      rationale: `Success state: ${context.successState}`,
    });
  }

  // Generate from constraints - Unwanted behaviors
  if (context.constraints) {
    const constraints = context.constraints.split(/[,、。]/);
    for (const constraint of constraints) {
      if (constraint.trim()) {
        requirements.push({
          id: genId(),
          pattern: 'unwanted',
          text: `IF ${constraint.trim()}, THEN the system SHALL prevent this behavior and notify the user`,
          priority: 'P0',
          rationale: `Constraint: ${constraint.trim()}`,
        });
      }
    }
  }

  // Generate from success criteria - Validation requirements
  if (context.successCriteria) {
    requirements.push({
      id: genId(),
      pattern: 'ubiquitous',
      text: `The system SHALL meet the following success criteria for ${feature}: ${context.successCriteria}`,
      priority: 'P1',
      rationale: `Success criteria: ${context.successCriteria}`,
    });
  }

  // Generate from additional context
  for (const additional of context.additionalContext) {
    if (additional && !additional.includes(':')) {
      requirements.push({
        id: genId(),
        pattern: 'optional',
        text: `WHERE applicable, the system SHALL ${additional}`,
        priority: 'P2',
        rationale: 'Additional requirement from hearing',
      });
    }
  }

  return requirements;
}

/**
 * Generate requirements document in Markdown format
 */
function generateRequirementsDocument(context: HearingContext, requirements: EARSRequirement[]): string {
  const now = new Date().toISOString().split('T')[0];
  
  let doc = `# REQ-${context.feature.toUpperCase()}-001: ${context.feature} Requirements

> Generated by MUSUBIX Interactive Hearing v${VERSION}
> Date: ${now}

## 1. Overview

### 1.1 Feature
**${context.feature}**

### 1.2 Purpose (WHY)
${context.purpose || '_Not specified_'}

### 1.3 Target User (WHO)
${context.targetUser || '_Not specified_'}

### 1.4 Success State (WHAT-IF)
${context.successState || '_Not specified_'}

### 1.5 Constraints
${context.constraints || '_Not specified_'}

### 1.6 Success Criteria
${context.successCriteria || '_Not specified_'}

---

## 2. EARS Requirements

| ID | Pattern | Priority | Requirement |
|----|---------|----------|-------------|
${requirements.map(r => `| ${r.id} | ${r.pattern} | ${r.priority} | ${r.text.substring(0, 60)}... |`).join('\n')}

---

## 3. Detailed Requirements

`;

  for (const req of requirements) {
    doc += `### ${req.id}

**Pattern**: ${req.pattern}  
**Priority**: ${req.priority}

> ${req.text}

*Rationale*: ${req.rationale}

---

`;
  }

  doc += `## 4. Additional Context

${context.additionalContext.length > 0 ? context.additionalContext.map(c => `- ${c}`).join('\n') : '_No additional context_'}

---

## 5. Traceability

| Requirement | Design | Test |
|-------------|--------|------|
${requirements.map(r => `| ${r.id} | DES-${context.feature.toUpperCase()}-??? | TST-${context.feature.toUpperCase()}-??? |`).join('\n')}

---

**Generated by**: MUSUBIX v${VERSION}  
**Hearing Date**: ${now}
`;

  return doc;
}

/**
 * Generate minimal template without interaction
 */
async function generateMinimalTemplate(
  feature: string,
  outputPath: string,
  globalOpts: { quiet?: boolean }
): Promise<void> {
  const now = new Date().toISOString().split('T')[0];
  const fullPath = resolve(process.cwd(), outputPath);
  
  const template = `# REQ-${feature.toUpperCase()}-001: ${feature} Requirements

> Generated by MUSUBIX v${VERSION}
> Date: ${now}

## 1. Overview

### 1.1 Feature
**${feature}**

### 1.2 Purpose (WHY)
_TODO: Define the purpose_

### 1.3 Target User (WHO)
_TODO: Define target users_

### 1.4 Success Criteria
_TODO: Define success criteria_

---

## 2. EARS Requirements

### REQ-${feature.toUpperCase()}-001 (P0)

**Pattern**: ubiquitous

> The system SHALL [TODO: define core functionality]

---

### REQ-${feature.toUpperCase()}-002 (P1)

**Pattern**: event-driven

> WHEN [TODO: trigger event], the system SHALL [TODO: define response]

---

### REQ-${feature.toUpperCase()}-003 (P1)

**Pattern**: state-driven

> WHILE [TODO: state condition], the system SHALL [TODO: define behavior]

---

## 3. Traceability

| Requirement | Design | Test |
|-------------|--------|------|
| REQ-${feature.toUpperCase()}-001 | DES-${feature.toUpperCase()}-??? | TST-${feature.toUpperCase()}-??? |

---

**Generated by**: MUSUBIX v${VERSION}
`;

  const dir = resolve(fullPath, '..');
  await mkdir(dir, { recursive: true });
  await writeFile(fullPath, template, 'utf-8');

  if (!globalOpts.quiet) {
    console.log(`✅ Template created: ${outputPath}`);
  }
}

// ============================================================================
// Requirements Review System (Article IV & IX Compliance)
// ============================================================================

/**
 * Requirements review result
 */
interface RequirementsReviewResult {
  passed: boolean;
  score: number;
  totalChecks: number;
  passedChecks: number;
  findings: ReviewFinding[];
  recommendations: string[];
  constitutionCompliance: {
    articleIV: boolean;  // EARS Format
    articleV: boolean;   // Traceability
    articleIX: boolean;  // Quality Gates
  };
}

/**
 * Review finding
 */
interface ReviewFinding {
  severity: 'error' | 'warning' | 'info';
  category: 'ears' | 'completeness' | 'testability' | 'consistency' | 'traceability';
  requirement?: string;
  message: string;
  suggestion?: string;
}

/**
 * EARS pattern keywords for validation
 */
const EARS_KEYWORDS = {
  ubiquitous: ['SHALL', 'system'],
  'event-driven': ['WHEN', 'SHALL'],
  'state-driven': ['WHILE', 'SHALL'],
  unwanted: ['SHALL NOT', 'IF', 'THEN'],
  optional: ['IF', 'THEN', 'SHALL'],
};

/**
 * Review requirements for quality and completeness
 */
async function reviewRequirements(
  requirements: EARSRequirement[],
  context: HearingContext
): Promise<RequirementsReviewResult> {
  const findings: ReviewFinding[] = [];
  const recommendations: string[] = [];
  let passedChecks = 0;
  let totalChecks = 0;

  // 1. Check EARS format compliance (Article IV)
  totalChecks++;
  let earsCompliant = true;
  for (const req of requirements) {
    const keywords = EARS_KEYWORDS[req.pattern as keyof typeof EARS_KEYWORDS];
    if (keywords) {
      const hasKeywords = keywords.every(kw => req.text.toUpperCase().includes(kw.toUpperCase()));
      if (!hasKeywords) {
        earsCompliant = false;
        findings.push({
          severity: 'error',
          category: 'ears',
          requirement: req.id,
          message: `EARS pattern '${req.pattern}' requires keywords: ${keywords.join(', ')}`,
          suggestion: `Rewrite requirement to include: ${keywords.join(', ')}`,
        });
      }
    }
  }
  if (earsCompliant) passedChecks++;

  // 2. Check completeness (all 5Ws covered)
  totalChecks++;
  const completenessIssues: string[] = [];
  if (!context.purpose) completenessIssues.push('WHY (purpose)');
  if (!context.targetUser) completenessIssues.push('WHO (target user)');
  if (!context.successState) completenessIssues.push('WHAT-IF (success state)');
  if (!context.constraints) completenessIssues.push('CONSTRAINTS');
  if (!context.successCriteria) completenessIssues.push('SUCCESS CRITERIA');

  if (completenessIssues.length > 0) {
    findings.push({
      severity: completenessIssues.length > 2 ? 'error' : 'warning',
      category: 'completeness',
      message: `Missing context: ${completenessIssues.join(', ')}`,
      suggestion: 'Run interactive hearing again to fill missing information',
    });
  } else {
    passedChecks++;
  }

  // 3. Check testability
  totalChecks++;
  let allTestable = true;
  for (const req of requirements) {
    const hasVagueTerms = /always|never|all|any|best|optimal|fast|slow|many|few/i.test(req.text);
    if (hasVagueTerms) {
      allTestable = false;
      findings.push({
        severity: 'warning',
        category: 'testability',
        requirement: req.id,
        message: 'Contains vague terms that may not be testable',
        suggestion: 'Replace vague terms with specific, measurable criteria',
      });
    }
  }
  if (allTestable) passedChecks++;

  // 4. Check priority distribution
  totalChecks++;
  const priorityCounts = {
    P0: requirements.filter(r => r.priority === 'P0').length,
    P1: requirements.filter(r => r.priority === 'P1').length,
    P2: requirements.filter(r => r.priority === 'P2').length,
  };

  if (priorityCounts.P0 === 0) {
    findings.push({
      severity: 'error',
      category: 'completeness',
      message: 'No P0 (must-have) requirements defined',
      suggestion: 'Ensure at least one core requirement is marked as P0',
    });
  } else if (priorityCounts.P0 > requirements.length * 0.5) {
    findings.push({
      severity: 'warning',
      category: 'consistency',
      message: `Too many P0 requirements (${priorityCounts.P0}/${requirements.length})`,
      suggestion: 'Review priorities - not everything can be must-have',
    });
  } else {
    passedChecks++;
  }

  // 5. Check minimum requirements count
  totalChecks++;
  if (requirements.length < 3) {
    findings.push({
      severity: 'warning',
      category: 'completeness',
      message: `Only ${requirements.length} requirements defined`,
      suggestion: 'Consider if more requirements are needed for complete coverage',
    });
  } else {
    passedChecks++;
  }

  // 6. Check for unique IDs
  totalChecks++;
  const ids = requirements.map(r => r.id);
  const duplicateIds = ids.filter((id, i) => ids.indexOf(id) !== i);
  if (duplicateIds.length > 0) {
    findings.push({
      severity: 'error',
      category: 'consistency',
      requirement: duplicateIds[0],
      message: `Duplicate requirement ID: ${duplicateIds[0]}`,
      suggestion: 'Ensure all requirement IDs are unique',
    });
  } else {
    passedChecks++;
  }

  // Generate recommendations
  if (findings.filter(f => f.severity === 'error').length > 0) {
    recommendations.push('⚠️ Address error-level findings before proceeding to design');
  }
  if (findings.filter(f => f.category === 'testability').length > 0) {
    recommendations.push('📝 Make requirements more specific and measurable');
  }
  if (completenessIssues.length > 0) {
    recommendations.push('🔄 Re-run interactive hearing to complete missing context');
  }
  if (requirements.length >= 3 && findings.filter(f => f.severity === 'error').length === 0) {
    recommendations.push('✅ Requirements are ready for design phase');
  }

  const score = totalChecks > 0 ? Math.round((passedChecks / totalChecks) * 100) : 0;

  return {
    passed: findings.filter(f => f.severity === 'error').length === 0,
    score,
    totalChecks,
    passedChecks,
    findings,
    recommendations,
    constitutionCompliance: {
      articleIV: earsCompliant,
      articleV: true, // Traceability section is generated
      articleIX: score >= 60,
    },
  };
}

/**
 * Display review result
 */
function displayReviewResult(result: RequirementsReviewResult, quiet: boolean): void {
  if (quiet) return;

  const statusIcon = result.passed ? '✅' : '❌';
  console.log(`${statusIcon} レビュー結果: ${result.score}% (${result.passedChecks}/${result.totalChecks} checks)`);
  console.log('');

  // Constitution compliance
  console.log('📜 憲法準拠状況:');
  console.log(`   Article IV (EARS形式): ${result.constitutionCompliance.articleIV ? '✓' : '✗'}`);
  console.log(`   Article V (トレーサビリティ): ${result.constitutionCompliance.articleV ? '✓' : '✗'}`);
  console.log(`   Article IX (品質ゲート): ${result.constitutionCompliance.articleIX ? '✓' : '✗'}`);
  console.log('');

  // Findings
  if (result.findings.length > 0) {
    console.log('📋 発見事項:');
    for (const finding of result.findings) {
      const icon = finding.severity === 'error' ? '🔴' : finding.severity === 'warning' ? '🟡' : '🔵';
      console.log(`   ${icon} [${finding.category}] ${finding.message}`);
      if (finding.requirement) {
        console.log(`      対象: ${finding.requirement}`);
      }
      if (finding.suggestion) {
        console.log(`      💡 ${finding.suggestion}`);
      }
    }
    console.log('');
  }

  // Recommendations
  if (result.recommendations.length > 0) {
    console.log('💡 推奨事項:');
    for (const rec of result.recommendations) {
      console.log(`   ${rec}`);
    }
    console.log('');
  }
}

/**
 * Generate review document
 */
function generateReviewDocument(result: RequirementsReviewResult): string {
  const now = new Date().toISOString().split('T')[0];

  let doc = `# Requirements Review Report

> Generated by MUSUBIX v${VERSION}
> Date: ${now}

## Summary

| Metric | Value |
|--------|-------|
| **Status** | ${result.passed ? '✅ PASSED' : '❌ FAILED'} |
| **Score** | ${result.score}% |
| **Checks Passed** | ${result.passedChecks}/${result.totalChecks} |

## Constitution Compliance

| Article | Name | Status |
|---------|------|--------|
| IV | EARS Format | ${result.constitutionCompliance.articleIV ? '✅ Compliant' : '❌ Non-compliant'} |
| V | Traceability | ${result.constitutionCompliance.articleV ? '✅ Compliant' : '❌ Non-compliant'} |
| IX | Quality Gates | ${result.constitutionCompliance.articleIX ? '✅ Compliant' : '❌ Non-compliant'} |

## Findings

`;

  if (result.findings.length === 0) {
    doc += '_No issues found._\n\n';
  } else {
    const errors = result.findings.filter(f => f.severity === 'error');
    const warnings = result.findings.filter(f => f.severity === 'warning');
    const infos = result.findings.filter(f => f.severity === 'info');

    if (errors.length > 0) {
      doc += '### 🔴 Errors\n\n';
      for (const f of errors) {
        doc += `- **[${f.category}]** ${f.message}\n`;
        if (f.requirement) doc += `  - Requirement: ${f.requirement}\n`;
        if (f.suggestion) doc += `  - 💡 ${f.suggestion}\n`;
      }
      doc += '\n';
    }

    if (warnings.length > 0) {
      doc += '### 🟡 Warnings\n\n';
      for (const f of warnings) {
        doc += `- **[${f.category}]** ${f.message}\n`;
        if (f.requirement) doc += `  - Requirement: ${f.requirement}\n`;
        if (f.suggestion) doc += `  - 💡 ${f.suggestion}\n`;
      }
      doc += '\n';
    }

    if (infos.length > 0) {
      doc += '### 🔵 Info\n\n';
      for (const f of infos) {
        doc += `- **[${f.category}]** ${f.message}\n`;
      }
      doc += '\n';
    }
  }

  doc += `## Recommendations

`;
  for (const rec of result.recommendations) {
    doc += `- ${rec}\n`;
  }

  doc += `
---

**Reviewed by**: MUSUBIX Automated Review System
**Review Date**: ${now}
`;

  return doc;
}

export { parseEARSRequirements };
