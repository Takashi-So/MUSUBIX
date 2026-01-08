/**
 * @fileoverview Security Rule Engine
 * @module @nahisaho/musubix-security/rules/engine/rule-engine
 * @trace REQ-RULE-001, REQ-RULE-002, REQ-RULE-004
 */

import * as fs from 'node:fs';
import * as path from 'node:path';
import { Project } from 'ts-morph';
import { minimatch } from 'minimatch';
import type {
  SecurityRule,
  RuleResult,
  RuleFinding,
  RuleConfig,
  RuleSeverity,
} from '../types.js';
import { meetsSeverityThreshold } from '../types.js';
import { RuleRegistry, getGlobalRegistry } from './rule-registry.js';
import { RuleContextBuilder } from './rule-context.js';

/**
 * Rule engine options
 */
export interface RuleEngineOptions {
  /** Rule registry to use */
  registry?: RuleRegistry;
  /** Project root directory */
  projectRoot?: string;
  /** Number of concurrent file processing */
  concurrency?: number;
  /** Progress callback */
  onProgress?: (progress: RuleEngineProgress) => void;
  /** File processed callback */
  onFileProcessed?: (filePath: string, findings: RuleFinding[]) => void;
  /** Abort signal */
  signal?: AbortSignal;
}

/**
 * Progress information
 */
export interface RuleEngineProgress {
  phase: 'init' | 'scanning' | 'analyzing' | 'complete';
  totalFiles: number;
  processedFiles: number;
  totalRules: number;
  currentFile?: string;
  currentRule?: string;
  findingsCount: number;
}

/**
 * Engine run result
 */
export interface RuleEngineResult {
  /** All findings */
  findings: RuleFinding[];
  /** Results by rule */
  resultsByRule: Map<string, RuleResult>;
  /** Results by file */
  resultsByFile: Map<string, RuleFinding[]>;
  /** Files processed */
  filesProcessed: number;
  /** Total execution time in ms */
  executionTimeMs: number;
  /** Errors encountered */
  errors: RuleEngineError[];
  /** Summary statistics */
  summary: RuleEngineSummary;
}

/**
 * Engine error
 */
export interface RuleEngineError {
  type: 'file' | 'rule' | 'system';
  filePath?: string;
  ruleId?: string;
  message: string;
  stack?: string;
}

/**
 * Summary statistics
 */
export interface RuleEngineSummary {
  totalFindings: number;
  bySeverity: Record<RuleSeverity, number>;
  byRule: Record<string, number>;
  byCategory: Record<string, number>;
}

/**
 * Security Rule Engine
 * Main orchestrator for running security rules against source files
 */
export class RuleEngine {
  private registry: RuleRegistry;
  private projectRoot: string;
  private concurrency: number;
  private onProgress?: (progress: RuleEngineProgress) => void;
  private onFileProcessed?: (filePath: string, findings: RuleFinding[]) => void;
  private signal?: AbortSignal;

  constructor(options: RuleEngineOptions = {}) {
    this.registry = options.registry ?? getGlobalRegistry();
    this.projectRoot = options.projectRoot ?? process.cwd();
    this.concurrency = options.concurrency ?? 4;
    this.onProgress = options.onProgress;
    this.onFileProcessed = options.onFileProcessed;
    this.signal = options.signal;
  }

  /**
   * Run rules against files
   */
  async run(config: RuleConfig): Promise<RuleEngineResult> {
    const startTime = Date.now();
    const errors: RuleEngineError[] = [];
    const allFindings: RuleFinding[] = [];
    const resultsByRule = new Map<string, RuleResult>();
    const resultsByFile = new Map<string, RuleFinding[]>();

    // Initialize progress
    this.emitProgress({
      phase: 'init',
      totalFiles: 0,
      processedFiles: 0,
      totalRules: 0,
      findingsCount: 0,
    });

    // Get files to scan
    const files = await this.getFilesToScan(config);
    
    // Get rules to run
    const rules = this.getRulesToRun(config);

    // Create shared Project for better performance
    const project = new Project({
      useInMemoryFileSystem: false,
      skipFileDependencyResolution: true,
    });

    // Process files
    let processedFiles = 0;
    const totalFiles = files.length;
    const totalRules = rules.length;

    // Initialize rule results
    for (const rule of rules) {
      resultsByRule.set(rule.id, {
        ruleId: rule.id,
        ruleName: rule.name,
        findings: [],
        executionTime: 0,
        errors: [],
        success: true,
      });
    }

    // Process files in batches
    for (let i = 0; i < files.length; i += this.concurrency) {
      // Check for abort
      if (this.signal?.aborted) {
        errors.push({
          type: 'system',
          message: 'Execution aborted',
        });
        break;
      }

      const batch = files.slice(i, i + this.concurrency);
      const batchResults = await Promise.all(
        batch.map(file => this.processFile(file, rules, config, project, errors))
      );

      // Collect results
      for (let j = 0; j < batch.length; j++) {
        const filePath = batch[j];
        const fileFindings = batchResults[j];
        
        processedFiles++;
        
        // Store file results
        resultsByFile.set(filePath, fileFindings);
        allFindings.push(...fileFindings);

        // Update rule results
        for (const finding of fileFindings) {
          const ruleResult = resultsByRule.get(finding.ruleId);
          if (ruleResult) {
            ruleResult.findings.push(finding);
          }
        }

        // Emit progress
        this.emitProgress({
          phase: 'analyzing',
          totalFiles,
          processedFiles,
          totalRules,
          currentFile: filePath,
          findingsCount: allFindings.length,
        });

        // Emit file processed
        this.onFileProcessed?.(filePath, fileFindings);
      }
    }

    // Filter findings by severity threshold
    const filteredFindings = allFindings.filter(f =>
      meetsSeverityThreshold(f.severity, config.severityThreshold)
    );

    // Calculate summary
    const summary = this.calculateSummary(filteredFindings, rules);

    // Final progress
    this.emitProgress({
      phase: 'complete',
      totalFiles,
      processedFiles,
      totalRules,
      findingsCount: filteredFindings.length,
    });

    return {
      findings: filteredFindings,
      resultsByRule,
      resultsByFile,
      filesProcessed: processedFiles,
      executionTimeMs: Date.now() - startTime,
      errors,
      summary,
    };
  }

  /**
   * Run rules against a single file
   */
  async runOnFile(
    filePath: string,
    config: RuleConfig
  ): Promise<RuleFinding[]> {
    const rules = this.getRulesToRun(config);
    const errors: RuleEngineError[] = [];
    const project = new Project({
      useInMemoryFileSystem: false,
      skipFileDependencyResolution: true,
    });

    return this.processFile(filePath, rules, config, project, errors);
  }

  /**
   * Run rules against source code string
   */
  async runOnSource(
    sourceCode: string,
    config: RuleConfig,
    fileName: string = 'anonymous.ts'
  ): Promise<RuleFinding[]> {
    const rules = this.getRulesToRun(config);
    const contextBuilder = new RuleContextBuilder()
      .withProjectRoot(this.projectRoot)
      .withConfig(config);

    const context = contextBuilder.buildFromSource(fileName, sourceCode);
    const findings: RuleFinding[] = [];

    for (const rule of rules) {
      try {
        // Check if rule is enabled
        const ruleConfig = config.rules[rule.id];
        if (ruleConfig?.enabled === false) continue;

        // Set current rule in context
        (context as any).setCurrentRule(rule.id);

        // Run rule
        const ruleFindings = await rule.analyze(context);
        findings.push(...ruleFindings);
      } catch (error) {
        // Log error but continue
        console.error(`Error running rule ${rule.id}:`, error);
      }
    }

    return findings;
  }

  /**
   * Process a single file
   */
  private async processFile(
    filePath: string,
    rules: SecurityRule[],
    config: RuleConfig,
    project: Project,
    errors: RuleEngineError[]
  ): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];

    try {
      // Build context
      const contextBuilder = new RuleContextBuilder()
        .withProjectRoot(this.projectRoot)
        .withConfig(config)
        .withProject(project)
        .withTaintAnalysis(config.enableTaintAnalysis)
        .withDFG(config.enableDFG);

      const context = await contextBuilder.build(filePath);

      // Run each rule
      for (const rule of rules) {
        try {
          // Check if rule is enabled
          const ruleConfig = config.rules[rule.id];
          if (ruleConfig?.enabled === false) continue;

          // Check severity threshold
          const ruleSeverity = ruleConfig?.severity ?? rule.defaultSeverity;
          if (!meetsSeverityThreshold(ruleSeverity, config.severityThreshold)) {
            continue;
          }

          // Set current rule in context
          (context as any).setCurrentRule(rule.id);

          // Run rule
          const ruleFindings = await rule.analyze(context);
          
          // Override severity if configured
          if (ruleConfig?.severity) {
            for (const f of ruleFindings) {
              f.severity = ruleConfig.severity;
            }
          }

          findings.push(...ruleFindings);
        } catch (error) {
          errors.push({
            type: 'rule',
            filePath,
            ruleId: rule.id,
            message: error instanceof Error ? error.message : String(error),
            stack: error instanceof Error ? error.stack : undefined,
          });
        }
      }
    } catch (error) {
      errors.push({
        type: 'file',
        filePath,
        message: error instanceof Error ? error.message : String(error),
        stack: error instanceof Error ? error.stack : undefined,
      });
    }

    return findings;
  }

  /**
   * Get files to scan
   */
  private async getFilesToScan(config: RuleConfig): Promise<string[]> {
    const includePatterns = config.include ?? ['**/*.ts', '**/*.tsx', '**/*.js', '**/*.jsx'];
    const excludePatterns = config.exclude ?? ['**/node_modules/**', '**/dist/**'];

    const files: string[] = [];
    
    await this.walkDirectory(this.projectRoot, (filePath) => {
      const relativePath = path.relative(this.projectRoot, filePath);
      
      // Check if matches include patterns
      const matchesInclude = includePatterns.some(pattern => 
        minimatch(relativePath, pattern, { dot: true })
      );
      
      // Check if matches exclude patterns
      const matchesExclude = excludePatterns.some(pattern =>
        minimatch(relativePath, pattern, { dot: true })
      );
      
      if (matchesInclude && !matchesExclude) {
        files.push(filePath);
      }
    });

    return files;
  }

  /**
   * Walk directory recursively
   */
  private async walkDirectory(
    dir: string,
    callback: (filePath: string) => void
  ): Promise<void> {
    try {
      const entries = await fs.promises.readdir(dir, { withFileTypes: true });
      
      for (const entry of entries) {
        const fullPath = path.join(dir, entry.name);
        
        if (entry.isDirectory()) {
          // Skip node_modules and hidden directories
          if (entry.name === 'node_modules' || entry.name.startsWith('.')) {
            continue;
          }
          await this.walkDirectory(fullPath, callback);
        } else if (entry.isFile()) {
          callback(fullPath);
        }
      }
    } catch (error) {
      // Ignore errors (e.g., permission denied)
    }
  }

  /**
   * Get rules to run based on config
   */
  private getRulesToRun(config: RuleConfig): SecurityRule[] {
    // Get all rules
    let rules = this.registry.getAll();

    // Filter by profile if specified
    if (config.profile) {
      const profileRules = this.getProfileRules(config.profile);
      if (profileRules) {
        rules = rules.filter(r => profileRules.includes(r.id));
      }
    }

    // Apply explicit enables/disables
    return rules.filter(rule => {
      const ruleConfig = config.rules[rule.id];
      
      // If explicitly disabled, skip
      if (ruleConfig?.enabled === false) return false;
      
      // If explicitly enabled, include
      if (ruleConfig?.enabled === true) return true;
      
      // Otherwise include (profile or default)
      return true;
    });
  }

  /**
   * Get rules for a profile
   */
  private getProfileRules(profile: string): string[] | null {
    const profiles: Record<string, string[]> = {
      minimal: [
        'owasp-a01', 'owasp-a03', 'owasp-a07',
        'cwe-79', 'cwe-89', 'cwe-287',
      ],
      standard: [
        'owasp-a01', 'owasp-a02', 'owasp-a03', 'owasp-a04', 'owasp-a05',
        'owasp-a06', 'owasp-a07', 'owasp-a08', 'owasp-a09', 'owasp-a10',
        'cwe-20', 'cwe-22', 'cwe-77', 'cwe-78', 'cwe-79', 'cwe-89',
        'cwe-94', 'cwe-119', 'cwe-125', 'cwe-190', 'cwe-200',
        'cwe-287', 'cwe-306', 'cwe-352', 'cwe-434', 'cwe-476',
        'cwe-502', 'cwe-522', 'cwe-611', 'cwe-787', 'cwe-798',
        'cwe-862', 'cwe-863', 'cwe-918', 'cwe-1321',
      ],
      strict: [
        // All rules
      ],
    };

    return profiles[profile] ?? null;
  }

  /**
   * Calculate summary statistics
   */
  private calculateSummary(
    findings: RuleFinding[],
    rules: SecurityRule[]
  ): RuleEngineSummary {
    const bySeverity: Record<RuleSeverity, number> = {
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      info: 0,
    };
    const byRule: Record<string, number> = {};
    const byCategory: Record<string, number> = {};

    for (const finding of findings) {
      // By severity
      bySeverity[finding.severity]++;

      // By rule
      byRule[finding.ruleId] = (byRule[finding.ruleId] ?? 0) + 1;

      // By category
      const rule = rules.find(r => r.id === finding.ruleId);
      if (rule?.owasp) {
        for (const owasp of rule.owasp) {
          byCategory[owasp] = (byCategory[owasp] ?? 0) + 1;
        }
      }
      if (rule?.cwe) {
        for (const cwe of rule.cwe) {
          byCategory[`CWE-${cwe}`] = (byCategory[`CWE-${cwe}`] ?? 0) + 1;
        }
      }
    }

    return {
      totalFindings: findings.length,
      bySeverity,
      byRule,
      byCategory,
    };
  }

  /**
   * Emit progress
   */
  private emitProgress(progress: RuleEngineProgress): void {
    this.onProgress?.(progress);
  }
}

/**
 * Create a rule engine
 */
export function createRuleEngine(options: RuleEngineOptions = {}): RuleEngine {
  return new RuleEngine(options);
}
