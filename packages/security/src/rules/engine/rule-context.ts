/**
 * @fileoverview Rule Context Builder
 * @module @nahisaho/musubix-security/rules/engine/rule-context
 * @trace REQ-RULE-003
 */

import { Project, SourceFile } from 'ts-morph';
import * as fs from 'node:fs';
import * as path from 'node:path';
import * as crypto from 'node:crypto';
import type {
  RuleContext,
  RuleConfig,
  RuleFinding,
  RuleResult,
} from '../types.js';

/**
 * Options for building rule context
 */
export interface RuleContextBuildOptions {
  /** Project root directory */
  projectRoot?: string;
  /** Rule configuration */
  config?: Partial<RuleConfig>;
  /** Previous rule results */
  previousResults?: Map<string, RuleResult>;
  /** Existing ts-morph Project */
  project?: Project;
}

/**
 * Internal context implementation
 */
class RuleContextImpl implements RuleContext {
  filePath: string;
  sourceCode: string;
  sourceFile: SourceFile;
  projectRoot: string;
  config: RuleConfig;
  previousResults: Map<string, RuleResult>;

  private currentRuleId: string = '';
  private findings: RuleFinding[] = [];

  constructor(
    filePath: string,
    sourceCode: string,
    sourceFile: SourceFile,
    projectRoot: string,
    config: RuleConfig,
    previousResults: Map<string, RuleResult>
  ) {
    this.filePath = filePath;
    this.sourceCode = sourceCode;
    this.sourceFile = sourceFile;
    this.projectRoot = projectRoot;
    this.config = config;
    this.previousResults = previousResults;
  }

  /**
   * Set current rule ID (called by engine before rule execution)
   */
  setCurrentRule(ruleId: string): void {
    this.currentRuleId = ruleId;
    this.findings = [];
  }

  /**
   * Get collected findings
   */
  getFindings(): RuleFinding[] {
    return this.findings;
  }

  /**
   * Report a finding
   */
  report(finding: Omit<RuleFinding, 'id' | 'ruleId'>): void {
    this.findings.push({
      ...finding,
      id: crypto.randomUUID(),
      ruleId: this.currentRuleId,
    });
  }

  /**
   * Get option value for current rule
   */
  getOption<T>(key: string, defaultValue: T): T {
    const ruleSettings = this.config.rules[this.currentRuleId];
    if (ruleSettings?.options && key in ruleSettings.options) {
      return ruleSettings.options[key] as T;
    }
    return defaultValue;
  }
}

/**
 * Rule Context Builder
 * Builds context for rule execution
 */
export class RuleContextBuilder {
  private projectRoot: string = process.cwd();
  private config: RuleConfig;
  private previousResults: Map<string, RuleResult> = new Map();
  private project: Project | null = null;

  constructor() {
    // Import DEFAULT_RULE_CONFIG dynamically to avoid circular dependency
    this.config = {
      profile: 'standard',
      rules: {},
      exclude: ['**/node_modules/**', '**/dist/**', '**/*.test.ts', '**/*.spec.ts'],
      include: ['**/*.ts', '**/*.tsx', '**/*.js', '**/*.jsx'],
      severityThreshold: 'info',
      enableTaintAnalysis: false,
      enableDFG: false,
    };
  }

  /**
   * Set project root
   */
  withProjectRoot(projectRoot: string): this {
    this.projectRoot = projectRoot;
    return this;
  }

  /**
   * Set configuration
   */
  withConfig(config: Partial<RuleConfig>): this {
    this.config = { ...this.config, ...config };
    return this;
  }

  /**
   * Set previous results
   */
  withPreviousResults(results: Map<string, RuleResult>): this {
    this.previousResults = results;
    return this;
  }

  /**
   * Use existing ts-morph Project
   */
  withProject(project: Project): this {
    this.project = project;
    return this;
  }

  /**
   * Enable taint analysis
   */
  withTaintAnalysis(enabled: boolean = true): this {
    this.config.enableTaintAnalysis = enabled;
    return this;
  }

  /**
   * Enable DFG analysis
   */
  withDFG(enabled: boolean = true): this {
    this.config.enableDFG = enabled;
    return this;
  }

  /**
   * Build context for a file
   */
  async build(filePath: string): Promise<RuleContextImpl> {
    const absolutePath = path.isAbsolute(filePath)
      ? filePath
      : path.resolve(this.projectRoot, filePath);

    // Read source code
    const sourceCode = await fs.promises.readFile(absolutePath, 'utf-8');

    // Get or create Project
    const project = this.project ?? new Project({
      useInMemoryFileSystem: false,
      skipFileDependencyResolution: true,
    });

    // Get or create SourceFile
    let sourceFile = project.getSourceFile(absolutePath);
    if (!sourceFile) {
      sourceFile = project.createSourceFile(absolutePath, sourceCode, {
        overwrite: true,
      });
    }

    return new RuleContextImpl(
      absolutePath,
      sourceCode,
      sourceFile,
      this.projectRoot,
      this.config,
      this.previousResults
    );
  }

  /**
   * Build context from source code string
   */
  buildFromSource(filePath: string, sourceCode: string): RuleContextImpl {
    const absolutePath = path.isAbsolute(filePath)
      ? filePath
      : path.resolve(this.projectRoot, filePath);

    // Get or create Project
    const project = this.project ?? new Project({
      useInMemoryFileSystem: true,
      skipFileDependencyResolution: true,
    });

    // Create SourceFile
    const sourceFile = project.createSourceFile(absolutePath, sourceCode, {
      overwrite: true,
    });

    return new RuleContextImpl(
      absolutePath,
      sourceCode,
      sourceFile,
      this.projectRoot,
      this.config,
      this.previousResults
    );
  }
}

/**
 * Create a context builder
 */
export function createContextBuilder(): RuleContextBuilder {
  return new RuleContextBuilder();
}
