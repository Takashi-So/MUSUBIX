/**
 * @fileoverview Main integration facade for Lean 4 formal verification
 * @module @nahisaho/musubix-lean
 * @traceability REQ-LEAN-001 to REQ-LEAN-006
 */

import { Result, ok, err } from 'neverthrow';
import type {
  LeanConfig,
  LeanTheorem,
  LeanProof,
  LeanVersion,
  VerificationResult,
  VerificationReport,
  HybridVerificationResult,
  EarsRequirement,
  TypeScriptSpec,
} from '../types.js';
import { LeanEnvironmentDetector } from '../environment/LeanEnvironmentDetector.js';
import { LeanProjectInitializer } from '../environment/LeanProjectInitializer.js';
import { LeanRunner } from '../infrastructure/LeanRunner.js';
import { LeanFileGenerator } from '../infrastructure/LeanFileGenerator.js';
import { EarsToLeanConverter } from '../converters/EarsToLeanConverter.js';
import { TypeScriptSpecifier } from '../converters/TypeScriptSpecifier.js';
import { ProofGenerator } from '../proof/ProofGenerator.js';
import { ReProverClient } from '../proof/ReProverClient.js';
import { VerificationReporter } from '../reporting/VerificationReporter.js';
import { TraceabilityManager } from '../traceability/TraceabilityManager.js';
import { HybridVerifier, type RuntimeTestResult } from '../hybrid/HybridVerifier.js';
import {
  LeanIntegrationError,
  LeanEnvironmentError,
  LeanVerificationError,
} from '../errors.js';

/**
 * Integration status
 */
export interface IntegrationStatus {
  initialized: boolean;
  leanAvailable: boolean;
  leanVersion?: LeanVersion;
  projectInitialized: boolean;
  mathlibAvailable: boolean;
  reprovarAvailable: boolean;
}

/**
 * Verification options
 */
export interface VerificationOptions {
  generateProofs?: boolean;
  useReProver?: boolean;
  timeout?: number;
  traceability?: boolean;
  hybridMode?: boolean;
}

/**
 * Main integration class for Lean 4 formal verification
 * Provides a unified API for all verification capabilities
 *
 * @traceability REQ-LEAN-001
 */
export class LeanIntegration {
  private leanConfig: LeanConfig;
  private detector: LeanEnvironmentDetector;
  private initializer: LeanProjectInitializer;
  private runner: LeanRunner;
  private generator: LeanFileGenerator;
  private earsConverter: EarsToLeanConverter;
  private tsSpecifier: TypeScriptSpecifier;
  private proofGenerator: ProofGenerator;
  private reprovarClient: ReProverClient;
  private reporter: VerificationReporter;
  private traceability: TraceabilityManager;
  private hybridVerifier: HybridVerifier;

  private status: IntegrationStatus = {
    initialized: false,
    leanAvailable: false,
    projectInitialized: false,
    mathlibAvailable: false,
    reprovarAvailable: false,
  };

  constructor(config: Partial<LeanConfig> = {}) {
    this.leanConfig = {
      leanPath: config.leanPath ?? 'lean',
      projectPath: config.projectPath ?? process.cwd(),
      timeout: config.timeout ?? 30000,
      lakeEnabled: config.lakeEnabled ?? true,
      mathlibEnabled: config.mathlibEnabled ?? false,
      verbose: config.verbose ?? false,
    };

    // Initialize all components
    this.detector = new LeanEnvironmentDetector();
    this.initializer = new LeanProjectInitializer(config);
    this.runner = new LeanRunner(config);
    this.generator = new LeanFileGenerator(config);
    this.earsConverter = new EarsToLeanConverter();
    this.tsSpecifier = new TypeScriptSpecifier();
    this.proofGenerator = new ProofGenerator();
    this.reprovarClient = new ReProverClient(config);
    this.reporter = new VerificationReporter();
    this.traceability = new TraceabilityManager();
    this.hybridVerifier = new HybridVerifier(config);

    // Connect components
    this.hybridVerifier.setReporter(this.reporter);
    this.hybridVerifier.setTraceabilityManager(this.traceability);
  }

  /**
   * Initialize the integration
   * @traceability REQ-LEAN-ENV-001
   */
  async initialize(): Promise<Result<IntegrationStatus, LeanIntegrationError>> {
    try {
      // Detect Lean environment
      const envInfo = await this.detector.detect();

      this.status.leanAvailable = envInfo.installed;
      this.status.leanVersion = envInfo.version ?? undefined;
      this.status.mathlibAvailable = envInfo.mathlibAvailable;

      if (!envInfo.installed) {
        return err(
          new LeanIntegrationError(
            'Lean 4 is not installed. Please install Lean 4 from https://leanprover.github.io/lean4/doc/setup.html'
          )
        );
      }

      // Check ReProver availability
      const reprovarAvailable = await this.reprovarClient.isAvailable();
      this.status.reprovarAvailable = reprovarAvailable;

      this.status.initialized = true;
      return ok(this.status);
    } catch (error) {
      return err(
        new LeanIntegrationError(
          `Initialization failed: ${error instanceof Error ? error.message : String(error)}`
        )
      );
    }
  }

  /**
   * Initialize a new Lean project
   * @traceability REQ-LEAN-ENV-002
   */
  async initProject(
    name: string,
    path?: string
  ): Promise<Result<void, LeanIntegrationError>> {
    try {
      await this.initializer.initialize({ name, directory: path ?? process.cwd() });
      this.status.projectInitialized = true;
      return ok(undefined);
    } catch (error) {
      return err(
        new LeanIntegrationError(
          `Project initialization failed: ${error instanceof Error ? error.message : String(error)}`
        )
      );
    }
  }

  /**
   * Convert EARS requirement to Lean theorem
   * @traceability REQ-LEAN-CONV-001
   */
  convertRequirement(requirement: EarsRequirement): Result<LeanTheorem, LeanIntegrationError> {
    const result = this.earsConverter.convert(requirement);
    return result.mapErr(
      (e: Error) => new LeanIntegrationError(`Conversion failed: ${e.message}`)
    );
  }

  /**
   * Convert TypeScript specification to Lean
   * @traceability REQ-LEAN-CONV-002
   */
  convertTypeScript(spec: TypeScriptSpec): Result<LeanTheorem[], LeanIntegrationError> {
    const functions = spec.functions ?? [];
    const theorems: LeanTheorem[] = [];
    
    for (const func of functions) {
      const result = this.tsSpecifier.specify(func);
      if (result.isErr()) {
        return err(
          new LeanIntegrationError(`TypeScript conversion failed: ${result.error.message}`)
        );
      }
      // Convert LeanFunctionSpec to LeanTheorem
      const funcSpec = result.value;
      theorems.push({
        id: `theorem-${func.name}`,
        name: funcSpec.functionName,
        statement: funcSpec.typeSignature,
        requirementId: `ts-func-${func.name}`,
        hypotheses: funcSpec.preconditionHypotheses,
        conclusion: funcSpec.postconditionGoal,
        leanCode: funcSpec.leanCode,
      });
    }
    
    return ok(theorems);
  }

  /**
   * Generate proof for a theorem
   * @traceability REQ-LEAN-PROOF-001
   */
  async generateProof(
    theorem: LeanTheorem,
    options: { useReProver?: boolean } = {}
  ): Promise<Result<LeanProof, LeanIntegrationError>> {
    try {
      let proof: LeanProof;

      if (options.useReProver && this.status.reprovarAvailable) {
        // Create proof state from theorem for ReProver
        const proofState = {
          goals: [{ id: 0, type: theorem.conclusion?.type ?? '', leanCode: theorem.conclusion?.leanCode ?? '' }],
          hypotheses: theorem.hypotheses,
          currentGoal: 0,
        };
        const searchResult = await this.reprovarClient.search(proofState);
        if (!searchResult.found || !searchResult.proof) {
          return err(new LeanIntegrationError(`ReProver search failed: ${searchResult.suggestions.join(', ')}`));
        }
        // Convert ReProverSearchResult to LeanProof
        proof = {
          id: `proof-${theorem.id}`,
          theoremId: theorem.id,
          tactics: searchResult.searchPath.map(node => node.tactic),
          leanCode: searchResult.proof,
          isComplete: true,
          generatedAt: new Date().toISOString(),
        };
      } else {
        const result = await this.proofGenerator.generate(theorem);
        if (!result.success || !result.proof) {
          return err(new LeanIntegrationError(`Proof generation failed: ${result.error ?? 'Unknown error'}`));
        }
        proof = result.proof;
      }

      return ok(proof);
    } catch (error) {
      return err(
        new LeanIntegrationError(
          `Proof generation failed: ${error instanceof Error ? error.message : String(error)}`
        )
      );
    }
  }

  /**
   * Verify a theorem
   * @traceability REQ-LEAN-VERIFY-001
   */
  async verify(
    theorem: LeanTheorem,
    options: VerificationOptions = {}
  ): Promise<Result<VerificationResult, LeanVerificationError>> {
    const startTime = Date.now();

    try {
      // Register in traceability
      if (options.traceability !== false) {
        this.traceability.linkTheoremToRequirement(theorem);
      }

      // Generate proof if needed
      let theoremWithProof = theorem;
      if (options.generateProofs && !theorem.proof) {
        const proofResult = await this.generateProof(theorem, {
          useReProver: options.useReProver,
        });
        if (proofResult.isOk()) {
          theoremWithProof = { ...theorem, proof: proofResult.value };

          // Link proof in traceability
          if (options.traceability !== false) {
            this.traceability.linkProofToTheorem(proofResult.value, theorem);
          }
        }
      }

      // Generate Lean file
      const outputDir = this.leanConfig.projectPath ?? process.cwd();
      const genResult = await this.generator.generate([theoremWithProof], {
        outputDir,
        includeImports: true,
        includeProofs: true,
      });

      // Type check
      const checkResult = await this.runner.typeCheck(genResult.path);

      const result: VerificationResult = {
        theoremId: theorem.id,
        status: checkResult.valid ? 'proved' : 'incomplete',
        proof: theoremWithProof.proof,
        errors: checkResult.errors,
        warnings: [],
        duration: Date.now() - startTime,
      };

      // Add to reporter
      this.reporter.addResult({
        theorem: theoremWithProof,
        status: result.status === 'proved' ? 'proved' : 'incomplete',
        proof: result.proof,
        error: result.errors[0],
        duration: result.duration,
      });

      return ok(result);
    } catch (error) {
      return err(
        new LeanVerificationError(
          `Verification failed: ${error instanceof Error ? error.message : String(error)}`
        )
      );
    }
  }

  /**
   * Perform hybrid verification
   * @traceability REQ-LEAN-HYBRID-001
   */
  async verifyHybrid(
    functionId: string,
    runtimeTests: () => RuntimeTestResult,
    theorem: LeanTheorem
  ): Promise<Result<HybridVerificationResult, LeanVerificationError>> {
    return this.hybridVerifier.verify(functionId, runtimeTests, theorem);
  }

  /**
   * Batch verify multiple theorems
   */
  async verifyBatch(
    theorems: LeanTheorem[],
    options: VerificationOptions = {}
  ): Promise<Map<string, VerificationResult>> {
    const results = new Map<string, VerificationResult>();

    for (const theorem of theorems) {
      const result = await this.verify(theorem, options);
      if (result.isOk()) {
        results.set(theorem.id, result.value);
      } else {
        results.set(theorem.id, {
          theoremId: theorem.id,
          status: 'error',
          errors: [result.error.message],
          warnings: [],
          duration: 0,
        });
      }
    }

    return results;
  }

  /**
   * Generate verification report
   * @traceability REQ-LEAN-FEEDBACK-001
   */
  generateReport(): VerificationReport {
    return this.reporter.generate();
  }

  /**
   * Export report in specified format
   */
  exportReport(format: 'json' | 'markdown' | 'html' | 'csv'): string {
    return this.reporter.export(format);
  }

  /**
   * Get traceability coverage
   * @traceability REQ-LEAN-TRACE-003
   */
  getTraceabilityCoverage(requirementIds: string[]): {
    totalRequirements: number;
    coveredRequirements: number;
    coveragePercentage: number;
    untraced: string[];
    fullyTraced: string[];
  } {
    const coverage = this.traceability.calculateCoverage(requirementIds);
    return {
      totalRequirements: coverage.totalRequirements,
      coveredRequirements: coverage.coveredRequirements,
      coveragePercentage: coverage.coveragePercentage,
      untraced: coverage.untraced,
      fullyTraced: coverage.fullyTraced,
    };
  }

  /**
   * Get traceability matrix as Markdown
   */
  getTraceabilityMatrix(): string {
    return this.traceability.exportMarkdown();
  }

  /**
   * Get current status
   */
  getStatus(): IntegrationStatus {
    return { ...this.status };
  }

  /**
   * Get Lean version
   */
  async getLeanVersion(): Promise<Result<LeanVersion, LeanEnvironmentError>> {
    try {
      const version = await this.runner.getVersion();
      return ok(version);
    } catch (error) {
      return err(
        new LeanEnvironmentError(
          `Failed to get version: ${error instanceof Error ? error.message : String(error)}`
        )
      );
    }
  }

  /**
   * Check if a file has valid Lean syntax
   */
  async validateSyntax(filePath: string): Promise<Result<boolean, LeanVerificationError>> {
    try {
      const result = await this.runner.typeCheck(filePath);
      return ok(result.valid);
    } catch (error) {
      return err(
        new LeanVerificationError(
          `Syntax validation failed: ${error instanceof Error ? error.message : String(error)}`
        )
      );
    }
  }

  /**
   * Clear all state
   */
  reset(): void {
    this.reporter.clear();
    this.traceability.clear();
    this.status = {
      initialized: false,
      leanAvailable: false,
      projectInitialized: false,
      mathlibAvailable: false,
      reprovarAvailable: false,
    };
  }
}

/**
 * Factory function for creating LeanIntegration instance
 */
export function createLeanIntegration(config?: Partial<LeanConfig>): LeanIntegration {
  return new LeanIntegration(config);
}
