/**
 * Eval Harness Implementation
 *
 * REQ-EH-001: Capability Eval Definition
 * REQ-EH-002: Regression Eval Definition
 * REQ-EH-003: pass@k Metrics
 * REQ-EH-004: Grader Types
 * REQ-EH-005: Human Grader Support
 *
 * @packageDocumentation
 */

import * as path from 'path';
import * as fs from 'fs/promises';
import { exec } from 'child_process';
import { promisify } from 'util';
import {
  type CapabilityEval,
  DEFAULT_EVAL_HARNESS_CONFIG,
  type EvalHarnessConfig,
  type EvalHarnessManager,
  type EvalRunResult,
  type EvalStatus,
  type EvalType,
  type GraderConfig,
  type HumanGraderChecklistItem,
  type HumanGraderConfig,
  type PassAtKMetrics,
  type RegressionEval,
  type SuccessCriterion,
  type TestResult,
} from './types.js';

const execAsync = promisify(exec);

/**
 * Generate evaluation ID
 */
function generateEvalId(type: EvalType, name: string): string {
  const slug = name
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '')
    .slice(0, 30);
  const timestamp = Date.now().toString(36).slice(-4);
  return `${type}-${slug}-${timestamp}`;
}

/**
 * Generate criterion ID
 */
function generateCriterionId(index: number): string {
  return `criterion-${(index + 1).toString().padStart(3, '0')}`;
}

/**
 * Create eval harness manager
 *
 * @param config - Configuration options
 * @returns EvalHarnessManager instance
 */
export function createEvalHarnessManager(
  config: Partial<EvalHarnessConfig> = {}
): EvalHarnessManager {
  const fullConfig: EvalHarnessConfig = {
    ...DEFAULT_EVAL_HARNESS_CONFIG,
    ...config,
  };

  // In-memory storage for evaluations
  const capabilityEvals = new Map<string, CapabilityEval>();
  const regressionEvals = new Map<string, RegressionEval>();
  const evalResults = new Map<string, EvalRunResult[]>();

  /**
   * Ensure directories exist
   */
  async function ensureDirectories(): Promise<void> {
    await fs.mkdir(fullConfig.evalsDir, { recursive: true });
    await fs.mkdir(fullConfig.reportsDir, { recursive: true });
  }

  /**
   * Run code-based grader
   */
  async function runCodeBasedGrader(
    evalId: string,
    config: GraderConfig & { type: 'code-based' }
  ): Promise<EvalRunResult> {
    const startedAt = new Date();

    try {
      const { stdout, stderr } = await execAsync(config.command, {
        timeout: config.timeout,
      });

      const output = stdout + (stderr ? `\nSTDERR:\n${stderr}` : '');
      let status: EvalStatus = 'passed';

      if (config.matchOutput) {
        const pattern =
          config.matchOutput instanceof RegExp
            ? config.matchOutput
            : new RegExp(config.matchOutput);
        if (!pattern.test(output)) {
          status = 'failed';
        }
      }

      return {
        evalId,
        evalType: 'capability',
        graderType: 'code-based',
        status,
        startedAt,
        completedAt: new Date(),
        duration: Date.now() - startedAt.getTime(),
        output,
      };
    } catch (error) {
      return {
        evalId,
        evalType: 'capability',
        graderType: 'code-based',
        status: 'failed',
        startedAt,
        completedAt: new Date(),
        duration: Date.now() - startedAt.getTime(),
        error: error instanceof Error ? error.message : String(error),
      };
    }
  }

  /**
   * Run model-based grader (stub - requires actual LLM integration)
   */
  async function runModelBasedGrader(
    evalId: string,
    _config: GraderConfig & { type: 'model-based' }
  ): Promise<EvalRunResult> {
    const startedAt = new Date();

    // Stub implementation - would integrate with actual LLM
    return {
      evalId,
      evalType: 'capability',
      graderType: 'model-based',
      status: 'pending',
      startedAt,
      completedAt: new Date(),
      duration: Date.now() - startedAt.getTime(),
      output: 'Model-based grading requires LLM integration',
    };
  }

  return {
    async createCapabilityEval(
      name: string,
      task: string,
      criteria: string[],
      expectedOutput: string
    ): Promise<CapabilityEval> {
      await ensureDirectories();

      const id = generateEvalId('capability', name);
      const now = new Date();

      const successCriteria: SuccessCriterion[] = criteria.map(
        (desc, index) => ({
          id: generateCriterionId(index),
          description: desc,
          status: 'pending' as EvalStatus,
        })
      );

      const eval_: CapabilityEval = {
        id,
        name,
        task,
        successCriteria,
        expectedOutput,
        createdAt: now,
        updatedAt: now,
      };

      capabilityEvals.set(id, eval_);

      // Save to file
      const filePath = path.join(fullConfig.evalsDir, `${id}.json`);
      await fs.writeFile(filePath, JSON.stringify(eval_, null, 2));

      return eval_;
    },

    async createRegressionEval(
      name: string,
      baseline: string,
      tests: TestResult[],
      previousPassedCount: number
    ): Promise<RegressionEval> {
      await ensureDirectories();

      const id = generateEvalId('regression', name);
      const passedCount = tests.filter((t) => t.status === 'pass').length;

      const eval_: RegressionEval = {
        id,
        name,
        baseline,
        tests,
        passedCount,
        totalCount: tests.length,
        previousPassedCount,
        createdAt: new Date(),
      };

      regressionEvals.set(id, eval_);

      // Save to file
      const filePath = path.join(fullConfig.evalsDir, `${id}.json`);
      await fs.writeFile(filePath, JSON.stringify(eval_, null, 2));

      return eval_;
    },

    async runEval(
      evalId: string,
      graderConfig: GraderConfig
    ): Promise<EvalRunResult> {
      let result: EvalRunResult;

      switch (graderConfig.type) {
        case 'code-based':
          result = await runCodeBasedGrader(evalId, graderConfig);
          break;
        case 'model-based':
          result = await runModelBasedGrader(evalId, graderConfig);
          break;
        case 'human':
          result = {
            evalId,
            evalType: 'capability',
            graderType: 'human',
            status: graderConfig.verdict === 'pass' ? 'passed' : 'pending',
            startedAt: new Date(),
            completedAt: graderConfig.verdict ? new Date() : undefined,
          };
          break;
        default:
          throw new Error(`Unknown grader type: ${(graderConfig as GraderConfig).type}`);
      }

      // Store result
      const existing = evalResults.get(evalId) || [];
      existing.push(result);
      evalResults.set(evalId, existing);

      return result;
    },

    async calculatePassAtK(evalId: string, k: number = 3): Promise<PassAtKMetrics> {
      const results = evalResults.get(evalId) || [];
      const attempts = results.slice(-k);

      const totalAttempts = attempts.length;
      const successfulAttempts = attempts.filter(
        (r) => r.status === 'passed'
      ).length;

      // pass@1: First attempt success
      const passAt1 = attempts.length > 0 && attempts[0].status === 'passed' ? 1 : 0;

      // pass@k: At least one success
      const passAt3 = successfulAttempts > 0 ? 1 : 0;

      // consecutive@k: All k attempts successful
      const consecutiveAt3 =
        totalAttempts >= k && successfulAttempts === k ? 1 : 0;

      return {
        passAt1,
        passAt3,
        consecutiveAt3,
        totalAttempts,
        successfulAttempts,
      };
    },

    async generateHumanGraderTemplate(
      evalId: string,
      reviewer?: string
    ): Promise<HumanGraderConfig> {
      const eval_ = capabilityEvals.get(evalId);

      let checklist: HumanGraderChecklistItem[];

      if (eval_) {
        // Generate from capability eval criteria
        checklist = eval_.successCriteria.map((c) => ({
          id: c.id,
          description: c.description,
          checked: false,
        }));
      } else {
        // Default checklist
        checklist = [
          { id: 'spec-met', description: '仕様を満たしている', checked: false },
          {
            id: 'edge-cases',
            description: 'エッジケースが考慮されている',
            checked: false,
          },
          {
            id: 'api-compat',
            description: '既存API互換性が維持されている',
            checked: false,
          },
          {
            id: 'security',
            description: 'セキュリティ上の懸念がない',
            checked: false,
          },
        ];
      }

      return {
        type: 'human',
        reviewer,
        checklist,
      };
    },

    async recordHumanVerdict(
      evalId: string,
      verdict: 'pass' | 'fail',
      notes?: string
    ): Promise<EvalRunResult> {
      const result: EvalRunResult = {
        evalId,
        evalType: 'capability',
        graderType: 'human',
        status: verdict === 'pass' ? 'passed' : 'failed',
        startedAt: new Date(),
        completedAt: new Date(),
        output: notes,
      };

      const existing = evalResults.get(evalId) || [];
      existing.push(result);
      evalResults.set(evalId, existing);

      return result;
    },

    async getEval(
      evalId: string
    ): Promise<CapabilityEval | RegressionEval | null> {
      return (
        capabilityEvals.get(evalId) || regressionEvals.get(evalId) || null
      );
    },

    async listEvals(
      type?: EvalType
    ): Promise<Array<CapabilityEval | RegressionEval>> {
      const results: Array<CapabilityEval | RegressionEval> = [];

      if (!type || type === 'capability') {
        results.push(...capabilityEvals.values());
      }
      if (!type || type === 'regression') {
        results.push(...regressionEvals.values());
      }

      return results;
    },

    getConfig(): EvalHarnessConfig {
      return fullConfig;
    },
  };
}

/**
 * Format capability eval as markdown
 *
 * @param eval_ - Capability eval to format
 * @returns Markdown string
 */
export function formatCapabilityEvalMarkdown(eval_: CapabilityEval): string {
  const criteriaList = eval_.successCriteria
    .map((c) => {
      const checkbox = c.status === 'passed' ? '[x]' : '[ ]';
      return `  - ${checkbox} ${c.description}`;
    })
    .join('\n');

  return `[CAPABILITY EVAL: ${eval_.name}]
Task: ${eval_.task}
Success Criteria:
${criteriaList}
Expected Output: ${eval_.expectedOutput}`;
}

/**
 * Format regression eval as markdown
 *
 * @param eval_ - Regression eval to format
 * @returns Markdown string
 */
export function formatRegressionEvalMarkdown(eval_: RegressionEval): string {
  const testList = eval_.tests
    .map((t) => `  - ${t.name}: ${t.status.toUpperCase()}`)
    .join('\n');

  return `[REGRESSION EVAL: ${eval_.name}]
Baseline: ${eval_.baseline}
Tests:
${testList}
Result: ${eval_.passedCount}/${eval_.totalCount} passed (previously ${eval_.previousPassedCount}/${eval_.totalCount})`;
}

/**
 * Format pass@k metrics as markdown
 *
 * @param metrics - pass@k metrics
 * @returns Markdown string
 */
export function formatPassAtKMarkdown(metrics: PassAtKMetrics): string {
  return `pass@k Metrics:
- pass@1: ${(metrics.passAt1 * 100).toFixed(1)}%
- pass@3: ${(metrics.passAt3 * 100).toFixed(1)}%
- consecutive@3: ${(metrics.consecutiveAt3 * 100).toFixed(1)}%
- Total Attempts: ${metrics.totalAttempts}
- Successful: ${metrics.successfulAttempts}`;
}

/**
 * Format human grader template as markdown
 *
 * @param config - Human grader config
 * @param evalName - Evaluation name
 * @returns Markdown string
 */
export function formatHumanGraderMarkdown(
  config: HumanGraderConfig,
  evalName: string
): string {
  const checklist = config.checklist
    .map((item) => `  - [${item.checked ? 'x' : ' '}] ${item.description}`)
    .join('\n');

  return `[HUMAN GRADE: ${evalName}]
Reviewer: ${config.reviewer || '@username'}
Checklist:
${checklist}
Notes:
  - ${config.notes || '...'}
Verdict: ${config.verdict?.toUpperCase() || 'PENDING'}`;
}
