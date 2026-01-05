/**
 * MCP Symbolic Tools
 *
 * Tools for symbolic reasoning capabilities in MUSUBIX MCP Server.
 *
 * @packageDocumentation
 * @module tools/symbolic
 *
 * @see REQ-SYMB-001 - Symbolic Reasoning Requirements
 * @see TSK-SYMB-008 - MCP Tool Integration
 */

import type { ToolDefinition, ToolResult, TextContent } from '../types.js';
import {
  createSymbolicPipeline,
  processSymbolic,
  type FilterInput,
  type CodeCandidate,
  type ProjectContext,
  type ConstitutionCheckInput,
  // Phase 2: Formal Verification
  EarsToFormalSpecConverter,
  VerificationConditionGenerator,
  Z3Adapter,
  type EarsRequirement,
} from '@nahisaho/musubix-core';

/**
 * Create text content helper
 */
function text(content: string): TextContent {
  return { type: 'text', text: content };
}

/**
 * Success result helper
 */
function success(content: string | object): ToolResult {
  const textContent = typeof content === 'string' ? content : JSON.stringify(content, null, 2);
  return {
    content: [text(textContent)],
  };
}

/**
 * Error result helper
 */
function error(message: string): ToolResult {
  return {
    content: [text(`Error: ${message}`)],
    isError: true,
  };
}

// ============================================================
// Code Filtering Tools
// ============================================================

/**
 * Filter code candidates through symbolic pipeline
 *
 * @description
 * Processes generated code through hallucination detection,
 * constitution checking, and confidence estimation.
 */
export const filterCodeTool: ToolDefinition = {
  name: 'symbolic_filter_code',
  description:
    'Filter LLM-generated code through symbolic validation pipeline (hallucination detection, constitution compliance, confidence estimation)',
  inputSchema: {
    type: 'object',
    properties: {
      code: {
        type: 'string',
        description: 'Generated code to filter',
      },
      language: {
        type: 'string',
        description: 'Programming language of the code',
        default: 'typescript',
      },
      projectPath: {
        type: 'string',
        description: 'Path to the project root for context',
      },
      dependencies: {
        type: 'array',
        items: { type: 'string' },
        description: 'List of project dependencies',
      },
    },
    required: ['code'],
  },
  handler: async (args) => {
    try {
      const { code, language, projectPath, dependencies } = args as {
        code: string;
        language?: string;
        projectPath?: string;
        dependencies?: string[];
      };

      const candidate: CodeCandidate = {
        code,
        language: language ?? 'typescript',
        metadata: {
          generatedAt: new Date().toISOString(),
          model: 'unknown',
        },
      };

      const context: ProjectContext = {
        projectPath: projectPath ?? process.cwd(),
        symbols: [],
        dependencies: dependencies ?? [],
        requirements: [],
      };

      const input: FilterInput = {
        candidates: [candidate],
        projectContext: context,
      };

      const { filterOutput, routingResults } = await processSymbolic(input);

      return success({
        action: 'filter_code',
        result: {
          filtered: filterOutput.filteredCandidates.length > 0,
          hallucinationReport: filterOutput.hallucinationReport,
          constitutionReport: filterOutput.constitutionReport,
          routing: routingResults[0],
        },
        recommendation:
          routingResults[0]?.decision === 'accept'
            ? 'Code passed symbolic validation'
            : routingResults[0]?.decision === 'verify'
              ? 'Code requires human verification'
              : 'Code should be regenerated',
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

// ============================================================
// Hallucination Detection Tools
// ============================================================

/**
 * Detect hallucinations in code
 *
 * @description
 * Checks for references to non-existent APIs, modules, or symbols.
 */
export const detectHallucinationsTool: ToolDefinition = {
  name: 'symbolic_detect_hallucinations',
  description:
    'Detect hallucinated references (non-existent APIs, modules, symbols) in generated code',
  inputSchema: {
    type: 'object',
    properties: {
      code: {
        type: 'string',
        description: 'Code to check for hallucinations',
      },
      knownSymbols: {
        type: 'array',
        items: {
          type: 'object',
          properties: {
            name: { type: 'string' },
            type: { type: 'string', enum: ['function', 'class', 'variable', 'interface', 'type'] },
            path: { type: 'string' },
          },
          required: ['name', 'type'],
        },
        description: 'Known project symbols to validate against',
      },
      dependencies: {
        type: 'array',
        items: { type: 'string' },
        description: 'Known package dependencies',
      },
    },
    required: ['code'],
  },
  handler: async (args) => {
    try {
      const { code, knownSymbols, dependencies } = args as {
        code: string;
        knownSymbols?: Array<{ name: string; type: string; path?: string }>;
        dependencies?: string[];
      };

      const pipeline = createSymbolicPipeline();
      const candidate: CodeCandidate = {
        code,
        language: 'typescript',
        metadata: { generatedAt: new Date().toISOString(), model: 'unknown' },
      };

      const context: ProjectContext = {
        projectPath: process.cwd(),
        symbols:
          knownSymbols?.map((s) => ({
            name: s.name,
            type: s.type as 'function' | 'class' | 'variable' | 'interface' | 'type',
            path: s.path ?? '',
          })) ?? [],
        dependencies: dependencies ?? [],
        requirements: [],
      };

      const result = await pipeline.hallucinationDetector.detect(candidate, context);

      return success({
        action: 'detect_hallucinations',
        hasHallucinations: result.hasHallucinations,
        items: result.items.map((item) => ({
          type: item.type,
          identifier: item.identifier,
          location: item.location,
          suggestions: item.suggestions,
        })),
        summary: result.hasHallucinations
          ? `Found ${result.items.length} potential hallucination(s)`
          : 'No hallucinations detected',
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

// ============================================================
// Constitution Validation Tools
// ============================================================

/**
 * Check constitution compliance
 *
 * @description
 * Validates code against the 9 constitutional articles.
 */
export const checkConstitutionTool: ToolDefinition = {
  name: 'symbolic_check_constitution',
  description: 'Check code compliance against the 9 constitutional articles',
  inputSchema: {
    type: 'object',
    properties: {
      code: {
        type: 'string',
        description: 'Code to validate',
      },
      context: {
        type: 'object',
        properties: {
          hasLibraryStructure: { type: 'boolean' },
          hasCLI: { type: 'boolean' },
          hasTests: { type: 'boolean' },
          earsRequirements: { type: 'array', items: { type: 'string' } },
          hasSteeringReference: { type: 'boolean' },
          documentedPatterns: { type: 'array', items: { type: 'string' } },
          hasADR: { type: 'boolean' },
          hasQualityGates: { type: 'boolean' },
        },
        description: 'Project context for constitution checks',
      },
      articles: {
        type: 'array',
        items: {
          type: 'string',
          enum: ['I', 'II', 'III', 'IV', 'V', 'VI', 'VII', 'VIII', 'IX'],
        },
        description: 'Specific articles to check (default: all)',
      },
    },
    required: ['code'],
  },
  handler: async (args) => {
    try {
      const { code, context, articles } = args as {
        code: string;
        context?: Partial<ConstitutionCheckInput['context']>;
        articles?: string[];
      };

      const pipeline = createSymbolicPipeline();

      const checkInput: ConstitutionCheckInput = {
        code,
        context: {
          hasLibraryStructure: context?.hasLibraryStructure ?? false,
          hasCLI: context?.hasCLI ?? false,
          hasTests: context?.hasTests ?? false,
          earsRequirements: context?.earsRequirements ?? [],
          traceabilityLinks: [],
          hasSteeringReference: context?.hasSteeringReference ?? false,
          documentedPatterns: context?.documentedPatterns ?? [],
          hasADR: context?.hasADR ?? false,
          hasQualityGates: context?.hasQualityGates ?? false,
        },
        requirements: [],
      };

      const report = await pipeline.constitutionRegistry.generateReport(checkInput);

      // Filter articles if specified
      const filteredResults = articles
        ? report.articleResults.filter((r) => articles.includes(r.article))
        : report.articleResults;

      return success({
        action: 'check_constitution',
        overallPassed: report.overallPassed,
        checkedArticles: filteredResults.length,
        results: filteredResults.map((r) => {
          const rule = pipeline.constitutionRegistry.getRule(r.article);
          return {
            article: r.article,
            name: rule?.name ?? `Article ${r.article}`,
            passed: r.passed,
            violations: r.violations.map((v) => ({
              severity: v.severity,
              message: v.message,
              suggestion: v.suggestion,
            })),
          };
        }),
        summary: report.overallPassed
          ? 'All constitution articles passed'
          : `${report.articleResults.filter((r) => !r.passed).length} article(s) have violations`,
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

// ============================================================
// Confidence Estimation Tools
// ============================================================

/**
 * Estimate confidence score
 *
 * @description
 * Estimates confidence score for generated code with breakdown.
 */
export const estimateConfidenceTool: ToolDefinition = {
  name: 'symbolic_estimate_confidence',
  description:
    'Estimate confidence score (0.0-1.0) for generated code with breakdown by syntactic, semantic, factual, and consistency factors',
  inputSchema: {
    type: 'object',
    properties: {
      code: {
        type: 'string',
        description: 'Code to estimate confidence for',
      },
      language: {
        type: 'string',
        description: 'Programming language',
        default: 'typescript',
      },
      hallucinationCount: {
        type: 'number',
        description: 'Number of detected hallucinations (if known)',
        default: 0,
      },
    },
    required: ['code'],
  },
  handler: async (args) => {
    try {
      const { code, language, hallucinationCount } = args as {
        code: string;
        language?: string;
        hallucinationCount?: number;
      };

      const pipeline = createSymbolicPipeline();
      const candidate: CodeCandidate = {
        code,
        language: language ?? 'typescript',
        metadata: { generatedAt: new Date().toISOString(), model: 'unknown' },
      };

      const context: ProjectContext = {
        projectPath: process.cwd(),
        symbols: [],
        dependencies: [],
        requirements: [],
      };

      const estimation = await pipeline.confidenceEstimator.estimate(
        candidate,
        context,
        hallucinationCount ?? 0,
      );

      const routing = pipeline.router.route(estimation);

      return success({
        action: 'estimate_confidence',
        score: estimation.score,
        breakdown: estimation.breakdown,
        riskFactors: estimation.riskFactors,
        routing: {
          decision: routing.decision,
          verificationRequirements: routing.verificationRequirements,
        },
        recommendation:
          routing.decision === 'accept'
            ? 'Code has high confidence, safe to use'
            : routing.decision === 'verify'
              ? 'Code requires human review before use'
              : 'Code should be regenerated with improved context',
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

// ============================================================
// Pipeline Information Tool
// ============================================================

/**
 * Get symbolic pipeline info
 *
 * @description
 * Returns information about the symbolic processing pipeline.
 */
export const getPipelineInfoTool: ToolDefinition = {
  name: 'symbolic_pipeline_info',
  description: 'Get information about the symbolic processing pipeline and its configuration',
  inputSchema: {
    type: 'object',
    properties: {},
    required: [],
  },
  handler: async () => {
    try {
      const pipeline = createSymbolicPipeline();

      return success({
        action: 'pipeline_info',
        components: {
          filter: 'SemanticCodeFilterPipeline',
          hallucinationDetector: 'HallucinationDetector',
          constitutionRegistry: {
            type: 'ConstitutionRuleRegistry',
            ruleCount: pipeline.constitutionRegistry.ruleCount,
          },
          confidenceEstimator: 'ConfidenceEstimator',
          router: 'ConfidenceBasedRouter',
          errorHandler: 'ErrorHandler',
        },
        thresholds: {
          acceptThreshold: 0.8,
          verifyThreshold: 0.5,
          regenerateBelow: 0.5,
          maxRegenerationAttempts: 3,
        },
        constitutionArticles: [
          { article: 'I', name: 'Library-First' },
          { article: 'II', name: 'CLI Interface' },
          { article: 'III', name: 'Test-First' },
          { article: 'IV', name: 'EARS Format' },
          { article: 'V', name: 'Traceability' },
          { article: 'VI', name: 'Project Memory' },
          { article: 'VII', name: 'Design Patterns' },
          { article: 'VIII', name: 'Decision Records' },
          { article: 'IX', name: 'Quality Gates' },
        ],
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

// ============================================================
// Formal Verification Tool (Phase 2)
// ============================================================

/**
 * Formal verification using EARS to SMT-LIB conversion and Z3
 *
 * @description
 * Converts EARS requirements to formal specifications and verifies
 * using Z3 theorem prover with graceful degradation.
 *
 * @traceability TSK-SYMB-012
 */
export const formalVerifyTool: ToolDefinition = {
  name: 'sdd_formal_verify',
  description:
    'Perform formal verification on EARS requirements using Z3 theorem prover. ' +
    'Converts requirements to SMT-LIB format and generates verification conditions.',
  inputSchema: {
    type: 'object',
    properties: {
      requirements: {
        type: 'array',
        description: 'Array of EARS requirements to verify',
        items: {
          type: 'object',
          properties: {
            id: { type: 'string', description: 'Requirement ID (e.g., REQ-001)' },
            text: { type: 'string', description: 'EARS requirement text' },
            priority: {
              type: 'string',
              enum: ['P0', 'P1', 'P2'],
              description: 'Priority level',
            },
          },
          required: ['id', 'text'],
        },
      },
      verificationMode: {
        type: 'string',
        enum: ['full', 'syntax-only', 'vc-generation'],
        description:
          'Verification mode: full (with Z3), syntax-only (parse only), vc-generation (generate VCs without Z3)',
      },
      timeout: {
        type: 'number',
        description: 'Timeout in milliseconds for Z3 execution (default: 5000)',
      },
    },
    required: ['requirements'],
  },
  handler: async (args) => {
    try {
      const requirements = args.requirements as EarsRequirement[];
      const mode = (args.verificationMode as string) || 'full';
      const timeout = (args.timeout as number) || 5000;

      if (!requirements || requirements.length === 0) {
        return error('At least one requirement is required');
      }

      // Initialize converters
      const earsConverter = new EarsToFormalSpecConverter();
      const vcGenerator = new VerificationConditionGenerator();
      const z3Adapter = new Z3Adapter({ timeoutMs: timeout });

      // Check Z3 availability
      const z3Available = await z3Adapter.isAvailable();

      // Process each requirement
      const results: Array<{
        requirementId: string;
        parsed: boolean;
        patternType: string | null;
        smtLib: string | null;
        vcCount: number;
        verified: boolean | null;
        z3Result: unknown;
        errors: string[];
      }> = [];

      let totalVcs = 0;
      let successfulParses = 0;
      let verifiedCount = 0;

      // Collect all parsed requirements for batch processing
      const parsedRequirements: EarsRequirement[] = [];
      const parseErrors: Map<string, string> = new Map();

      for (const req of requirements) {
        const parseResult = earsConverter.parse(req.id, req.text);
        if (parseResult.success) {
          parsedRequirements.push(req);
          successfulParses++;
        } else {
          parseErrors.set(req.id, parseResult.error);
        }
      }

      // Convert all requirements to formal spec
      const formalSpec = earsConverter.convertAll(parsedRequirements);

      // Process results for each requirement
      for (const req of requirements) {
        const result: {
          requirementId: string;
          parsed: boolean;
          patternType: string | null;
          smtLib: string | null;
          vcCount: number;
          verified: boolean | null;
          z3Result: unknown;
          errors: string[];
        } = {
          requirementId: req.id,
          parsed: false,
          patternType: null,
          smtLib: null,
          vcCount: 0,
          verified: null,
          z3Result: null,
          errors: [],
        };

        if (parseErrors.has(req.id)) {
          result.errors.push(parseErrors.get(req.id) || 'Unknown parse error');
        } else {
          result.parsed = true;

          // Find corresponding AST node
          const astNode = formalSpec.astNodes.find((n) => n.requirementId === req.id);
          if (astNode) {
            result.patternType = astNode.pattern;
          }

          // Find corresponding SMT output
          const smtOutput = formalSpec.smtOutputs.find((s) => s.requirementId === req.id);
          if (smtOutput && mode !== 'syntax-only') {
            result.smtLib = smtOutput.smtLib;
          }

          // Generate VCs from AST if available
          if (astNode && mode !== 'syntax-only') {
            const vcResult = vcGenerator.fromEarsAst([astNode]);
            result.vcCount = vcResult.conditions.length;
            totalVcs += vcResult.conditions.length;
          }
        }

        results.push(result);
      }

      // Perform Z3 verification if full mode and Z3 available
      if (mode === 'full' && z3Available && formalSpec.combinedSmtLib) {
        // Collect all VCs
        const allVcs = formalSpec.astNodes.flatMap((ast) => vcGenerator.fromEarsAst([ast]).conditions);

        if (allVcs.length > 0) {
          const verifyResult = await z3Adapter.verifyAll(allVcs, formalSpec.combinedSmtLib);

          // Count verified
          const verifiedVcs = verifyResult.vcResults.filter((r) => r.status === 'verified').length;
          verifiedCount = verifiedVcs;

          // Update results with verification info
          for (const result of results) {
            if (result.parsed) {
              const reqVcResults = verifyResult.vcResults.filter((r) =>
                r.vcId.startsWith(result.requirementId),
              );
              if (reqVcResults.length > 0) {
                const verified = reqVcResults.filter((r) => r.status === 'verified').length;
                result.verified = verified === reqVcResults.length;
                result.z3Result = {
                  verified,
                  total: reqVcResults.length,
                  verdict: verifyResult.overallVerdict,
                };
              }
            }
          }
        }
      }

      // Summary
      const summary = {
        totalRequirements: requirements.length,
        successfullyParsed: successfulParses,
        totalVcsGenerated: totalVcs,
        z3Available,
        verified: mode === 'full' ? verifiedCount : null,
        mode,
      };

      return success({
        action: 'formal_verify',
        summary,
        results,
        recommendation:
          !z3Available && mode === 'full'
            ? 'Z3 is not installed. Install Z3 for full formal verification, or use vc-generation mode.'
            : successfulParses === requirements.length
              ? 'All requirements successfully parsed and processed'
              : `${requirements.length - successfulParses} requirement(s) failed to parse. Check EARS syntax.`,
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

// ============================================================
// Exports
// ============================================================

/**
 * All symbolic tools
 */
export const symbolicTools: ToolDefinition[] = [
  filterCodeTool,
  detectHallucinationsTool,
  checkConstitutionTool,
  estimateConfidenceTool,
  getPipelineInfoTool,
  formalVerifyTool,
];

/**
 * Get all symbolic tool definitions
 */
export function getSymbolicTools(): ToolDefinition[] {
  return symbolicTools;
}
