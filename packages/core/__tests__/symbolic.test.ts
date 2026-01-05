/**
 * Symbolic Module Unit Tests
 *
 * Tests for the neuro-symbolic integration components.
 *
 * @see REQ-SYMB-001 - Symbolic Reasoning Requirements
 * @see TSK-SYMB-001 through TSK-SYMB-008
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  // Types
  type FilterInput,
  type CodeCandidate,
  type ProjectContext,
  type SymbolInfo,
  type ConstitutionCheckInput,
  // Classes
  SemanticCodeFilterPipeline,
  HallucinationDetector,
  ProjectSymbolIndex,
  ConstitutionRuleRegistry,
  ConfidenceEstimator,
  ConfidenceBasedRouter,
  ErrorHandler,
  // Defaults
  DEFAULT_CONSTITUTION_RULES,
  // Factory functions
  createSymbolicPipeline,
  processSymbolic,
  // Article validators
  checkArticleI,
  checkArticleIII,
  checkArticleIV,
} from '../src/symbolic/index.js';

// === Test Fixtures ===

function createTestCandidate(code: string, language = 'typescript'): CodeCandidate {
  return {
    code,
    language,
    metadata: {
      generatedAt: new Date().toISOString(),
      model: 'test-model',
    },
  };
}

function createTestContext(symbols: SymbolInfo[] = []): ProjectContext {
  return {
    projectPath: '/test/project',
    symbols,
    dependencies: ['typescript', 'vitest'],
    requirements: [],
  };
}

function createTestSymbols(): SymbolInfo[] {
  return [
    { name: 'UserService', type: 'class', path: '/test/services/user.ts' },
    { name: 'createUser', type: 'function', path: '/test/services/user.ts' },
    { name: 'User', type: 'interface', path: '/test/types/user.ts' },
    { name: 'validateEmail', type: 'function', path: '/test/utils/validation.ts' },
  ];
}

// === SemanticCodeFilterPipeline Tests ===

describe('SemanticCodeFilterPipeline', () => {
  let filter: SemanticCodeFilterPipeline;
  let hallucinationDetector: HallucinationDetector;
  let constitutionRegistry: ConstitutionRuleRegistry;

  beforeEach(() => {
    hallucinationDetector = new HallucinationDetector();
    constitutionRegistry = new ConstitutionRuleRegistry({
      rules: DEFAULT_CONSTITUTION_RULES,
    });
    filter = new SemanticCodeFilterPipeline({
      hallucinationDetector,
      constitutionRegistry,
    });
  });

  it('should filter valid code without violations', async () => {
    const input: FilterInput = {
      candidates: [createTestCandidate('const x = 1;')],
      projectContext: createTestContext(createTestSymbols()),
    };

    const output = await filter.filter(input);

    expect(output).toBeDefined();
    expect(output.filteredCandidates).toHaveLength(1);
  });

  it('should include hallucination report', async () => {
    const input: FilterInput = {
      candidates: [
        createTestCandidate(`
import { NonExistentModule } from 'fake-package';
const result = NonExistentModule.doSomething();
`),
      ],
      projectContext: createTestContext(createTestSymbols()),
    };

    const output = await filter.filter(input);

    expect(output.hallucinationReport).toBeDefined();
  });

  it('should include constitution report', async () => {
    const input: FilterInput = {
      candidates: [createTestCandidate('const x = 1;')],
      projectContext: createTestContext(),
    };

    const output = await filter.filter(input);

    expect(output.constitutionReport).toBeDefined();
  });
});

// === HallucinationDetector Tests ===

describe('HallucinationDetector', () => {
  let detector: HallucinationDetector;

  beforeEach(() => {
    detector = new HallucinationDetector();
  });

  it('should detect non-existent imports', async () => {
    const candidate = createTestCandidate(`
import { FakeService } from './non-existent';
import { AnotherFake } from 'unknown-package';
`);
    const context = createTestContext(createTestSymbols());

    const result = await detector.detect(candidate, context);

    expect(result).toBeDefined();
    expect(result.hasHallucinations).toBe(true);
    expect(result.items.length).toBeGreaterThan(0);
    expect(result.items.some((i) => i.type === 'import')).toBe(true);
  });

  it('should not flag known project symbols', async () => {
    const candidate = createTestCandidate(`
import { UserService } from './services/user';
const svc = new UserService();
`);
    const context = createTestContext(createTestSymbols());

    const result = await detector.detect(candidate, context);

    // Known symbols should not be flagged as hallucinations
    const userServiceHallucination = result.items.find(
      (i) => i.identifier === 'UserService' && i.type === 'function_call',
    );
    expect(userServiceHallucination).toBeUndefined();
  });

  it('should provide suggestions for misspelled identifiers', async () => {
    const candidate = createTestCandidate(`
const svc = new UsrService(); // Misspelled
`);
    const context = createTestContext(createTestSymbols());

    const result = await detector.detect(candidate, context);

    // Should detect 'UsrService' as hallucination with suggestion 'UserService'
    const hallucination = result.items.find((i) => i.identifier === 'UsrService');
    if (hallucination) {
      expect(hallucination.suggestions).toContain('UserService');
    }
  });

  it('should handle code without hallucinations', async () => {
    const candidate = createTestCandidate(`
const x = 1;
const y = x + 2;
console.log(y);
`);
    const context = createTestContext([]);

    const result = await detector.detect(candidate, context);

    expect(result).toBeDefined();
  });
});

// === ProjectSymbolIndex Tests ===

describe('ProjectSymbolIndex', () => {
  let index: ProjectSymbolIndex;

  beforeEach(() => {
    index = new ProjectSymbolIndex();
    for (const symbol of createTestSymbols()) {
      index.addSymbol(symbol);
    }
  });

  it('should check if symbol exists', () => {
    expect(index.hasSymbol('UserService')).toBe(true);
    expect(index.hasSymbol('createUser')).toBe(true);
    expect(index.hasSymbol('NonExistent')).toBe(false);
  });

  it('should find similar symbols', () => {
    const similar = index.findSimilar('UsrService', 3);

    expect(similar).toContain('UserService');
  });

  it('should get symbol info', () => {
    const info = index.getSymbol('UserService');

    expect(info).toBeDefined();
    expect(info?.type).toBe('class');
    expect(info?.path).toBe('/test/services/user.ts');
  });

  it('should clear index', () => {
    index.clear();

    expect(index.hasSymbol('UserService')).toBe(false);
    expect(index.size).toBe(0);
  });
});

// === ConstitutionRuleRegistry Tests ===

describe('ConstitutionRuleRegistry', () => {
  let registry: ConstitutionRuleRegistry;

  beforeEach(() => {
    registry = new ConstitutionRuleRegistry({
      rules: DEFAULT_CONSTITUTION_RULES,
    });
  });

  it('should have all 9 constitution articles', () => {
    expect(registry.ruleCount).toBe(9);
  });

  it('should check code against all rules', async () => {
    const input: ConstitutionCheckInput = {
      code: 'const x = 1;',
      context: {
        hasLibraryStructure: false,
        hasCLI: false,
        hasTests: false,
        earsRequirements: [],
        traceabilityLinks: [],
        hasSteeringReference: false,
        documentedPatterns: [],
        hasADR: false,
        hasQualityGates: false,
      },
      requirements: [],
    };

    const result = await registry.check(input);

    expect(result).toBeDefined();
    expect(result.passed).toBeDefined();
    expect(result.violations).toBeDefined();
  });

  it('should generate compliance report', async () => {
    const input: ConstitutionCheckInput = {
      code: 'const x = 1;',
      context: {
        hasLibraryStructure: true,
        hasCLI: true,
        hasTests: true,
        earsRequirements: ['REQ-001'],
        traceabilityLinks: [{ requirementId: 'REQ-001', designId: 'DES-001' }],
        hasSteeringReference: true,
        documentedPatterns: ['Repository'],
        hasADR: true,
        hasQualityGates: true,
      },
      requirements: [],
    };

    const report = await registry.generateReport(input);

    expect(report).toBeDefined();
    expect(report.overallPassed).toBeDefined();
    expect(report.articleResults).toHaveLength(9);
  });

  it('should get rule by article', () => {
    const articleI = registry.getRule('I');
    const articleIX = registry.getRule('IX');

    expect(articleI).toBeDefined();
    expect(articleI?.name).toContain('Library-First');
    expect(articleIX).toBeDefined();
    expect(articleIX?.name).toContain('Quality Gates');
  });
});

// === Article Validator Tests ===

describe('Article Validators', () => {
  describe('Article I - Library-First', () => {
    it('should pass when library structure exists', async () => {
      const input: ConstitutionCheckInput = {
        code: '',
        context: {
          hasLibraryStructure: true,
          hasCLI: false,
          hasTests: false,
          earsRequirements: [],
          traceabilityLinks: [],
          hasSteeringReference: false,
          documentedPatterns: [],
          hasADR: false,
          hasQualityGates: false,
        },
        requirements: [],
      };

      const result = await checkArticleI(input);

      expect(result.passed).toBe(true);
      expect(result.violations).toHaveLength(0);
    });

    it('should fail when library structure missing', async () => {
      const input: ConstitutionCheckInput = {
        code: '',
        context: {
          hasLibraryStructure: false,
          hasCLI: false,
          hasTests: false,
          earsRequirements: [],
          traceabilityLinks: [],
          hasSteeringReference: false,
          documentedPatterns: [],
          hasADR: false,
          hasQualityGates: false,
        },
        requirements: [],
      };

      const result = await checkArticleI(input);

      expect(result.passed).toBe(false);
      expect(result.violations.length).toBeGreaterThan(0);
    });
  });

  describe('Article III - Test-First', () => {
    it('should pass when tests exist', async () => {
      const input: ConstitutionCheckInput = {
        code: '',
        context: {
          hasLibraryStructure: false,
          hasCLI: false,
          hasTests: true,
          earsRequirements: [],
          traceabilityLinks: [],
          hasSteeringReference: false,
          documentedPatterns: [],
          hasADR: false,
          hasQualityGates: false,
        },
        requirements: [],
      };

      const result = await checkArticleIII(input);

      expect(result.passed).toBe(true);
    });
  });

  describe('Article IV - EARS Format', () => {
    it('should pass when EARS requirements exist', async () => {
      const input: ConstitutionCheckInput = {
        code: '',
        context: {
          hasLibraryStructure: false,
          hasCLI: false,
          hasTests: false,
          earsRequirements: ['REQ-001', 'REQ-002'],
          traceabilityLinks: [],
          hasSteeringReference: false,
          documentedPatterns: [],
          hasADR: false,
          hasQualityGates: false,
        },
        requirements: [],
      };

      const result = await checkArticleIV(input);

      expect(result.passed).toBe(true);
    });
  });
});

// === ConfidenceEstimator Tests ===

describe('ConfidenceEstimator', () => {
  let estimator: ConfidenceEstimator;

  beforeEach(() => {
    estimator = new ConfidenceEstimator();
  });

  it('should estimate confidence for valid code', async () => {
    const candidate = createTestCandidate(`
function add(a: number, b: number): number {
  return a + b;
}
`);
    const context = createTestContext();

    const estimation = await estimator.estimate(candidate, context, 0);

    expect(estimation).toBeDefined();
    expect(estimation.score).toBeGreaterThan(0);
    expect(estimation.score).toBeLessThanOrEqual(1);
    expect(estimation.breakdown).toBeDefined();
    expect(estimation.breakdown.syntactic).toBeDefined();
    expect(estimation.breakdown.semantic).toBeDefined();
    expect(estimation.breakdown.factual).toBeDefined();
    expect(estimation.breakdown.consistency).toBeDefined();
  });

  it('should penalize code with hallucinations', async () => {
    const candidate = createTestCandidate('const x = 1;');
    const context = createTestContext();

    const withoutHallucinations = await estimator.estimate(candidate, context, 0);
    const withHallucinations = await estimator.estimate(candidate, context, 3);

    expect(withHallucinations.score).toBeLessThan(withoutHallucinations.score);
    expect(withHallucinations.breakdown.factual).toBeLessThan(
      withoutHallucinations.breakdown.factual,
    );
  });

  it('should identify risk factors', async () => {
    const candidate = createTestCandidate('const x = 1;');
    const context = createTestContext();

    const estimation = await estimator.estimate(candidate, context, 5);

    expect(estimation.riskFactors.length).toBeGreaterThan(0);
    expect(estimation.riskFactors.some((r) => r.type === 'hallucination_risk')).toBe(true);
  });

  it('should include explanation', async () => {
    const candidate = createTestCandidate('const x = 1;');
    const context = createTestContext();

    const estimation = await estimator.estimate(candidate, context, 0);

    expect(estimation.explanation).toBeDefined();
    expect(estimation.explanation.summary).toBeDefined();
    expect(estimation.explanation.reasoning.length).toBeGreaterThan(0);
  });

  it('should respect custom weights', async () => {
    const customEstimator = new ConfidenceEstimator({
      syntacticWeight: 1.0,
      semanticWeight: 0,
      factualWeight: 0,
      consistencyWeight: 0,
    });

    const candidate = createTestCandidate('const x = 1;');
    const context = createTestContext();

    const estimation = await customEstimator.estimate(candidate, context, 0);

    // Score should be heavily influenced by syntactic only
    expect(estimation.score).toBeCloseTo(estimation.breakdown.syntactic, 1);
  });
});

// === ConfidenceBasedRouter Tests ===

describe('ConfidenceBasedRouter', () => {
  let router: ConfidenceBasedRouter;

  beforeEach(() => {
    router = new ConfidenceBasedRouter();
  });

  it('should accept high confidence code', () => {
    const estimation = {
      score: 0.9,
      breakdown: { syntactic: 0.9, semantic: 0.9, factual: 0.9, consistency: 0.9 },
      riskFactors: [],
      explanation: { summary: '', reasoning: [], evidence: [], relatedRequirements: [] },
    };

    const result = router.route(estimation);

    expect(result.decision).toBe('accept');
    expect(result.verificationRequirements).toHaveLength(0);
  });

  it('should require verification for medium confidence', () => {
    const estimation = {
      score: 0.65,
      breakdown: { syntactic: 0.7, semantic: 0.6, factual: 0.65, consistency: 0.65 },
      riskFactors: [],
      explanation: { summary: '', reasoning: [], evidence: [], relatedRequirements: [] },
    };

    const result = router.route(estimation);

    expect(result.decision).toBe('verify');
    expect(result.verificationRequirements.length).toBeGreaterThan(0);
  });

  it('should recommend regeneration for low confidence', () => {
    const estimation = {
      score: 0.3,
      breakdown: { syntactic: 0.4, semantic: 0.3, factual: 0.2, consistency: 0.3 },
      riskFactors: [{ type: 'hallucination_risk' as const, description: 'test', impact: 0.3 }],
      explanation: { summary: '', reasoning: [], evidence: [], relatedRequirements: [] },
    };

    const result = router.route(estimation);

    expect(result.decision).toBe('regenerate');
  });

  it('should use custom thresholds', () => {
    const customRouter = new ConfidenceBasedRouter({
      thresholds: {
        acceptThreshold: 0.95,
        verifyThreshold: 0.7,
      },
    });

    const estimation = {
      score: 0.85,
      breakdown: { syntactic: 0.9, semantic: 0.8, factual: 0.85, consistency: 0.85 },
      riskFactors: [],
      explanation: { summary: '', reasoning: [], evidence: [], relatedRequirements: [] },
    };

    const result = customRouter.route(estimation);

    expect(result.decision).toBe('verify');
  });

  it('should include explanation', () => {
    const estimation = {
      score: 0.7,
      breakdown: { syntactic: 0.7, semantic: 0.7, factual: 0.7, consistency: 0.7 },
      riskFactors: [],
      explanation: { summary: '', reasoning: [], evidence: [], relatedRequirements: [] },
    };

    const result = router.route(estimation);

    expect(result.explanation).toBeDefined();
    expect(result.explanation.summary).toContain('Verification required');
    expect(result.explanation.reasoning.length).toBeGreaterThan(0);
  });

  it('should track regeneration attempts', () => {
    expect(router.isRegenerationLimitReached(0)).toBe(false);
    expect(router.isRegenerationLimitReached(2)).toBe(false);
    expect(router.isRegenerationLimitReached(3)).toBe(true);
    expect(router.isRegenerationLimitReached(5)).toBe(true);
  });
});

// === ErrorHandler Tests ===

describe('ErrorHandler', () => {
  let handler: ErrorHandler;

  beforeEach(() => {
    handler = new ErrorHandler();
  });

  it('should classify errors correctly', () => {
    const typeError = new TypeError('Cannot read property x');
    const networkError = new Error('Network timeout');
    const validationError = new Error('Validation failed');

    expect(handler.classifyError(typeError).severity).toBe('fatal');
    expect(handler.classifyError(networkError).severity).toBe('degraded');
    expect(handler.classifyError(validationError).severity).toBe('recoverable');
  });

  it('should handle recoverable errors', async () => {
    const error = new Error('Resource not found');

    const result = await handler.handleError(error, {
      component: 'TestComponent',
      operation: 'testOperation',
    });

    expect(result).toBeDefined();
    expect(result.auditEntry).toBeDefined();
    expect(result.explanation).toBeDefined();
  });

  it('should log errors to audit', async () => {
    const error = new Error('Test error');

    await handler.handleError(error, {
      component: 'TestComponent',
      operation: 'testOperation',
    });

    const auditLog = handler.getAuditLog();
    expect(auditLog.length).toBe(1);
    expect(auditLog[0].component).toBe('TestComponent');
    expect(auditLog[0].operation).toBe('testOperation');
  });

  it('should clear audit log', async () => {
    const error = new Error('Test error');

    await handler.handleError(error, {
      component: 'TestComponent',
      operation: 'testOperation',
    });

    handler.clearAuditLog();

    expect(handler.getAuditLog()).toHaveLength(0);
  });

  it('should select appropriate fallback', async () => {
    const error = new Error('Network timeout');

    const result = await handler.handleError(error, {
      component: 'HallucinationDetector',
      operation: 'detect',
    });

    if (result.success && result.fallbackUsed) {
      expect(result.fallbackUsed).toBe('skip_hallucination_check');
    }
  });
});

// === Integration Tests ===

describe('Symbolic Pipeline Integration', () => {
  it('should create complete pipeline', () => {
    const pipeline = createSymbolicPipeline();

    expect(pipeline.filter).toBeInstanceOf(SemanticCodeFilterPipeline);
    expect(pipeline.hallucinationDetector).toBeInstanceOf(HallucinationDetector);
    expect(pipeline.constitutionRegistry).toBeInstanceOf(ConstitutionRuleRegistry);
    expect(pipeline.confidenceEstimator).toBeInstanceOf(ConfidenceEstimator);
    expect(pipeline.router).toBeInstanceOf(ConfidenceBasedRouter);
    expect(pipeline.errorHandler).toBeInstanceOf(ErrorHandler);
  });

  it('should process code through complete pipeline', async () => {
    const input: FilterInput = {
      candidates: [
        createTestCandidate(`
function greet(name: string): string {
  return \`Hello, \${name}!\`;
}
`),
      ],
      projectContext: createTestContext(createTestSymbols()),
    };

    const { filterOutput, routingResults } = await processSymbolic(input);

    expect(filterOutput).toBeDefined();
    expect(filterOutput.filteredCandidates).toHaveLength(1);
    expect(routingResults).toHaveLength(1);
    expect(['accept', 'verify', 'regenerate']).toContain(routingResults[0].decision);
  });

  it('should handle multiple candidates', async () => {
    const input: FilterInput = {
      candidates: [
        createTestCandidate('const a = 1;'),
        createTestCandidate('const b = 2;'),
        createTestCandidate('const c = 3;'),
      ],
      projectContext: createTestContext(),
    };

    const { filterOutput, routingResults } = await processSymbolic(input);

    expect(filterOutput.filteredCandidates).toHaveLength(3);
    expect(routingResults).toHaveLength(3);
  });
});
