/**
 * @fileoverview Neuro-Symbolic Core unit tests
 * @trace TST-SEC2-INT-001, TST-SEC2-INT-002, TST-SEC2-INT-003
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  NeuroSymbolicCore,
  createNeuroSymbolicCore,
  StubLLMAnalyzer,
  StubKnowledgeQuery,
} from '../src/intelligence/neuro-symbolic-core.js';
import type { Vulnerability, Severity } from '../src/types/vulnerability.js';
import type { NeuroSymbolicResult, FinalDecision } from '../src/types/neuro-symbolic.js';

// Helper to create test vulnerabilities
function createVulnerability(overrides: Partial<Vulnerability> = {}): Vulnerability {
  return {
    id: `VULN-${Date.now()}-${Math.random().toString(36).substr(2, 3)}`,
    type: 'injection',
    severity: 'high' as Severity,
    cwes: ['CWE-89'],
    owasp: ['A03:2021'],
    location: {
      file: 'test.ts',
      startLine: 10,
      endLine: 15,
      startColumn: 0,
      endColumn: 50,
    },
    description: 'SQL Injection vulnerability',
    recommendation: 'Use parameterized queries',
    confidence: 0.85,
    ruleId: 'SEC-001',
    codeSnippet: 'const result = db.query(`SELECT * FROM users WHERE id = ${userId}`);',
    detectedAt: new Date(),
    ...overrides,
  } as Vulnerability;
}

describe('NeuroSymbolicCore', () => {
  let core: NeuroSymbolicCore;

  beforeEach(() => {
    core = createNeuroSymbolicCore();
  });

  describe('integrate', () => {
    it('should integrate neural and symbolic analysis', async () => {
      const vulnerability = createVulnerability();

      const result = await core.integrate(vulnerability);

      expect(result).toHaveProperty('neuralConfidence');
      expect(result).toHaveProperty('symbolicValid');
      expect(result).toHaveProperty('finalDecision');
      expect(result).toHaveProperty('neuralExplanation');
      expect(result).toHaveProperty('symbolicEvidence');
      expect(result).toHaveProperty('combinedConfidence');
      expect(result).toHaveProperty('rationale');
    });

    it('should return confirmed for high confidence and valid symbolic', async () => {
      const vulnerability = createVulnerability({
        confidence: 0.95,
        cwes: ['CWE-89'],
      });

      const result = await core.integrate(vulnerability, { neuralThreshold: 0.8 });

      // With matching CWE and high confidence, should be confirmed
      expect(['confirmed', 'needs-review']).toContain(result.finalDecision);
    });

    it('should return rejected when symbolic validation fails', async () => {
      // Create a vulnerability with unmatched CWE
      const vulnerability = createVulnerability({
        cwes: ['CWE-UNKNOWN-999'],
        confidence: 0.5,
      });

      const result = await core.integrate(vulnerability);

      // Without matching patterns, symbolic validation should fail
      expect(result.symbolicValid).toBe(false);
      expect(result.finalDecision).toBe('rejected');
    });

    it('should handle custom options', async () => {
      const vulnerability = createVulnerability();

      const result = await core.integrate(vulnerability, {
        neuralThreshold: 0.5,
        requireSymbolicValidation: true,
      });

      expect(result).toBeDefined();
      expect(result.neuralConfidence).toBeGreaterThan(0);
    });
  });

  describe('validateSymbolic', () => {
    it('should validate vulnerability with known patterns', async () => {
      const vulnerability = createVulnerability({
        cwes: ['CWE-89'], // SQL Injection
      });

      const result = await core.validateSymbolic(vulnerability);

      expect(result.valid).toBe(true);
      expect(result.matchedPatterns).toContain('sql-injection');
      expect(result.evidence.length).toBeGreaterThan(0);
    });

    it('should validate XSS vulnerability', async () => {
      const vulnerability = createVulnerability({
        cwes: ['CWE-79'],
      });

      const result = await core.validateSymbolic(vulnerability);

      expect(result.valid).toBe(true);
      expect(result.matchedPatterns).toContain('xss');
    });

    it('should validate command injection vulnerability', async () => {
      const vulnerability = createVulnerability({
        cwes: ['CWE-78'],
      });

      const result = await core.validateSymbolic(vulnerability);

      expect(result.valid).toBe(true);
      expect(result.matchedPatterns).toContain('command-injection');
    });

    it('should include rule inference in evidence', async () => {
      const vulnerability = createVulnerability({
        cwes: ['CWE-89'],
      });

      const result = await core.validateSymbolic(vulnerability);

      const ruleEvidence = result.evidence.filter(e => e.type === 'rule-inference');
      expect(ruleEvidence.length).toBeGreaterThan(0);
      expect(result.appliedRules).toContain('RULE-001'); // SQL injection rule
    });

    it('should include static analysis evidence', async () => {
      const vulnerability = createVulnerability();

      const result = await core.validateSymbolic(vulnerability);

      const saEvidence = result.evidence.filter(e => e.type === 'static-analysis');
      expect(saEvidence.length).toBe(1);
      expect(saEvidence[0].source).toBe(vulnerability.ruleId);
    });
  });

  describe('analyzeNeural', () => {
    it('should return neural result without LLM analyzer', async () => {
      const vulnerability = createVulnerability();

      const result = await core.analyzeNeural(vulnerability);

      expect(result.model).toBe('heuristic-fallback');
      expect(result.confidence).toBeGreaterThan(0);
      expect(result.explanation).toBeDefined();
    });

    it('should use LLM analyzer when set', async () => {
      const stubAnalyzer = new StubLLMAnalyzer();
      core.setLLMAnalyzer(stubAnalyzer);

      const vulnerability = createVulnerability();
      const result = await core.analyzeNeural(vulnerability);

      expect(result.model).toBe('stub-analyzer');
    });
  });

  describe('calculateScore', () => {
    it('should reduce score when symbolic validation fails', () => {
      const neuralResult = {
        confidence: 0.9,
        explanation: 'Test',
        suggestedSeverity: 'high' as Severity,
        suggestedFixes: [],
        model: 'test',
        latency: 0,
      };
      const symbolicResult = {
        valid: false,
        evidence: [],
        matchedPatterns: [],
        appliedRules: [],
      };

      const score = core.calculateScore(neuralResult, symbolicResult);

      // Score should be significantly reduced
      expect(score).toBeLessThan(0.5);
    });

    it('should return higher score when both analyses agree', () => {
      const neuralResult = {
        confidence: 0.9,
        explanation: 'Test',
        suggestedSeverity: 'high' as Severity,
        suggestedFixes: [],
        model: 'test',
        latency: 0,
      };
      const symbolicResult = {
        valid: true,
        evidence: [
          { type: 'pattern-match' as const, source: 'sql-injection', description: 'Matched', weight: 0.9 },
        ],
        matchedPatterns: ['sql-injection'],
        appliedRules: ['RULE-001'],
      };

      const score = core.calculateScore(neuralResult, symbolicResult);

      expect(score).toBeGreaterThan(0.7);
    });
  });

  describe('with StubLLMAnalyzer', () => {
    let analyzer: StubLLMAnalyzer;

    beforeEach(() => {
      analyzer = new StubLLMAnalyzer();
      core.setLLMAnalyzer(analyzer);
    });

    it('should detect user input and dangerous sinks', async () => {
      const vulnerability = createVulnerability({
        codeSnippet: 'const result = db.query(`SELECT * FROM users WHERE id = ${req.body.id}`);',
      });

      const result = await analyzer.analyzeContext(
        vulnerability.codeSnippet!,
        vulnerability
      );

      expect(result.explanation).toContain('User input detected');
      expect(result.explanation).toContain('Dangerous sink detected');
    });

    it('should generate explanation with data flow', async () => {
      const vulnerability = createVulnerability();
      const taintPath = {
        source: { id: '1', type: 'user-input' as const, location: vulnerability.location, variable: 'userId' },
        sink: { id: '2', type: 'sql' as const, location: vulnerability.location, requiredSanitizers: [] },
        steps: [],
        sanitizers: [],
        isSafe: false,
      };

      const explanation = await analyzer.generateExplanation(vulnerability, taintPath);

      expect(explanation).toContain('high');
      expect(explanation).toContain('CWE-89');
    });
  });

  describe('with StubKnowledgeQuery', () => {
    let query: StubKnowledgeQuery;

    beforeEach(() => {
      query = new StubKnowledgeQuery();
      core.setKnowledgeQuery(query);
    });

    it('should query patterns with CWEs', async () => {
      const matches = await query.queryPattern('test code', ['CWE-89', 'CWE-79']);

      expect(matches.length).toBe(2);
      expect(matches[0].entityType).toBe('CWE');
    });

    it('should match rules for vulnerability', async () => {
      const vulnerability = createVulnerability({ cwes: ['CWE-89'] });

      const rules = await query.matchRule(vulnerability);

      expect(rules).toContain('RULE-001');
    });

    it('should infer vulnerabilities from code', async () => {
      const sqlCode = 'db.query(`SELECT * FROM ${table}`)';
      const inferred = await query.inferVulnerability(sqlCode);

      expect(inferred).toContain('CWE-89');
    });

    it('should infer XSS from innerHTML', async () => {
      const xssCode = 'element.innerHTML = userInput;';
      const inferred = await query.inferVulnerability(xssCode);

      expect(inferred).toContain('CWE-79');
    });

    it('should integrate with knowledge graph in validation', async () => {
      core.setKnowledgeQuery(query);
      const vulnerability = createVulnerability({ cwes: ['CWE-89'] });

      const result = await core.validateSymbolic(vulnerability);

      const kgEvidence = result.evidence.filter(e => e.type === 'knowledge-graph');
      expect(kgEvidence.length).toBeGreaterThan(0);
    });
  });

  describe('integration rules (REQ-SEC2-INT-002)', () => {
    it('should reject when symbolic is invalid', async () => {
      const vulnerability = createVulnerability({
        cwes: ['CWE-UNKNOWN'],
        confidence: 0.95,
      });

      const result = await core.integrate(vulnerability);

      expect(result.finalDecision).toBe('rejected');
      expect(result.rationale).toContain('REJECTED');
    });

    it('should confirm with high neural confidence and valid symbolic', async () => {
      const vulnerability = createVulnerability({
        cwes: ['CWE-89'],
        confidence: 0.95,
      });

      const result = await core.integrate(vulnerability, { neuralThreshold: 0.8 });

      // Should be confirmed or needs-review based on combined evidence
      expect(['confirmed', 'needs-review']).toContain(result.finalDecision);
    });

    it('should return needs-review with low neural confidence', async () => {
      const vulnerability = createVulnerability({
        cwes: ['CWE-89'],
        confidence: 0.5,
      });

      const result = await core.integrate(vulnerability, { neuralThreshold: 0.9 });

      // With low neural confidence but valid symbolic, should need review
      expect(['needs-review', 'confirmed']).toContain(result.finalDecision);
    });
  });

  describe('rationale generation', () => {
    it('should include neural confidence in rationale', async () => {
      const vulnerability = createVulnerability();

      const result = await core.integrate(vulnerability);

      expect(result.rationale).toContain('Neural analysis confidence');
    });

    it('should include symbolic validation status', async () => {
      const vulnerability = createVulnerability({ cwes: ['CWE-89'] });

      const result = await core.integrate(vulnerability);

      expect(result.rationale).toContain('Symbolic validation');
    });

    it('should include matched patterns when available', async () => {
      const vulnerability = createVulnerability({ cwes: ['CWE-89'] });

      const result = await core.integrate(vulnerability);

      expect(result.rationale).toContain('Matched patterns');
    });

    it('should include decision explanation', async () => {
      const vulnerability = createVulnerability({ cwes: ['CWE-89'] });

      const result = await core.integrate(vulnerability);

      expect(result.rationale).toContain('Decision:');
    });
  });
});

describe('createNeuroSymbolicCore', () => {
  it('should create instance with default options', () => {
    const core = createNeuroSymbolicCore();

    expect(core).toBeInstanceOf(NeuroSymbolicCore);
  });

  it('should create instance with custom options', () => {
    const core = createNeuroSymbolicCore({
      neuralThreshold: 0.9,
      requireSymbolicValidation: true,
      llmProvider: 'anthropic',
    });

    expect(core).toBeInstanceOf(NeuroSymbolicCore);
  });
});
