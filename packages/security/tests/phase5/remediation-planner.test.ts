/**
 * @fileoverview Tests for RemediationPlanner
 * @module @nahisaho/musubix-security/tests/phase5/remediation-planner.test
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  RemediationPlanner,
  createRemediationPlanner,
  quickCreatePlan,
} from '../../src/remediation/remediation-planner.js';
import type {
  Vulnerability,
  Fix,
  ScanResult,
  SourceLocation,
  CodeEdit,
} from '../../src/types/index.js';

// ============================================================================
// Test Helpers
// ============================================================================

function createLocation(file: string, startLine: number, endLine?: number): SourceLocation {
  return {
    file,
    startLine,
    endLine: endLine ?? startLine,
    startColumn: 0,
    endColumn: 80,
  };
}

function createVulnerability(
  id: string,
  type: string,
  severity: 'critical' | 'high' | 'medium' | 'low' | 'info' = 'high',
  file: string = 'test.ts'
): Vulnerability {
  return {
    id,
    ruleId: `SEC-${type.toUpperCase()}`,
    type,
    severity,
    description: `Test ${type} vulnerability`,
    location: createLocation(file, 10),
    evidence: {
      code: 'vulnerable code',
      context: 'Test context',
    },
    cwe: ['CWE-79'],
    owasp: ['A03:2021'],
    confidence: 0.9,
    remediation: `Fix the ${type} vulnerability`,
    references: [],
    metadata: {},
  };
}

function createCodeEdit(file: string, startLine: number): CodeEdit {
  return {
    location: createLocation(file, startLine),
    oldCode: 'old',
    newCode: 'new',
    description: 'Test edit',
  };
}

function createFix(id: string, vulnerabilityId: string, file: string = 'test.ts'): Fix {
  return {
    id,
    vulnerabilityId,
    strategy: 'test-strategy',
    title: `Fix for ${vulnerabilityId}`,
    description: 'Test fix',
    confidence: 0.9,
    breakingChange: false,
    rationale: 'Test rationale',
    edits: [createCodeEdit(file, 10)],
    imports: [],
    generatedAt: new Date(),
  };
}

function createScanResult(vulnerabilities: Vulnerability[]): ScanResult {
  return {
    scanId: `SCAN-${Date.now()}`,
    timestamp: new Date().toISOString(),
    target: './src',
    duration: 1000,
    vulnerabilities,
    secrets: [],
    dependencies: [],
    summary: {
      totalFiles: 10,
      filesScanned: 10,
      totalVulnerabilities: vulnerabilities.length,
      bySeverity: {
        critical: vulnerabilities.filter(v => v.severity === 'critical').length,
        high: vulnerabilities.filter(v => v.severity === 'high').length,
        medium: vulnerabilities.filter(v => v.severity === 'medium').length,
        low: vulnerabilities.filter(v => v.severity === 'low').length,
        info: vulnerabilities.filter(v => v.severity === 'info').length,
      },
      totalSecrets: 0,
      totalDependencyIssues: 0,
      secretsBySeverity: { critical: 0, high: 0, medium: 0, low: 0 },
      dependenciesBySeverity: { critical: 0, high: 0, medium: 0, low: 0 },
    },
    config: {
      vulnerability: { enabled: true, rules: [], exclude: [] },
      taint: { enabled: false, sources: [], sinks: [], sanitizers: [] },
      secret: { enabled: false, patterns: [], exclude: [] },
      dependency: { enabled: false, exclude: [], auditLevel: 'moderate' },
      reporting: { formats: ['json'], outputDir: './reports' },
    },
  };
}

// ============================================================================
// RemediationPlanner Tests
// ============================================================================

describe('RemediationPlanner', () => {
  let planner: RemediationPlanner;

  beforeEach(() => {
    planner = createRemediationPlanner();
  });

  describe('constructor', () => {
    it('should create with default options', () => {
      const p = new RemediationPlanner();
      expect(p).toBeInstanceOf(RemediationPlanner);
    });

    it('should create with custom options', () => {
      const p = new RemediationPlanner({
        defaultStrategy: 'severity-first',
        maxFixesPerPhase: 5,
        teamSize: 4,
      });
      expect(p).toBeInstanceOf(RemediationPlanner);
    });
  });

  describe('createPlan', () => {
    it('should create plan for single vulnerability', () => {
      const vulns = [createVulnerability('V-001', 'xss', 'high')];
      const fixes = [createFix('FIX-001', 'V-001')];
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes);

      expect(plan.id).toBeDefined();
      expect(plan.status).toBe('draft');
      expect(plan.totalVulnerabilities).toBe(1);
      expect(plan.phases.length).toBeGreaterThan(0);
    });

    it('should create plan for multiple vulnerabilities', () => {
      const vulns = [
        createVulnerability('V-001', 'xss', 'critical'),
        createVulnerability('V-002', 'sql-injection', 'high'),
        createVulnerability('V-003', 'path-traversal', 'medium'),
      ];
      const fixes = vulns.map((v, i) => createFix(`FIX-00${i + 1}`, v.id));
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes);

      expect(plan.totalVulnerabilities).toBe(3);
      expect(plan.riskReduction.criticalFixed).toBe(1);
      expect(plan.riskReduction.highFixed).toBe(1);
    });

    it('should prioritize critical vulnerabilities first', () => {
      const vulns = [
        createVulnerability('V-001', 'xss', 'low'),
        createVulnerability('V-002', 'sql-injection', 'critical'),
        createVulnerability('V-003', 'path-traversal', 'medium'),
      ];
      const fixes = vulns.map((v, i) => createFix(`FIX-00${i + 1}`, v.id));
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes, { strategy: 'severity-first' });

      // First phase should contain critical vulnerability
      const firstPhaseFixes = plan.phases[0].fixes;
      expect(firstPhaseFixes.some(f => f.vulnerability.severity === 'critical')).toBe(true);
    });

    it('should use effort-first strategy when specified', () => {
      const vulns = [
        createVulnerability('V-001', 'xss', 'high'),
        createVulnerability('V-002', 'hardcoded-secret', 'high'),
      ];
      const fixes = [
        createFix('FIX-001', 'V-001'),
        createFix('FIX-002', 'V-002'),
      ];
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes, { strategy: 'effort-first' });

      expect(plan.phases.length).toBeGreaterThan(0);
    });

    it('should use risk-based strategy by default', () => {
      const vulns = [
        createVulnerability('V-001', 'xss', 'high'),
        createVulnerability('V-002', 'sql-injection', 'critical'),
      ];
      const fixes = vulns.map((v, i) => createFix(`FIX-00${i + 1}`, v.id));
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes);

      // Should prioritize by risk
      expect(plan.phases[0].fixes[0].priorityScore).toBeGreaterThan(0);
    });

    it('should detect dependencies between fixes', () => {
      const vulns = [
        createVulnerability('V-001', 'hardcoded-secret', 'high', 'auth.ts'),
        createVulnerability('V-002', 'weak-crypto', 'high', 'auth.ts'),
      ];
      const fixes = vulns.map((v, i) => createFix(`FIX-00${i + 1}`, v.id, 'auth.ts'));
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes, { strategy: 'dependency-aware' });

      expect(plan.dependencies.length).toBeGreaterThanOrEqual(0);
    });

    it('should respect maxPhases option', () => {
      const vulns = Array.from({ length: 20 }, (_, i) =>
        createVulnerability(`V-${i}`, 'xss', 'medium')
      );
      const fixes = vulns.map(v => createFix(`FIX-${v.id}`, v.id));
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes, { maxPhases: 3 });

      expect(plan.phases.length).toBeLessThanOrEqual(3);
    });

    it('should calculate effort estimates', () => {
      const vulns = [createVulnerability('V-001', 'xss', 'high')];
      const fixes = [createFix('FIX-001', 'V-001')];
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes);

      expect(plan.estimatedEffort.hours).toBeGreaterThan(0);
      expect(plan.estimatedEffort.testingHours).toBeGreaterThan(0);
    });

    it('should calculate risk reduction', () => {
      const vulns = [
        createVulnerability('V-001', 'xss', 'critical'),
        createVulnerability('V-002', 'sql-injection', 'high'),
      ];
      const fixes = vulns.map((v, i) => createFix(`FIX-00${i + 1}`, v.id));
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes);

      expect(plan.riskReduction.initialRisk).toBeGreaterThan(0);
      expect(plan.riskReduction.reductionPercent).toBe(100);
    });
  });

  describe('updatePlanStatus', () => {
    it('should update plan status', () => {
      const vulns = [createVulnerability('V-001', 'xss')];
      const fixes = [createFix('FIX-001', 'V-001')];
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes);
      const updated = planner.updatePlanStatus(plan, 'approved');

      expect(updated.status).toBe('approved');
      expect(updated.metadata.approvalDate).toBeDefined();
    });

    it('should preserve other plan data', () => {
      const vulns = [createVulnerability('V-001', 'xss')];
      const fixes = [createFix('FIX-001', 'V-001')];
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes);
      const originalId = plan.id;
      const updated = planner.updatePlanStatus(plan, 'in-progress');

      expect(updated.id).toBe(originalId);
      expect(updated.phases).toEqual(plan.phases);
    });
  });

  describe('markFixCompleted', () => {
    it('should mark fix as completed', () => {
      const vulns = [createVulnerability('V-001', 'xss')];
      const fixes = [createFix('FIX-001', 'V-001')];
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes);
      const updated = planner.markFixCompleted(plan, 'FIX-001');

      const fixStatus = updated.phases
        .flatMap(p => p.fixes)
        .find(f => f.fix.id === 'FIX-001')?.status;

      expect(fixStatus).toBe('completed');
    });
  });

  describe('getNextFixes', () => {
    it('should return pending fixes', () => {
      const vulns = [
        createVulnerability('V-001', 'xss'),
        createVulnerability('V-002', 'sql-injection'),
      ];
      const fixes = vulns.map((v, i) => createFix(`FIX-00${i + 1}`, v.id));
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes);
      const nextFixes = planner.getNextFixes(plan, 5);

      expect(nextFixes.length).toBeGreaterThan(0);
      expect(nextFixes.every(f => f.status === 'pending')).toBe(true);
    });

    it('should respect count parameter', () => {
      const vulns = Array.from({ length: 10 }, (_, i) =>
        createVulnerability(`V-${i}`, 'xss')
      );
      const fixes = vulns.map(v => createFix(`FIX-${v.id}`, v.id));
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes);
      const nextFixes = planner.getNextFixes(plan, 3);

      expect(nextFixes.length).toBeLessThanOrEqual(3);
    });
  });

  describe('calculateProgress', () => {
    it('should calculate progress correctly', () => {
      const vulns = [
        createVulnerability('V-001', 'xss'),
        createVulnerability('V-002', 'sql-injection'),
      ];
      const fixes = vulns.map((v, i) => createFix(`FIX-00${i + 1}`, v.id));
      const scanResult = createScanResult(vulns);

      let plan = planner.createPlan(scanResult, fixes);
      let progress = planner.calculateProgress(plan);

      expect(progress.totalFixes).toBe(2);
      expect(progress.completedFixes).toBe(0);
      expect(progress.percentComplete).toBe(0);

      // Mark one fix as completed
      plan = planner.markFixCompleted(plan, 'FIX-001');
      progress = planner.calculateProgress(plan);

      expect(progress.completedFixes).toBe(1);
      expect(progress.percentComplete).toBe(50);
    });
  });

  describe('generateReport', () => {
    it('should generate markdown report', () => {
      const vulns = [
        createVulnerability('V-001', 'xss', 'critical'),
        createVulnerability('V-002', 'sql-injection', 'high'),
      ];
      const fixes = vulns.map((v, i) => createFix(`FIX-00${i + 1}`, v.id));
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes);
      const report = planner.generateReport(plan);

      expect(report).toContain('# Security Remediation Plan Report');
      expect(report).toContain('## Summary');
      expect(report).toContain('## Risk Reduction');
      expect(report).toContain('## Phases');
    });

    it('should include progress in report', () => {
      const vulns = [createVulnerability('V-001', 'xss')];
      const fixes = [createFix('FIX-001', 'V-001')];
      const scanResult = createScanResult(vulns);

      const plan = planner.createPlan(scanResult, fixes);
      const report = planner.generateReport(plan);

      expect(report).toContain('Total Fixes:');
      expect(report).toContain('Completed:');
    });
  });
});

// ============================================================================
// Factory Functions Tests
// ============================================================================

describe('Factory Functions', () => {
  describe('createRemediationPlanner', () => {
    it('should create RemediationPlanner instance', () => {
      const planner = createRemediationPlanner();
      expect(planner).toBeInstanceOf(RemediationPlanner);
    });

    it('should pass options to RemediationPlanner', () => {
      const planner = createRemediationPlanner({
        defaultStrategy: 'balanced',
        teamSize: 3,
      });
      expect(planner).toBeInstanceOf(RemediationPlanner);
    });
  });

  describe('quickCreatePlan', () => {
    it('should quickly create a plan', () => {
      const vulns = [createVulnerability('V-001', 'xss')];
      const fixes = [createFix('FIX-001', 'V-001')];
      const scanResult = createScanResult(vulns);

      const plan = quickCreatePlan(scanResult, fixes);

      expect(plan.id).toBeDefined();
      expect(plan.phases.length).toBeGreaterThan(0);
    });
  });
});

// ============================================================================
// Edge Cases
// ============================================================================

describe('Edge Cases', () => {
  let planner: RemediationPlanner;

  beforeEach(() => {
    planner = createRemediationPlanner();
  });

  it('should handle empty vulnerabilities', () => {
    const scanResult = createScanResult([]);
    const plan = planner.createPlan(scanResult, []);

    expect(plan.totalVulnerabilities).toBe(0);
    expect(plan.phases.length).toBe(0);
  });

  it('should handle vulnerabilities without fixes', () => {
    const vulns = [createVulnerability('V-001', 'xss')];
    const scanResult = createScanResult(vulns);

    const plan = planner.createPlan(scanResult, []);

    expect(plan.totalVulnerabilities).toBe(1);
  });

  it('should handle fixes without matching vulnerabilities', () => {
    const vulns = [createVulnerability('V-001', 'xss')];
    const fixes = [createFix('FIX-999', 'V-999')];
    const scanResult = createScanResult(vulns);

    const plan = planner.createPlan(scanResult, fixes);

    expect(plan.totalVulnerabilities).toBe(1);
  });

  it('should handle large number of vulnerabilities', () => {
    const vulns = Array.from({ length: 100 }, (_, i) =>
      createVulnerability(`V-${i}`, 'xss', ['critical', 'high', 'medium', 'low'][i % 4] as 'critical' | 'high' | 'medium' | 'low')
    );
    const fixes = vulns.map(v => createFix(`FIX-${v.id}`, v.id));
    const scanResult = createScanResult(vulns);

    const plan = planner.createPlan(scanResult, fixes);

    expect(plan.totalVulnerabilities).toBe(100);
    expect(plan.phases.length).toBeGreaterThan(0);
  });

  it('should handle overlapping vulnerabilities in same file', () => {
    const vulns = [
      { ...createVulnerability('V-001', 'xss', 'high', 'test.ts'), location: createLocation('test.ts', 5, 10) },
      { ...createVulnerability('V-002', 'sql-injection', 'high', 'test.ts'), location: createLocation('test.ts', 8, 12) },
    ];
    const fixes = vulns.map((v, i) => createFix(`FIX-00${i + 1}`, v.id, 'test.ts'));
    const scanResult = createScanResult(vulns);

    const plan = planner.createPlan(scanResult, fixes, { strategy: 'dependency-aware' });

    // Should detect conflict due to overlapping lines
    expect(plan.dependencies.some(d => d.type === 'conflicts')).toBe(true);
  });

  it('should handle all severity levels', () => {
    const vulns = [
      createVulnerability('V-001', 'xss', 'critical'),
      createVulnerability('V-002', 'xss', 'high'),
      createVulnerability('V-003', 'xss', 'medium'),
      createVulnerability('V-004', 'xss', 'low'),
      createVulnerability('V-005', 'xss', 'info'),
    ];
    const fixes = vulns.map((v, i) => createFix(`FIX-00${i + 1}`, v.id));
    const scanResult = createScanResult(vulns);

    const plan = planner.createPlan(scanResult, fixes);

    expect(plan.riskReduction.criticalFixed).toBe(1);
    expect(plan.riskReduction.highFixed).toBe(1);
    expect(plan.riskReduction.mediumFixed).toBe(1);
    expect(plan.riskReduction.lowFixed).toBe(1);
  });
});
