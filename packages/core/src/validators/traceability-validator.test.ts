/**
 * Traceability Validator Tests
 *
 * @see TSK-VAL-002
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { mkdir, writeFile, rm } from 'fs/promises';
import { join } from 'path';
import {
  TraceabilityValidator,
  validateTraceability,
} from './traceability-validator.js';

const TEST_DIR = join(process.cwd(), 'tmp', 'traceability-test');
const SPECS_DIR = join(TEST_DIR, 'storage', 'specs');
const DESIGN_DIR = join(TEST_DIR, 'storage', 'design');

describe('TraceabilityValidator', () => {
  beforeEach(async () => {
    await mkdir(SPECS_DIR, { recursive: true });
    await mkdir(DESIGN_DIR, { recursive: true });
  });

  afterEach(async () => {
    await rm(TEST_DIR, { recursive: true, force: true });
  });

  describe('extractArtifacts', () => {
    it('should extract requirements from markdown files', async () => {
      await writeFile(
        join(SPECS_DIR, 'requirements.md'),
        `# Requirements

## REQ-001: User Authentication

THE system SHALL authenticate users with username and password.

## REQ-002: Session Management

WHEN user logs in, THE system SHALL create a session.
`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.requirements).toHaveLength(2);
      expect(result.requirements[0].id).toBe('REQ-001');
      expect(result.requirements[1].id).toBe('REQ-002');
    });

    it('should extract designs from markdown files', async () => {
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `# Design

## DES-001: Authentication Module

Implements REQ-001.

## DES-002: Session Store

Implements REQ-002.
`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.designs).toHaveLength(2);
      expect(result.designs[0].id).toBe('DES-001');
      expect(result.designs[1].id).toBe('DES-002');
    });

    it('should handle empty directories', async () => {
      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.requirements).toHaveLength(0);
      expect(result.designs).toHaveLength(0);
      expect(result.valid).toBe(true); // 100% coverage of 0 requirements
    });
  });

  describe('extractLinks', () => {
    it('should extract traces from design to requirements', async () => {
      await writeFile(
        join(SPECS_DIR, 'requirements.md'),
        `## REQ-001: Feature A`
      );

      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001: Implementation of Feature A

This design traces to REQ-001.
`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.links).toHaveLength(1);
      expect(result.links[0]).toMatchObject({
        source: 'DES-001',
        target: 'REQ-001',
        type: 'traces-to',
      });
    });

    it('should find multiple links in one design', async () => {
      await writeFile(
        join(SPECS_DIR, 'requirements.md'),
        `## REQ-001: Feature A
## REQ-002: Feature B`
      );

      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001: Combined Implementation

Implements both REQ-001 and REQ-002.
`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.links).toHaveLength(2);
      expect(result.links.map((l) => l.target)).toContain('REQ-001');
      expect(result.links.map((l) => l.target)).toContain('REQ-002');
    });
  });

  describe('orphan detection', () => {
    it('should detect orphan requirements', async () => {
      await writeFile(
        join(SPECS_DIR, 'requirements.md'),
        `## REQ-001: Feature A
## REQ-002: Feature B`
      );

      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001: Implementation of Feature A

Traces to REQ-001 only.
`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.orphanRequirements).toHaveLength(1);
      expect(result.orphanRequirements[0].id).toBe('REQ-002');
    });

    it('should detect orphan designs', async () => {
      await writeFile(
        join(SPECS_DIR, 'requirements.md'),
        `## REQ-001: Feature A`
      );

      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001: Implementation of Feature A

Traces to REQ-001.

## DES-002: Some Utility

No requirement link here.
`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.orphanDesigns).toHaveLength(1);
      expect(result.orphanDesigns[0].id).toBe('DES-002');
    });
  });

  describe('coverage calculation', () => {
    it('should calculate 100% coverage when all requirements traced', async () => {
      await writeFile(join(SPECS_DIR, 'requirements.md'), `## REQ-001: Feature`);
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001
Traces to REQ-001.`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.coverage.percentage).toBe(100);
      expect(result.coverage.requirementsCovered).toBe(1);
      expect(result.coverage.requirementsTotal).toBe(1);
    });

    it('should calculate 50% coverage correctly', async () => {
      await writeFile(
        join(SPECS_DIR, 'requirements.md'),
        `## REQ-001: Feature A
## REQ-002: Feature B`
      );
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001
Traces to REQ-001.`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.coverage.percentage).toBe(50);
      expect(result.coverage.requirementsCovered).toBe(1);
      expect(result.coverage.requirementsTotal).toBe(2);
    });

    it('should handle zero requirements', async () => {
      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.coverage.percentage).toBe(100);
      expect(result.coverage.requirementsTotal).toBe(0);
    });
  });

  describe('validation', () => {
    it('should pass with full coverage and no orphans', async () => {
      await writeFile(join(SPECS_DIR, 'requirements.md'), `## REQ-001: Feature`);
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001
Traces to REQ-001.`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.valid).toBe(true);
    });

    it('should fail when coverage below minimum', async () => {
      await writeFile(
        join(SPECS_DIR, 'requirements.md'),
        `## REQ-001: Feature A
## REQ-002: Feature B
## REQ-003: Feature C
## REQ-004: Feature D
## REQ-005: Feature E`
      );
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001
Traces to REQ-001.`
      );

      const validator = new TraceabilityValidator({ minCoverage: 80 });
      const result = await validator.validate(TEST_DIR);

      expect(result.valid).toBe(false);
      expect(result.coverage.percentage).toBe(20);
      expect(result.issues.some((i) => i.code === 'LOW_COVERAGE')).toBe(true);
    });

    it('should pass when coverage meets minimum', async () => {
      await writeFile(
        join(SPECS_DIR, 'requirements.md'),
        `## REQ-001: A
## REQ-002: B
## REQ-003: C
## REQ-004: D
## REQ-005: E`
      );
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001: Impl
REQ-001, REQ-002, REQ-003, REQ-004, REQ-005`
      );

      const validator = new TraceabilityValidator({ minCoverage: 80 });
      const result = await validator.validate(TEST_DIR);

      expect(result.valid).toBe(true);
      expect(result.coverage.percentage).toBe(100);
    });

    it('should fail when requireFullCoverage is true and not 100%', async () => {
      await writeFile(
        join(SPECS_DIR, 'requirements.md'),
        `## REQ-001: A
## REQ-002: B`
      );
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001
REQ-001`
      );

      const validator = new TraceabilityValidator({ requireFullCoverage: true });
      const result = await validator.validate(TEST_DIR);

      expect(result.valid).toBe(false);
      expect(result.issues.some((i) => i.code === 'INCOMPLETE_COVERAGE')).toBe(
        true
      );
    });
  });

  describe('issues', () => {
    it('should generate warnings for orphan requirements', async () => {
      await writeFile(join(SPECS_DIR, 'requirements.md'), `## REQ-001: Feature`);

      const validator = new TraceabilityValidator({ minCoverage: 0 });
      const result = await validator.validate(TEST_DIR);

      expect(result.issues).toHaveLength(1);
      expect(result.issues[0]).toMatchObject({
        severity: 'warning',
        code: 'ORPHAN_REQUIREMENT',
        artifactId: 'REQ-001',
      });
    });

    it('should generate warnings for orphan designs', async () => {
      await writeFile(join(DESIGN_DIR, 'design.md'), `## DES-001: Orphan design`);

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.issues.some((i) => i.code === 'ORPHAN_DESIGN')).toBe(true);
    });
  });

  describe('generateReport', () => {
    it('should generate a markdown report', async () => {
      await writeFile(
        join(SPECS_DIR, 'requirements.md'),
        `## REQ-001: A
## REQ-002: B`
      );
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001
REQ-001`
      );

      const validator = new TraceabilityValidator({ minCoverage: 0 });
      const result = await validator.validate(TEST_DIR);
      const report = validator.generateReport(result);

      expect(report).toContain('# Traceability Validation Report');
      expect(report).toContain('Coverage: 50%');
      expect(report).toContain('REQ-002');
    });

    it('should show PASSED for valid results', async () => {
      await writeFile(join(SPECS_DIR, 'requirements.md'), `## REQ-001: A`);
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001
REQ-001`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);
      const report = validator.generateReport(result);

      expect(report).toContain('✅ PASSED');
    });

    it('should show FAILED for invalid results', async () => {
      await writeFile(
        join(SPECS_DIR, 'requirements.md'),
        Array.from({ length: 10 }, (_, i) => `## REQ-00${i}: Feature`).join('\n')
      );
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001
REQ-000`
      );

      const validator = new TraceabilityValidator({ minCoverage: 80 });
      const result = await validator.validate(TEST_DIR);
      const report = validator.generateReport(result);

      expect(report).toContain('❌ FAILED');
    });
  });

  describe('validateDesignFile', () => {
    it('should validate a single design file', async () => {
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001: Implementation
Traces to REQ-001.`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validateDesignFile(
        join(DESIGN_DIR, 'design.md'),
        [
          {
            id: 'REQ-001',
            type: 'requirement',
            filePath: 'specs.md',
            lineNumber: 1,
          },
        ]
      );

      expect(result.valid).toBe(true);
      expect(result.designs).toHaveLength(1);
      expect(result.links).toHaveLength(1);
    });
  });

  describe('validateTraceability convenience function', () => {
    it('should work as a standalone function', async () => {
      await writeFile(join(SPECS_DIR, 'requirements.md'), `## REQ-001: Feature`);
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001
REQ-001`
      );

      const result = await validateTraceability(TEST_DIR);

      expect(result.valid).toBe(true);
    });

    it('should accept options', async () => {
      await writeFile(join(SPECS_DIR, 'requirements.md'), `## REQ-001: Feature`);

      const result = await validateTraceability(TEST_DIR, { minCoverage: 0 });

      expect(result.valid).toBe(true);
    });
  });

  describe('complex ID patterns', () => {
    it('should handle hyphenated requirement IDs', async () => {
      await writeFile(
        join(SPECS_DIR, 'requirements.md'),
        `## REQ-AUTH-001: Authentication
## REQ-SESS-002: Session`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.requirements.map((r) => r.id)).toContain('REQ-AUTH-001');
      expect(result.requirements.map((r) => r.id)).toContain('REQ-SESS-002');
    });

    it('should handle hyphenated design IDs', async () => {
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-AUTH-001: Auth Module
## DES-SESS-002: Session Module`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.designs.map((d) => d.id)).toContain('DES-AUTH-001');
      expect(result.designs.map((d) => d.id)).toContain('DES-SESS-002');
    });
  });

  describe('line number tracking', () => {
    it('should track line numbers for requirements', async () => {
      await writeFile(
        join(SPECS_DIR, 'requirements.md'),
        `# Requirements

## REQ-001: First

## REQ-002: Second`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      const req1 = result.requirements.find((r) => r.id === 'REQ-001');
      const req2 = result.requirements.find((r) => r.id === 'REQ-002');

      expect(req1?.lineNumber).toBe(3);
      expect(req2?.lineNumber).toBe(5);
    });

    it('should track line numbers for links', async () => {
      await writeFile(join(SPECS_DIR, 'requirements.md'), `## REQ-001: Feature`);
      await writeFile(
        join(DESIGN_DIR, 'design.md'),
        `## DES-001

Traces to REQ-001 here.`
      );

      const validator = new TraceabilityValidator();
      const result = await validator.validate(TEST_DIR);

      expect(result.links[0].lineNumber).toBe(3);
    });
  });
});
