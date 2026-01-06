/**
 * ImpactAnalyzer Unit Tests
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { ImpactAnalyzer } from '../../src/traceability/ImpactAnalyzer';
import { TraceabilityDB } from '../../src/traceability/TraceabilityDB';

describe('ImpactAnalyzer', () => {
  let analyzer: ImpactAnalyzer;
  let db: TraceabilityDB;

  beforeEach(async () => {
    // Use in-memory database for tests
    db = new TraceabilityDB(':memory:');
    analyzer = new ImpactAnalyzer(db);

    // Setup test data
    await db.addNode({ id: 'REQ-001', type: 'requirement', title: 'Requirement 1' });
    await db.addNode({ id: 'REQ-002', type: 'requirement', title: 'Requirement 2' });
    await db.addNode({ id: 'DES-001', type: 'design', title: 'Design 1' });
    await db.addNode({ id: 'DES-002', type: 'design', title: 'Design 2' });
    await db.addNode({ id: 'CODE-001', type: 'code', title: 'Code 1' });

    await db.addLink({ source: 'DES-001', target: 'REQ-001', type: 'satisfies' });
    await db.addLink({ source: 'DES-002', target: 'REQ-002', type: 'satisfies' });
    await db.addLink({ source: 'CODE-001', target: 'DES-001', type: 'implements' });
  });

  afterEach(async () => {
    await db.close();
  });

  describe('constructor', () => {
    it('should create instance with database', () => {
      expect(analyzer).toBeInstanceOf(ImpactAnalyzer);
    });

    it('should create instance with options', () => {
      const analyzerWithOptions = new ImpactAnalyzer(db, {
        maxDepth: 5,
        decayFactor: 0.5,
      });
      expect(analyzerWithOptions).toBeInstanceOf(ImpactAnalyzer);
    });
  });

  describe('analyze', () => {
    it('should find directly impacted nodes', async () => {
      const result = await analyzer.analyze('REQ-001');

      expect(result).toBeDefined();
      expect(result.sourceId).toBe('REQ-001');
    });

    it('should return result with impacted nodes array', async () => {
      const result = await analyzer.analyze('REQ-001');
      expect(Array.isArray(result.impactedNodes)).toBe(true);
    });
  });

  describe('analyzeReverse', () => {
    it('should find nodes that impact the target', async () => {
      const result = await analyzer.analyzeReverse('CODE-001');
      expect(result).toBeDefined();
    });
  });

  describe('analyzeCoverage', () => {
    it('should return coverage analysis result', async () => {
      const result = await analyzer.analyzeCoverage();
      expect(result).toBeDefined();
    });
  });

  describe('detectCycles', () => {
    it('should return array for cycle detection', async () => {
      const cycles = await analyzer.detectCycles();
      expect(Array.isArray(cycles)).toBe(true);
    });
  });
});
