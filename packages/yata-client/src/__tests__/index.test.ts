/**
 * @musubix/yata-client - Basic Tests
 */
import { describe, it, expect } from 'vitest';

describe('@musubix/yata-client', () => {
  describe('Package Export', () => {
    it('should export VERSION', async () => {
      const { VERSION } = await import('../index.js');
      expect(VERSION).toBeDefined();
      expect(typeof VERSION).toBe('string');
    });

    it('should export YataMCPClient', async () => {
      const { YataMCPClient } = await import('../index.js');
      expect(YataMCPClient).toBeDefined();
    });

    it('should export NeuroSymbolicIntegrator', async () => {
      const { NeuroSymbolicIntegrator } = await import('../index.js');
      expect(NeuroSymbolicIntegrator).toBeDefined();
    });

    it('should export OntologyMapper', async () => {
      const { OntologyMapper } = await import('../index.js');
      expect(OntologyMapper).toBeDefined();
    });

    it('should export ContradictionDetector', async () => {
      const { ContradictionDetector } = await import('../index.js');
      expect(ContradictionDetector).toBeDefined();
    });

    it('should export ConfidenceEvaluator', async () => {
      const { ConfidenceEvaluator } = await import('../index.js');
      expect(ConfidenceEvaluator).toBeDefined();
    });
  });

  describe('Factory Functions', () => {
    it('should export createYataClient', async () => {
      const { createYataClient } = await import('../index.js');
      expect(createYataClient).toBeDefined();
      expect(typeof createYataClient).toBe('function');
    });

    it('should export createNeuroSymbolicIntegrator', async () => {
      const { createNeuroSymbolicIntegrator } = await import('../index.js');
      expect(createNeuroSymbolicIntegrator).toBeDefined();
      expect(typeof createNeuroSymbolicIntegrator).toBe('function');
    });
  });

  describe('Constants', () => {
    it('should export MUSUBIX_NAMESPACES', async () => {
      const { MUSUBIX_NAMESPACES } = await import('../index.js');
      expect(MUSUBIX_NAMESPACES).toBeDefined();
      expect(typeof MUSUBIX_NAMESPACES).toBe('object');
    });

    it('should export MUSUBIX_CONCEPTS', async () => {
      const { MUSUBIX_CONCEPTS } = await import('../index.js');
      expect(MUSUBIX_CONCEPTS).toBeDefined();
      expect(typeof MUSUBIX_CONCEPTS).toBe('object');
    });
  });
});
