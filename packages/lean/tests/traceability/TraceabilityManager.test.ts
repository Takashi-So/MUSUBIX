/**
 * @fileoverview Unit tests for TraceabilityManager
 * @module @nahisaho/musubix-lean/tests/traceability/TraceabilityManager
 * @traceability REQ-LEAN-TRACE-001 to REQ-LEAN-TRACE-003
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { TraceabilityManager, type LinkType } from '../../src/traceability/TraceabilityManager.ts';
import type { LeanTheorem, LeanProof, VerificationResult } from '../../src/types.ts';

describe('TraceabilityManager', () => {
  let manager: TraceabilityManager;

  beforeEach(() => {
    manager = new TraceabilityManager();
  });

  describe('registerArtifact', () => {
    it('should register requirement artifact', () => {
      const artifact = manager.registerArtifact({
        type: 'requirement',
        name: 'Input validation',
        content: 'THE system SHALL validate input',
      });

      expect(artifact.id).toBeDefined();
      expect(artifact.type).toBe('requirement');
    });

    it('should register theorem artifact with custom id', () => {
      const artifact = manager.registerArtifact({
        type: 'theorem',
        artifactId: 'THM-001',
        name: 'input_validation_theorem',
        content: 'theorem input_validation : ...',
      });

      expect(artifact.id).toBe('THM-001');
      expect(artifact.type).toBe('theorem');
    });

    it('should register proof artifact', () => {
      const artifact = manager.registerArtifact({
        type: 'proof',
        artifactId: 'PROOF-001',
        name: 'input_validation_proof',
        content: 'by intro; assumption',
      });

      expect(artifact.id).toBe('PROOF-001');
    });
  });

  describe('createLink', () => {
    it('should create traceability link between artifacts', () => {
      manager.registerArtifact({ type: 'requirement', artifactId: 'REQ-001', name: 'req', content: '' });
      manager.registerArtifact({ type: 'theorem', artifactId: 'THM-001', name: 'thm', content: '' });

      const link = manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem');
      expect(link.id).toBeDefined();
      expect(link.source).toBe('REQ-001');
      expect(link.target).toBe('THM-001');
      expect(link.type).toBe('requirement_to_theorem');
      expect(link.confidence).toBe(1.0);
    });

    it('should create link with custom confidence', () => {
      const link = manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem', 0.8);
      expect(link.confidence).toBe(0.8);
    });

    it('should create link with metadata', () => {
      const link = manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem', 1.0, { note: 'test' });
      expect(link.metadata).toEqual({ note: 'test' });
    });
  });

  describe('linkTheoremToRequirement', () => {
    it('should link theorem to its requirement', () => {
      const theorem: LeanTheorem = {
        id: 'THM-001',
        name: 'test_theorem',
        statement: 'test statement',
        requirementId: 'REQ-001',
        hypotheses: [],
        conclusion: { type: 'bool', leanCode: 'true' },
        leanCode: 'theorem test : true := by trivial',
      };

      const link = manager.linkTheoremToRequirement(theorem);
      expect(link.source).toBe('REQ-001');
      expect(link.target).toBe('THM-001');
      expect(link.type).toBe('requirement_to_theorem');
    });
  });

  describe('linkProofToTheorem', () => {
    it('should link proof to its theorem', () => {
      const theorem: LeanTheorem = {
        id: 'THM-001',
        name: 'test_theorem',
        statement: 'test statement',
        requirementId: 'REQ-001',
        hypotheses: [],
        conclusion: { type: 'bool', leanCode: 'true' },
        leanCode: 'theorem test : true := by trivial',
      };

      const proof: LeanProof = {
        id: 'PROOF-001',
        theoremId: 'THM-001',
        tactics: ['trivial'],
        leanCode: 'by trivial',
        isComplete: true,
        generatedAt: new Date().toISOString(),
      };

      const link = manager.linkProofToTheorem(proof, theorem);
      expect(link.source).toBe('THM-001');
      expect(link.target).toBe('PROOF-001');
      expect(link.type).toBe('theorem_to_proof');
    });
  });

  describe('getLinksFromSource', () => {
    it('should get all links from a source artifact', () => {
      manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem');
      manager.createLink('REQ-001', 'THM-002', 'requirement_to_theorem');
      manager.createLink('REQ-002', 'THM-003', 'requirement_to_theorem');

      const links = manager.getLinksFromSource('REQ-001');
      expect(links).toHaveLength(2);
      expect(links.every(l => l.source === 'REQ-001')).toBe(true);
    });
  });

  describe('getLinksToTarget', () => {
    it('should get all links targeting an artifact', () => {
      manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem');
      manager.createLink('REQ-002', 'THM-001', 'requirement_to_theorem');

      const links = manager.getLinksToTarget('THM-001');
      expect(links).toHaveLength(2);
      expect(links.every(l => l.target === 'THM-001')).toBe(true);
    });
  });

  describe('getLinksByType', () => {
    it('should get all links of a specific type', () => {
      manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem');
      manager.createLink('THM-001', 'PROOF-001', 'theorem_to_proof');
      manager.createLink('REQ-002', 'THM-002', 'requirement_to_theorem');

      const links = manager.getLinksByType('requirement_to_theorem');
      expect(links).toHaveLength(2);
      expect(links.every(l => l.type === 'requirement_to_theorem')).toBe(true);
    });
  });

  describe('calculateCoverage', () => {
    it('should calculate traceability coverage', () => {
      manager.registerArtifact({ type: 'requirement', artifactId: 'REQ-001', name: 'req1', content: '' });
      manager.registerArtifact({ type: 'requirement', artifactId: 'REQ-002', name: 'req2', content: '' });
      manager.registerArtifact({ type: 'theorem', artifactId: 'THM-001', name: 'thm1', content: '' });
      manager.registerArtifact({ type: 'proof', artifactId: 'PROOF-001', name: 'proof1', content: '' });

      manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem');
      manager.createLink('THM-001', 'PROOF-001', 'theorem_to_proof', 1.0, { isComplete: true });

      const coverage = manager.calculateCoverage(['REQ-001', 'REQ-002']);
      expect(coverage.totalRequirements).toBe(2);
      expect(coverage.untraced).toContain('REQ-002');
      expect(coverage.coveragePercentage).toBeGreaterThanOrEqual(0);
    });
  });

  describe('getTraceChain', () => {
    it('should get full traceability chain for a requirement', () => {
      manager.registerArtifact({ type: 'requirement', artifactId: 'REQ-001', name: 'req', content: '' });
      manager.registerArtifact({ type: 'theorem', artifactId: 'THM-001', name: 'thm', content: '' });
      manager.registerArtifact({ type: 'proof', artifactId: 'PROOF-001', name: 'proof', content: '' });

      manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem');
      manager.createLink('THM-001', 'PROOF-001', 'theorem_to_proof');

      const chain = manager.getTraceChain('REQ-001');
      expect(chain.length).toBeGreaterThanOrEqual(1);
      expect(chain.some(a => a.id === 'REQ-001')).toBe(true);
    });
  });

  describe('validateIntegrity', () => {
    it('should detect broken links', () => {
      // Create link without registering artifacts
      manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem');

      const { valid, errors } = manager.validateIntegrity();
      expect(valid).toBe(false);
      expect(errors.length).toBeGreaterThan(0);
    });

    it('should pass for valid links', () => {
      manager.registerArtifact({ type: 'requirement', artifactId: 'REQ-001', name: 'req', content: '' });
      manager.registerArtifact({ type: 'theorem', artifactId: 'THM-001', name: 'thm', content: '' });
      manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem');

      const { valid, errors } = manager.validateIntegrity();
      expect(valid).toBe(true);
      expect(errors).toHaveLength(0);
    });
  });

  describe('exportMatrix', () => {
    it('should export traceability matrix', () => {
      manager.registerArtifact({ type: 'requirement', artifactId: 'REQ-001', name: 'req', content: '' });
      manager.registerArtifact({ type: 'theorem', artifactId: 'THM-001', name: 'thm', content: '' });
      manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem');

      const matrix = manager.exportMatrix();
      expect(matrix['REQ-001']).toBeDefined();
      expect(matrix['REQ-001']['THM-001']).toBeDefined();
    });
  });

  describe('exportMarkdown', () => {
    it('should export to Markdown format', () => {
      manager.registerArtifact({ type: 'requirement', artifactId: 'REQ-001', name: 'req', content: '' });
      manager.registerArtifact({ type: 'theorem', artifactId: 'THM-001', name: 'thm', content: '' });
      manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem');

      const markdown = manager.exportMarkdown();
      expect(markdown).toContain('# Traceability Matrix');
      expect(markdown).toContain('REQ-001');
    });
  });

  describe('clear', () => {
    it('should clear all data', () => {
      manager.registerArtifact({ type: 'requirement', artifactId: 'REQ-001', name: 'req', content: '' });
      manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem');

      manager.clear();

      const stats = manager.getStats();
      expect(stats.artifacts).toBe(0);
      expect(stats.links).toBe(0);
    });
  });

  describe('getStats', () => {
    it('should return statistics', () => {
      manager.registerArtifact({ type: 'requirement', artifactId: 'REQ-001', name: 'req', content: '' });
      manager.registerArtifact({ type: 'theorem', artifactId: 'THM-001', name: 'thm', content: '' });
      manager.createLink('REQ-001', 'THM-001', 'requirement_to_theorem');
      manager.createLink('THM-001', 'PROOF-001', 'theorem_to_proof');

      const stats = manager.getStats();
      expect(stats.artifacts).toBe(2);
      expect(stats.links).toBe(2);
      expect(stats.byType['requirement_to_theorem']).toBe(1);
      expect(stats.byType['theorem_to_proof']).toBe(1);
    });
  });
});
