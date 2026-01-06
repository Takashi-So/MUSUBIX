/**
 * Formal Verify MCP Tools Unit Tests
 */

import { describe, it, expect } from 'vitest';
import {
  verifyPreconditionTool,
  verifyPostconditionTool,
  earsToSmtTool,
  traceAddLinkTool,
  traceQueryTool,
  traceImpactTool,
  formalVerifyTools,
  getFormalVerifyTools,
  handleFormalVerifyTool,
} from '../../src/tools/formal-verify-tools';

describe('Formal Verify MCP Tools', () => {
  describe('Tool Definitions', () => {
    describe('verifyPreconditionTool', () => {
      it('should have correct name', () => {
        expect(verifyPreconditionTool.name).toBe('verify_precondition');
      });

      it('should have description', () => {
        expect(verifyPreconditionTool.description).toBeDefined();
        expect(verifyPreconditionTool.description.length).toBeGreaterThan(0);
      });

      it('should have required inputSchema', () => {
        expect(verifyPreconditionTool.inputSchema).toBeDefined();
        expect(verifyPreconditionTool.inputSchema.type).toBe('object');
        expect(verifyPreconditionTool.inputSchema.properties).toBeDefined();
      });

      it('should require expression parameter', () => {
        expect(verifyPreconditionTool.inputSchema.required).toContain('expression');
      });

      it('should have variables parameter', () => {
        expect(verifyPreconditionTool.inputSchema.properties.variables).toBeDefined();
      });
    });

    describe('verifyPostconditionTool', () => {
      it('should have correct name', () => {
        expect(verifyPostconditionTool.name).toBe('verify_postcondition');
      });

      it('should require precondition, transition, and postcondition', () => {
        expect(verifyPostconditionTool.inputSchema.required).toContain('precondition');
        expect(verifyPostconditionTool.inputSchema.required).toContain('transition');
        expect(verifyPostconditionTool.inputSchema.required).toContain('postcondition');
      });
    });

    describe('earsToSmtTool', () => {
      it('should have correct name', () => {
        expect(earsToSmtTool.name).toBe('ears_to_smt');
      });

      it('should require requirement parameter', () => {
        expect(earsToSmtTool.inputSchema.required).toContain('requirement');
      });

      it('should have description mentioning EARS', () => {
        expect(earsToSmtTool.description.toLowerCase()).toContain('ears');
      });
    });

    describe('traceAddLinkTool', () => {
      it('should have correct name', () => {
        expect(traceAddLinkTool.name).toBe('trace_add_link');
      });

      it('should require source, target, and type', () => {
        expect(traceAddLinkTool.inputSchema.required).toContain('source');
        expect(traceAddLinkTool.inputSchema.required).toContain('target');
        expect(traceAddLinkTool.inputSchema.required).toContain('linkType');
      });
    });

    describe('traceQueryTool', () => {
      it('should have correct name', () => {
        expect(traceQueryTool.name).toBe('trace_query');
      });

      it('should have optional filter parameters', () => {
        expect(traceQueryTool.inputSchema.properties.nodeType).toBeDefined();
        expect(traceQueryTool.inputSchema.properties.linkedTo).toBeDefined();
      });
    });

    describe('traceImpactTool', () => {
      it('should have correct name', () => {
        expect(traceImpactTool.name).toBe('trace_impact');
      });

      it('should require nodeId parameter', () => {
        expect(traceImpactTool.inputSchema.required).toContain('nodeId');
      });

      it('should have optional maxDepth parameter', () => {
        expect(traceImpactTool.inputSchema.properties.maxDepth).toBeDefined();
      });
    });
  });

  describe('formalVerifyTools array', () => {
    it('should contain all 6 tools', () => {
      expect(formalVerifyTools.length).toBe(6);
    });

    it('should contain verifyPreconditionTool', () => {
      expect(formalVerifyTools).toContain(verifyPreconditionTool);
    });

    it('should contain verifyPostconditionTool', () => {
      expect(formalVerifyTools).toContain(verifyPostconditionTool);
    });

    it('should contain earsToSmtTool', () => {
      expect(formalVerifyTools).toContain(earsToSmtTool);
    });

    it('should contain traceAddLinkTool', () => {
      expect(formalVerifyTools).toContain(traceAddLinkTool);
    });

    it('should contain traceQueryTool', () => {
      expect(formalVerifyTools).toContain(traceQueryTool);
    });

    it('should contain traceImpactTool', () => {
      expect(formalVerifyTools).toContain(traceImpactTool);
    });
  });

  describe('getFormalVerifyTools', () => {
    it('should return array of tools', () => {
      const tools = getFormalVerifyTools();
      expect(Array.isArray(tools)).toBe(true);
      expect(tools.length).toBe(6);
    });

    it('should return same tools as formalVerifyTools', () => {
      const tools = getFormalVerifyTools();
      expect(tools).toEqual(formalVerifyTools);
    });
  });

  describe('handleFormalVerifyTool', () => {
    it('should handle verify_precondition tool', async () => {
      const result = await handleFormalVerifyTool('verify_precondition', {
        expression: 'x > 0',
        variables: [{ name: 'x', type: 'Int' }],
      });

      expect(result).toBeDefined();
      expect(result.content).toBeDefined();
    });

    it('should handle verify_postcondition tool', async () => {
      const result = await handleFormalVerifyTool('verify_postcondition', {
        precondition: 'x >= 0',
        transition: 'x_next == x + 1',
        postcondition: 'x_next > 0',
        variables: [
          { name: 'x', type: 'Int' },
          { name: 'x_next', type: 'Int' },
        ],
      });

      expect(result).toBeDefined();
      expect(result.content).toBeDefined();
    });

    it('should handle ears_to_smt tool', async () => {
      const result = await handleFormalVerifyTool('ears_to_smt', {
        requirement: 'THE system SHALL validate all user inputs',
      });

      expect(result).toBeDefined();
      expect(result.content).toBeDefined();
    });

    it('should handle trace_add_link tool', async () => {
      const result = await handleFormalVerifyTool('trace_add_link', {
        source: 'DES-001',
        target: 'REQ-001',
        linkType: 'satisfies',
      });

      expect(result).toBeDefined();
      expect(result.content).toBeDefined();
    });

    it('should handle trace_query tool', async () => {
      const result = await handleFormalVerifyTool('trace_query', {
        nodeType: 'requirement',
      });

      expect(result).toBeDefined();
      expect(result.content).toBeDefined();
    });

    it('should handle trace_impact tool', async () => {
      const result = await handleFormalVerifyTool('trace_impact', {
        nodeId: 'REQ-001',
      });

      expect(result).toBeDefined();
      expect(result.content).toBeDefined();
    });

    it('should return error for unknown tool', async () => {
      const result = await handleFormalVerifyTool('unknown_tool', {});

      expect(result).toBeDefined();
      expect(result.isError).toBe(true);
    });
  });
});
