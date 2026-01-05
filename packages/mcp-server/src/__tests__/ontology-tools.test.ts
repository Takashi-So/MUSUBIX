/**
 * @fileoverview Tests for Ontology Tools
 * @traceability REQ-INT-003
 */

import { describe, it, expect } from 'vitest';
import { 
  consistencyValidateTool, 
  validateTripleTool, 
  checkCircularTool,
  ontologyTools,
  getOntologyTools,
} from '../tools/ontology-tools.js';

describe('Ontology Tools', () => {
  describe('consistencyValidateTool', () => {
    it('should have correct definition', () => {
      expect(consistencyValidateTool.name).toBe('consistency_validate');
      expect(consistencyValidateTool.description).toContain('OWL');
      expect(consistencyValidateTool.inputSchema.properties).toHaveProperty('triples');
    });

    it('should validate valid triples', async () => {
      const result = await consistencyValidateTool.handler({
        triples: [
          { subject: 'user:1', predicate: 'hasName', object: 'Alice' },
          { subject: 'user:2', predicate: 'hasName', object: 'Bob' },
        ],
      });

      expect(result.isError).toBe(false);
      expect(result.content[0]).toHaveProperty('text');
      const text = (result.content[0] as { text: string }).text;
      expect(text).toContain('VALID');
    });

    it('should detect duplicate triples', async () => {
      const result = await consistencyValidateTool.handler({
        triples: [
          { subject: 'user:1', predicate: 'hasName', object: 'Alice' },
        ],
        existingTriples: [
          { subject: 'user:1', predicate: 'hasName', object: 'Alice' },
        ],
      });

      expect(result.isError).toBe(false);
      const text = (result.content[0] as { text: string }).text;
      expect(text).toContain('duplicate');
    });

    it('should detect circular dependencies', async () => {
      const result = await consistencyValidateTool.handler({
        triples: [
          { subject: 'A', predicate: 'dependsOn', object: 'B' },
          { subject: 'B', predicate: 'dependsOn', object: 'C' },
          { subject: 'C', predicate: 'dependsOn', object: 'A' },
        ],
        checkTypes: ['circular'],
      });

      expect(result.isError).toBe(false);
      const text = (result.content[0] as { text: string }).text;
      expect(text).toContain('circular');
    });
  });

  describe('validateTripleTool', () => {
    it('should have correct definition', () => {
      expect(validateTripleTool.name).toBe('validate_triple');
      expect(validateTripleTool.inputSchema.required).toContain('subject');
      expect(validateTripleTool.inputSchema.required).toContain('predicate');
      expect(validateTripleTool.inputSchema.required).toContain('object');
    });

    it('should validate single triple', async () => {
      const result = await validateTripleTool.handler({
        subject: 'entity:1',
        predicate: 'hasType',
        object: 'Person',
      });

      expect(result.isError).toBe(false);
      const text = (result.content[0] as { text: string }).text;
      expect(text).toContain('VALID');
    });

    it('should detect duplicate in context', async () => {
      const result = await validateTripleTool.handler({
        subject: 'entity:1',
        predicate: 'hasType',
        object: 'Person',
        context: [
          { subject: 'entity:1', predicate: 'hasType', object: 'Person' },
        ],
      });

      expect(result.isError).toBe(false);
      const text = (result.content[0] as { text: string }).text;
      expect(text).toContain('Duplicate');
    });
  });

  describe('checkCircularTool', () => {
    it('should have correct definition', () => {
      expect(checkCircularTool.name).toBe('check_circular');
      expect(checkCircularTool.inputSchema.properties).toHaveProperty('relationships');
    });

    it('should detect no cycles in acyclic graph', async () => {
      const result = await checkCircularTool.handler({
        relationships: [
          { from: 'A', to: 'B' },
          { from: 'B', to: 'C' },
          { from: 'A', to: 'C' },
        ],
      });

      expect(result.isError).toBe(false);
      const text = (result.content[0] as { text: string }).text;
      expect(text).toContain('No circular dependencies');
    });

    it('should detect cycle', async () => {
      const result = await checkCircularTool.handler({
        relationships: [
          { from: 'A', to: 'B' },
          { from: 'B', to: 'C' },
          { from: 'C', to: 'A' },
        ],
      });

      expect(result.isError).toBe(false);
      const text = (result.content[0] as { text: string }).text;
      expect(text).toContain('cycle');
    });
  });

  describe('tool exports', () => {
    it('should export array of ontology tools', () => {
      expect(ontologyTools).toBeInstanceOf(Array);
      expect(ontologyTools.length).toBe(3);
    });

    it('should have getOntologyTools function', () => {
      const tools = getOntologyTools();
      expect(tools).toBeInstanceOf(Array);
      expect(tools.length).toBe(3);
    });
  });
});
