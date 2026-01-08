/**
 * MCP Synthesis Tools Tests
 * @module @nahisaho/musubix-mcp-server
 * @description Tests for synthesis MCP tools
 * Traces to: TSK-INT-103, REQ-INT-103
 */

import { describe, it, expect } from 'vitest';
import {
  synthesizeFromExamples,
  analyzeExamples,
  learnPatterns,
  queryPatterns,
  getSynthesisStats,
  SYNTHESIS_TOOLS,
} from '../tools/synthesis-tools.js';
import {
  synthesisGuidancePrompt,
  patternExplanationPrompt,
  SYNTHESIS_PROMPTS,
  getSynthesisPrompts,
} from '../prompts/synthesis-prompts.js';

describe('Synthesis Tools', () => {
  describe('SYNTHESIS_TOOLS', () => {
    it('should export 5 tools', () => {
      expect(SYNTHESIS_TOOLS).toHaveLength(5);
    });

    it('should have unique tool names', () => {
      const names = SYNTHESIS_TOOLS.map(t => t.name);
      expect(new Set(names).size).toBe(names.length);
    });
  });

  describe('synthesizeFromExamples', () => {
    it('should have correct definition', () => {
      expect(synthesizeFromExamples.name).toBe('synthesis_from_examples');
      expect(synthesizeFromExamples.description).toContain('Synthesize');
      expect(synthesizeFromExamples.inputSchema.properties).toHaveProperty('examples');
    });

    it('should synthesize from valid examples', async () => {
      const result = await synthesizeFromExamples.handler({
        examples: [
          { input: 'hello', output: 'HELLO' },
          { input: 'world', output: 'WORLD' },
        ],
        domain: 'string',
      });

      expect(result.isError).toBeFalsy();
      const content = result.content[0];
      expect(content.type).toBe('text');
      expect(content.text).toContain('Synthesis completed');
    });

    it('should reject empty examples', async () => {
      const result = await synthesizeFromExamples.handler({
        examples: [],
      });

      expect(result.isError).toBe(true);
      expect(result.content[0].text).toContain('At least one example');
    });
  });

  describe('analyzeExamples', () => {
    it('should have correct definition', () => {
      expect(analyzeExamples.name).toBe('synthesis_analyze_examples');
      expect(analyzeExamples.description).toContain('quality');
    });

    it('should analyze example quality', async () => {
      const result = await analyzeExamples.handler({
        examples: [
          { input: 'a', output: 'A' },
          { input: 'b', output: 'B' },
          { input: 'c', output: 'C' },
        ],
      });

      expect(result.isError).toBeFalsy();
      const content = JSON.parse(result.content[0].text);
      expect(content.quality.score).toBeGreaterThan(0.5);
    });

    it('should flag insufficient examples', async () => {
      const result = await analyzeExamples.handler({
        examples: [{ input: 'a', output: 'A' }],
      });

      expect(result.isError).toBeFalsy();
      const content = JSON.parse(result.content[0].text);
      expect(content.quality.issues).toContain('Insufficient examples');
    });
  });

  describe('learnPatterns', () => {
    it('should have correct definition', () => {
      expect(learnPatterns.name).toBe('synthesis_learn_patterns');
      expect(learnPatterns.description).toContain('patterns');
    });

    it('should learn from code snippet', async () => {
      const result = await learnPatterns.handler({
        code: 'function upper(s: string) { return s.toUpperCase(); }',
        language: 'typescript',
      });

      expect(result.isError).toBeFalsy();
      const content = JSON.parse(result.content[0].text);
      expect(content.result.extracted).toBeGreaterThanOrEqual(1);
    });

    it('should reject empty code', async () => {
      const result = await learnPatterns.handler({
        code: '',
      });

      expect(result.isError).toBe(true);
    });
  });

  describe('queryPatterns', () => {
    it('should have correct definition', () => {
      expect(queryPatterns.name).toBe('synthesis_query_patterns');
    });

    it('should query pattern library', async () => {
      const result = await queryPatterns.handler({
        query: 'string transformation',
        minConfidence: 0.7,
      });

      expect(result.isError).toBeFalsy();
      const content = JSON.parse(result.content[0].text);
      expect(content.result.matches).toBeDefined();
    });

    it('should reject empty query', async () => {
      const result = await queryPatterns.handler({
        query: '',
      });

      expect(result.isError).toBe(true);
    });
  });

  describe('getSynthesisStats', () => {
    it('should have correct definition', () => {
      expect(getSynthesisStats.name).toBe('synthesis_get_stats');
    });

    it('should return statistics', async () => {
      const result = await getSynthesisStats.handler({
        includeHistory: true,
      });

      expect(result.isError).toBeFalsy();
      const content = JSON.parse(result.content[0].text);
      expect(content.stats.synthesisCount).toBeDefined();
      expect(content.stats.patternLibrary).toBeDefined();
    });
  });
});

describe('Synthesis Prompts', () => {
  describe('SYNTHESIS_PROMPTS', () => {
    it('should export 2 prompts', () => {
      expect(SYNTHESIS_PROMPTS).toHaveLength(2);
    });

    it('should be retrievable via getSynthesisPrompts', () => {
      const prompts = getSynthesisPrompts();
      expect(prompts).toHaveLength(2);
    });
  });

  describe('synthesisGuidancePrompt', () => {
    it('should have correct definition', () => {
      expect(synthesisGuidancePrompt.name).toBe('synthesis_guidance');
      expect(synthesisGuidancePrompt.description).toContain('Guide');
    });

    it('should generate guidance prompt', async () => {
      const result = await synthesisGuidancePrompt.handler({
        domain: 'string',
        taskDescription: 'Convert to uppercase',
      });

      expect(result.messages).toHaveLength(1);
      expect(result.messages[0].content.text).toContain('examples');
    });
  });

  describe('patternExplanationPrompt', () => {
    it('should have correct definition', () => {
      expect(patternExplanationPrompt.name).toBe('synthesis_explain_pattern');
      expect(patternExplanationPrompt.arguments?.find(a => a.name === 'pattern')?.required).toBe(true);
    });

    it('should generate explanation prompt', async () => {
      const result = await patternExplanationPrompt.handler({
        pattern: 'str => str.toUpperCase()',
        examples: JSON.stringify([{ input: 'hello', output: 'HELLO' }]),
      });

      expect(result.messages).toHaveLength(1);
      expect(result.messages[0].content.text).toContain('explain');
    });
  });
});
