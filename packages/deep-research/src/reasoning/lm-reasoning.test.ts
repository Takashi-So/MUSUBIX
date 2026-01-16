// LM Reasoning Tests
// TSK-DR-010

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { LMReasoning, type LMProvider } from './lm-reasoning.js';
import type { ResearchContext, KnowledgeItem } from '../types/index.js';

describe('LMReasoning', () => {
  let mockProvider: LMProvider;
  let reasoning: LMReasoning;

  beforeEach(() => {
    mockProvider = {
      name: 'Mock LM',
      generate: vi.fn(),
      isAvailable: vi.fn().mockResolvedValue(true),
    };
    reasoning = new LMReasoning(mockProvider, 3);
  });

  describe('generateQuestions', () => {
    it('should generate reflective questions', async () => {
      const context: ResearchContext = {
        query: 'How does TypeScript type inference work?',
        iteration: 1,
        maxIterations: 5,
        knowledgeBase: [
          {
            type: 'fact',
            content: 'TypeScript has static type checking',
            sources: ['https://example.com/ts'],
            relevance: 0.9,
            timestamp: Date.now(),
          },
        ],
      };

      (mockProvider.generate as any).mockResolvedValueOnce(`
[
  {
    "question": "What are the performance implications of type inference?",
    "reason": "Performance aspect not covered",
    "priority": 4
  },
  {
    "question": "How does type inference handle complex generics?",
    "reason": "Need deeper understanding of edge cases",
    "priority": 5
  }
]
      `);

      const questions = await reasoning.generateQuestions(context);

      expect(questions).toHaveLength(2);
      expect(questions[0].question).toContain('performance');
      expect(questions[0].priority).toBe(4);
      expect(questions[1].priority).toBe(5);
      expect(mockProvider.generate).toHaveBeenCalledWith(
        expect.stringContaining('TypeScript type inference'),
        expect.objectContaining({
          temperature: 0.7,
          systemPrompt: expect.stringContaining('research assistant'),
        })
      );
    });

    it('should limit questions to maxQuestions', async () => {
      const context: ResearchContext = {
        query: 'Test query',
        iteration: 1,
        maxIterations: 5,
        knowledgeBase: [],
      };

      (mockProvider.generate as any).mockResolvedValueOnce(`
[
  {"question": "Q1", "reason": "R1", "priority": 3},
  {"question": "Q2", "reason": "R2", "priority": 4},
  {"question": "Q3", "reason": "R3", "priority": 5},
  {"question": "Q4", "reason": "R4", "priority": 2},
  {"question": "Q5", "reason": "R5", "priority": 1}
]
      `);

      const questions = await reasoning.generateQuestions(context);

      expect(questions).toHaveLength(3); // maxQuestions = 3
    });

    it('should handle invalid JSON response', async () => {
      const context: ResearchContext = {
        query: 'Test',
        iteration: 1,
        maxIterations: 5,
        knowledgeBase: [],
      };

      (mockProvider.generate as any).mockResolvedValueOnce('Invalid response');

      const questions = await reasoning.generateQuestions(context);

      expect(questions).toHaveLength(0);
    });

    it('should clamp priority values to 1-5', async () => {
      const context: ResearchContext = {
        query: 'Test',
        iteration: 1,
        maxIterations: 5,
        knowledgeBase: [],
      };

      (mockProvider.generate as any).mockResolvedValueOnce(`
[
  {"question": "Q1", "reason": "R1", "priority": 10},
  {"question": "Q2", "reason": "R2", "priority": -5}
]
      `);

      const questions = await reasoning.generateQuestions(context);

      expect(questions[0].priority).toBe(5); // clamped to max
      expect(questions[1].priority).toBe(1); // clamped to min
    });
  });

  describe('evaluateAnswer', () => {
    it('should evaluate answer as definitive', async () => {
      const knowledgeItems: KnowledgeItem[] = [
        {
          type: 'fact',
          content: 'TypeScript uses structural typing',
          sources: ['https://example.com/1'],
          relevance: 0.9,
          timestamp: Date.now(),
        },
        {
          type: 'fact',
          content: 'Type inference works at compile time',
          sources: ['https://example.com/2'],
          relevance: 0.85,
          timestamp: Date.now(),
        },
      ];

      (mockProvider.generate as any).mockResolvedValueOnce(`
{
  "isDefinitive": true,
  "confidence": 0.88,
  "reasoning": "All key aspects covered"
}
      `);

      const result = await reasoning.evaluateAnswer(
        'How does TypeScript type inference work?',
        knowledgeItems
      );

      expect(result.isDefinitive).toBe(true);
      expect(result.confidence).toBe(0.88);
      expect(result.reasoning).toContain('covered');
    });

    it('should evaluate answer as incomplete', async () => {
      const knowledgeItems: KnowledgeItem[] = [
        {
          type: 'opinion',
          content: 'TypeScript is good',
          sources: ['https://example.com/1'],
          relevance: 0.5,
          timestamp: Date.now(),
        },
      ];

      (mockProvider.generate as any).mockResolvedValueOnce(`
{
  "isDefinitive": false,
  "confidence": 0.3,
  "reasoning": "Insufficient technical details"
}
      `);

      const result = await reasoning.evaluateAnswer('Technical query', knowledgeItems);

      expect(result.isDefinitive).toBe(false);
      expect(result.confidence).toBe(0.3);
    });

    it('should clamp confidence to 0-1 range', async () => {
      const knowledgeItems: KnowledgeItem[] = [];

      (mockProvider.generate as any).mockResolvedValueOnce(`
{
  "isDefinitive": true,
  "confidence": 2.5,
  "reasoning": "Test"
}
      `);

      const result = await reasoning.evaluateAnswer('Test', knowledgeItems);

      expect(result.confidence).toBe(1); // clamped to max
    });

    it('should handle invalid evaluation response', async () => {
      const knowledgeItems: KnowledgeItem[] = [];

      (mockProvider.generate as any).mockResolvedValueOnce('Invalid JSON');

      const result = await reasoning.evaluateAnswer('Test', knowledgeItems);

      expect(result.isDefinitive).toBe(false);
      expect(result.confidence).toBe(0.5);
      expect(result.reasoning).toBe('Could not parse evaluation');
    });
  });

  describe('convertToEARS', () => {
    it('should convert knowledge to EARS format', async () => {
      const knowledgeItems: KnowledgeItem[] = [
        {
          type: 'fact',
          content: 'System must validate user input',
          sources: ['https://example.com/1'],
          relevance: 0.9,
          timestamp: Date.now(),
        },
        {
          type: 'recommendation',
          content: 'Use encryption for sensitive data',
          sources: ['https://example.com/2'],
          relevance: 0.85,
          timestamp: Date.now(),
        },
      ];

      (mockProvider.generate as any).mockResolvedValueOnce(`
THE system SHALL validate all user input before processing.
THE system SHALL encrypt sensitive data at rest and in transit.
WHEN invalid input is detected, THE system SHALL reject it with an error message.
      `);

      const ears = await reasoning.convertToEARS(knowledgeItems);

      expect(ears.length).toBeGreaterThan(0);
      expect(ears[0]).toContain('SHALL');
      expect(ears.some(e => e.includes('WHEN'))).toBe(true);
    });

    it('should filter non-EARS lines', async () => {
      const knowledgeItems: KnowledgeItem[] = [
        {
          type: 'fact',
          content: 'Test fact',
          sources: ['https://example.com/1'],
          relevance: 0.9,
          timestamp: Date.now(),
        },
      ];

      (mockProvider.generate as any).mockResolvedValueOnce(`
This is just a comment.
THE system SHALL do something.
Another non-EARS line.
WHEN event occurs, THE system SHALL respond.
      `);

      const ears = await reasoning.convertToEARS(knowledgeItems);

      expect(ears).toHaveLength(2);
      expect(ears[0]).toContain('SHALL');
      expect(ears[1]).toContain('WHEN');
    });

    it('should process knowledge in batches', async () => {
      const knowledgeItems: KnowledgeItem[] = Array.from({ length: 12 }, (_, i) => ({
        type: 'fact' as const,
        content: `Fact ${i + 1}`,
        sources: ['https://example.com'],
        relevance: 0.8,
        timestamp: Date.now(),
      }));

      (mockProvider.generate as any).mockResolvedValue(`
THE system SHALL requirement 1.
THE system SHALL requirement 2.
      `);

      const ears = await reasoning.convertToEARS(knowledgeItems);

      // Should call provider 3 times (12 items / 5 batch size = 3 batches)
      expect(mockProvider.generate).toHaveBeenCalledTimes(3);
      expect(ears.length).toBeGreaterThan(0);
    });

    it('should handle empty knowledge items', async () => {
      const knowledgeItems: KnowledgeItem[] = [];

      const ears = await reasoning.convertToEARS(knowledgeItems);

      expect(ears).toHaveLength(0);
      expect(mockProvider.generate).not.toHaveBeenCalled();
    });
  });
});
