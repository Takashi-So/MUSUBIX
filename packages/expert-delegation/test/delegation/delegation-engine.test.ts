/**
 * @nahisaho/musubix-expert-delegation
 * Delegation Engine Tests
 *
 * Traces to: REQ-DEL-001, REQ-DEL-002
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { DelegationEngine } from '../../src/delegation/delegation-engine.js';
import { MockVSCodeLMProvider } from '../../src/test/mocks.js';
import { createTestTask, createTestContext } from '../../src/test/helpers.js';

describe('DelegationEngine', () => {
  let engine: DelegationEngine;
  let mockProvider: MockVSCodeLMProvider;

  beforeEach(() => {
    mockProvider = new MockVSCodeLMProvider();
    mockProvider.setDefaultResponse({
      content: '## Summary\nTest analysis result\n\n## Recommendations\n- Item 1',
      finishReason: 'stop',
    });
    engine = new DelegationEngine(mockProvider, undefined, {
      enableConstitutionCheck: false,
      enforceTraceability: false,
    });
  });

  describe('delegate', () => {
    it('should delegate task to detected expert', async () => {
      const task = createTestTask({
        context: createTestContext({
          userMessage: 'Review the architecture design',
        }),
      });

      const result = await engine.delegate(task);
      expect(result.success).toBe(true);
      expect(result.expertType).toBe('architect');
    });

    it('should use explicit expert when specified', async () => {
      const task = createTestTask({
        expertType: 'security-analyst',
        context: createTestContext({
          userMessage: 'Check something',
        }),
      });

      const result = await engine.delegate(task);
      expect(result.success).toBe(true);
      expect(result.expertType).toBe('security-analyst');
    });

    it('should execute in advisory mode by default', async () => {
      const task = createTestTask({
        expertType: 'architect',
      });

      const result = await engine.delegate(task);
      expect(result.mode).toBe('advisory');
    });

    it('should execute in implementation mode when specified', async () => {
      mockProvider.setDefaultResponse({
        content: '```typescript\nconst x = 1;\n```',
        finishReason: 'stop',
      });

      const task = createTestTask({
        expertType: 'architect',
        mode: 'implementation',
        context: createTestContext({
          mode: 'implementation',
        }),
      });

      const result = await engine.delegate(task);
      expect(result.mode).toBe('implementation');
    });
  });

  describe('delegateSimple', () => {
    it('should delegate with minimal parameters', async () => {
      const result = await engine.delegateSimple('How should I structure this?');
      expect(result.success).toBe(true);
    });

    it('should accept explicit expert', async () => {
      const result = await engine.delegateSimple('Check this', {
        expertType: 'code-reviewer',
      });
      expect(result.expertType).toBe('code-reviewer');
    });

    it('should accept mode option', async () => {
      mockProvider.setDefaultResponse({
        content: '```typescript\nconst code = true;\n```',
        finishReason: 'stop',
      });

      const result = await engine.delegateSimple('Generate code', {
        expertType: 'architect',
        mode: 'implementation',
      });
      expect(result.mode).toBe('implementation');
    });
  });

  describe('analyze', () => {
    it('should execute in advisory mode', async () => {
      const result = await engine.analyze('Check the security');
      expect(result.mode).toBe('advisory');
    });
  });

  describe('generate', () => {
    it('should execute in implementation mode', async () => {
      mockProvider.setDefaultResponse({
        content: '```typescript\nfunction test() {}\n```',
        finishReason: 'stop',
      });

      const result = await engine.generate('Create a function', 'architect');
      expect(result.mode).toBe('implementation');
    });
  });

  describe('retry', () => {
    it('should retry with feedback', async () => {
      const previousResult = {
        success: false,
        expertType: 'architect' as const,
        mode: 'advisory' as const,
        content: 'Failed response',
        confidence: 0,
      };

      mockProvider.setDefaultResponse({
        content: 'Improved response',
        finishReason: 'stop',
      });

      const result = await engine.retry('task-1', previousResult, 'Please improve');
      expect(result.success).toBe(true);
    });
  });

  describe('escalate', () => {
    it('should escalate to higher expert', async () => {
      const context = createTestContext({
        userMessage: 'Complex task',
      });

      const result = await engine.escalate('task-1', 'security-analyst', context);
      // Security analyst escalates to architect
      expect(result).toBeDefined();
    });

    it('should fail for top-level expert', async () => {
      const context = createTestContext({
        userMessage: 'Complex task',
      });

      const result = await engine.escalate('task-1', 'architect', context);
      // Architect has no escalation target
      expect(result.success).toBe(false);
      expect(result.metadata?.escalationFailed).toBe(true);
    });
  });

  describe('constitution check', () => {
    it('should block implementation without requirements', async () => {
      const engineWithConstitution = new DelegationEngine(mockProvider, undefined, {
        enableConstitutionCheck: true,
        enforceTraceability: false,
      });

      const task = createTestTask({
        expertType: 'architect',
        mode: 'implementation',
        context: createTestContext({
          mode: 'implementation',
          relatedRequirements: undefined,
          relatedDesigns: undefined,
        }),
      });

      const result = await engineWithConstitution.delegate(task);
      expect(result.success).toBe(false);
      expect(result.metadata?.constitutionViolations).toBeDefined();
    });

    it('should allow implementation with requirements', async () => {
      const engineWithConstitution = new DelegationEngine(mockProvider, undefined, {
        enableConstitutionCheck: true,
        enforceTraceability: false,
      });

      mockProvider.setDefaultResponse({
        content: '```typescript\n// Implementation\n```',
        finishReason: 'stop',
      });

      const task = createTestTask({
        expertType: 'architect',
        mode: 'implementation',
        context: createTestContext({
          mode: 'implementation',
          relatedRequirements: ['THE system SHALL authenticate users'],
          relatedDesigns: ['DES-001'],
        }),
      });

      const result = await engineWithConstitution.delegate(task);
      expect(result.success).toBe(true);
    });
  });

  describe('getExpertManager', () => {
    it('should return expert manager', () => {
      const manager = engine.getExpertManager();
      expect(manager).toBeDefined();
      expect(manager.getAllExperts().length).toBe(7);
    });
  });

  describe('getSemanticRouter', () => {
    it('should return semantic router', () => {
      const router = engine.getSemanticRouter();
      expect(router).toBeDefined();
    });
  });
});
