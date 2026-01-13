/**
 * @nahisaho/musubix-expert-delegation
 * MCP Tool Handlers Tests
 *
 * Traces to: REQ-INT-001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { MCPToolHandlers } from '../../src/mcp/handlers.js';
import { MockVSCodeLMProvider } from '../../src/test/mocks.js';

describe('MCPToolHandlers', () => {
  let handlers: MCPToolHandlers;
  let mockProvider: MockVSCodeLMProvider;

  beforeEach(() => {
    mockProvider = new MockVSCodeLMProvider();
    mockProvider.setDefaultResponse({
      content: '## Analysis\nTest response',
      finishReason: 'stop',
    });
    handlers = new MCPToolHandlers(mockProvider);
  });

  describe('handleExpertDelegate', () => {
    it('should delegate to auto-detected expert', async () => {
      const result = await handlers.handleExpertDelegate({
        message: 'Review the architecture',
      });

      expect(result.isError).toBeFalsy();
      expect(result.content[0].text).toContain('Analysis');
    });

    it('should delegate to explicit expert', async () => {
      const result = await handlers.handleExpertDelegate({
        message: 'Check this',
        expert: 'security-analyst',
      });

      expect(result.isError).toBeFalsy();
    });

    it('should support mode option', async () => {
      mockProvider.setDefaultResponse({
        content: '```typescript\ncode\n```',
        finishReason: 'stop',
      });

      const result = await handlers.handleExpertDelegate({
        message: 'Generate code',
        expert: 'architect',
        mode: 'implementation',
        relatedRequirements: ['THE system SHALL provide user authentication'],
        relatedDesigns: ['DES-TEST-001'],
        traceLinks: ['REQ-TEST-001 -> DES-TEST-001'],
      });

      expect(result.isError).toBeFalsy();
    });
  });

  describe('handleExpertArchitect', () => {
    it('should delegate to architect', async () => {
      const result = await handlers.handleExpertArchitect({
        message: 'Design a system',
      });

      expect(result.isError).toBeFalsy();
    });

    it('should include constraints', async () => {
      const result = await handlers.handleExpertArchitect({
        message: 'Design a system',
        constraints: ['Must be scalable', 'Use microservices'],
      });

      expect(result.isError).toBeFalsy();
    });
  });

  describe('handleExpertSecurity', () => {
    it('should analyze code for vulnerabilities', async () => {
      const result = await handlers.handleExpertSecurity({
        code: 'const password = "secret123"',
      });

      expect(result.isError).toBeFalsy();
    });

    it('should support threat modeling', async () => {
      const result = await handlers.handleExpertSecurity({
        code: 'function auth() {}',
        threatModel: true,
      });

      expect(result.isError).toBeFalsy();
    });
  });

  describe('handleExpertReview', () => {
    it('should review code', async () => {
      const result = await handlers.handleExpertReview({
        code: 'function test() { return 1; }',
        language: 'typescript',
      });

      expect(result.isError).toBeFalsy();
    });

    it('should support focus areas', async () => {
      const result = await handlers.handleExpertReview({
        code: 'function test() {}',
        focus: ['performance', 'readability'],
      });

      expect(result.isError).toBeFalsy();
    });
  });

  describe('handleExpertPlan', () => {
    it('should review plan', async () => {
      const result = await handlers.handleExpertPlan({
        plan: 'Create a user authentication system',
      });

      expect(result.isError).toBeFalsy();
    });

    it('should check constitution by default', async () => {
      const result = await handlers.handleExpertPlan({
        plan: 'Implementation plan',
        checkConstitution: true,
      });

      expect(result.isError).toBeFalsy();
    });
  });

  describe('handleExpertEars', () => {
    it('should convert to EARS format', async () => {
      const result = await handlers.handleExpertEars({
        requirements: 'The system must authenticate users',
      });

      expect(result.isError).toBeFalsy();
    });

    it('should accept suggested pattern', async () => {
      const result = await handlers.handleExpertEars({
        requirements: 'When user logs in',
        suggestedPattern: 'event-driven',
      });

      expect(result.isError).toBeFalsy();
    });
  });

  describe('handleExpertFormal', () => {
    it('should perform formal verification', async () => {
      const result = await handlers.handleExpertFormal({
        code: 'function add(a, b) { return a + b; }',
      });

      expect(result.isError).toBeFalsy();
    });

    it('should support output format', async () => {
      const result = await handlers.handleExpertFormal({
        code: 'function f() {}',
        outputFormat: 'lean4',
      });

      expect(result.isError).toBeFalsy();
    });
  });

  describe('handleExpertOntology', () => {
    it('should perform ontology reasoning', async () => {
      const result = await handlers.handleExpertOntology({
        query: 'What is related to User?',
      });

      expect(result.isError).toBeFalsy();
    });

    it('should accept context triples', async () => {
      const result = await handlers.handleExpertOntology({
        query: 'Infer relationships',
        triples: [
          { s: 'User', p: 'hasRole', o: 'Admin' },
        ],
      });

      expect(result.isError).toBeFalsy();
    });
  });

  describe('handleTriggerDetect', () => {
    it('should detect expert from message', async () => {
      const result = await handlers.handleTriggerDetect({
        message: 'Review the architecture',
      });

      expect(result.isError).toBeFalsy();
      const data = JSON.parse(result.content[0].text);
      expect(data.detected).toBe(true);
      expect(data.expert).toBe('architect');
    });

    it('should return confidence score', async () => {
      const result = await handlers.handleTriggerDetect({
        message: 'Check EARS format',
      });

      const data = JSON.parse(result.content[0].text);
      expect(data.confidence).toBeGreaterThan(0);
    });
  });

  describe('handleDelegationRetry', () => {
    it('should return error for unknown task', async () => {
      const result = await handlers.handleDelegationRetry({
        taskId: 'unknown-task',
      });

      expect(result.isError).toBe(true);
      expect(result.content[0].text).toContain('not found');
    });

    it('should retry saved task', async () => {
      // First save a task result
      handlers.saveTaskResult('task-1', {
        success: false,
        expertType: 'architect',
        mode: 'advisory',
        content: 'Previous failure',
        confidence: 0,
      });

      const result = await handlers.handleDelegationRetry({
        taskId: 'task-1',
        feedback: 'Please try again',
      });

      expect(result.isError).toBeFalsy();
    });
  });

  describe('handleProviderSelect', () => {
    it('should select model', async () => {
      const result = await handlers.handleProviderSelect({});

      expect(result.isError).toBeFalsy();
      const data = JSON.parse(result.content[0].text);
      expect(data.status).toBe('ready');
    });

    it('should accept criteria', async () => {
      const result = await handlers.handleProviderSelect({
        criteria: { family: 'gpt-4' },
        temperature: 0.5,
      });

      expect(result.isError).toBeFalsy();
    });
  });

  describe('task management', () => {
    it('should save and clear task results', () => {
      handlers.saveTaskResult('task-1', {
        success: true,
        expertType: 'architect',
        mode: 'advisory',
        content: 'Result',
        confidence: 0.9,
      });

      handlers.clearTaskResult('task-1');
      // No direct way to verify, but should not throw
    });
  });
});
