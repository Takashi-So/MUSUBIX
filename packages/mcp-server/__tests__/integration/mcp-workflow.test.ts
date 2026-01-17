/**
 * MUSUBIX MCP Server Integration Tests
 * 
 * Tests the integration between MCP Server tools and core functionality
 * 
 * @see REQ-INT-102 - MCP Protocol Support
 * @see REQ-INT-102 - SDD Workflow
 */

import { describe, it, expect } from 'vitest';
import {
  createRequirementsTool,
  validateRequirementsTool,
  createDesignTool,
  validateDesignTool,
  createTasksTool,
  queryKnowledgeTool,
  updateKnowledgeTool,
  validateConstitutionTool,
  validateTraceabilityTool,
} from '../../src/tools/sdd-tools.js';

/**
 * Helper to parse tool result content
 */
function parseResult(result: { content: Array<{ type: string; text: string }> }): unknown {
  const textContent = result.content.find(c => c.type === 'text');
  if (!textContent) return null;
  try {
    return JSON.parse(textContent.text);
  } catch {
    return textContent.text;
  }
}

describe('Integration: MCP Server Workflow', () => {
  describe('Requirements Management Workflow', () => {
    it('should create requirements document or request clarification', async () => {
      const result = await createRequirementsTool.handler({
        projectName: 'TestProject',
        featureName: 'User Authentication',
        description: 'Authentication requirements for user login',
      });

      expect(result.isError).toBeFalsy();
      const parsed = parseResult(result) as { status?: string; action?: string; needsClarification?: boolean };
      // v3.3.9: ヒアリング機能により、コンテキスト不足時は clarification_needed
      if (parsed.needsClarification) {
        expect(parsed.action).toBe('clarification_needed');
      } else {
        expect(parsed.status).toBe('template_created');
      }
    });

    it('should validate requirements document', async () => {
      const result = await validateRequirementsTool.handler({
        documentPath: 'test-doc.md',
        strictMode: false,
      });

      expect(result.isError).toBeFalsy();
      const parsed = parseResult(result) as { action: string };
      expect(parsed.action).toBe('validate_requirements');
    });
  });

  describe('Design Workflow', () => {
    it('should create design document or request clarification', async () => {
      const result = await createDesignTool.handler({
        projectName: 'TestProject',
        componentName: 'PaymentService',
        requirementsId: 'REQ-001',
      });

      expect(result.isError).toBeFalsy();
      const parsed = parseResult(result) as { status?: string; action?: string; needsClarification?: boolean };
      // v3.3.9: ヒアリング機能により、コンテキスト不足時は clarification_needed
      if (parsed.needsClarification) {
        expect(parsed.action).toBe('clarification_needed');
      } else {
        expect(parsed.status).toBe('template_created');
      }
    });

    it('should validate design document', async () => {
      const result = await validateDesignTool.handler({
        documentPath: 'design-doc.md',
      });

      expect(result.isError).toBeFalsy();
      const parsed = parseResult(result) as { action: string };
      expect(parsed.action).toBe('validate_design');
    });
  });

  describe('Task Generation Workflow', () => {
    it('should create tasks from design', async () => {
      const result = await createTasksTool.handler({
        designId: 'DES-001',
        projectName: 'TestProject',
      });

      expect(result.isError).toBeFalsy();
      const parsed = parseResult(result) as { status: string };
      expect(parsed.status).toBe('tasks_generated');
    });
  });

  describe('Knowledge Graph Integration', () => {
    it('should query knowledge graph', async () => {
      const result = await queryKnowledgeTool.handler({
        query: 'authentication patterns',
        ontologyTypes: ['Pattern'],
      });

      expect(result.isError).toBeFalsy();
      const parsed = parseResult(result) as { action: string };
      expect(parsed.action).toBe('query_knowledge');
    });

    it('should update knowledge graph', async () => {
      const result = await updateKnowledgeTool.handler({
        entityType: 'Component',
        entityId: 'AuthService',
        properties: { type: 'service', patterns: ['singleton'] },
      });

      expect(result.isError).toBeFalsy();
      const parsed = parseResult(result) as { status: string };
      expect(parsed.status).toBe('pending');
    });
  });

  describe('Validation Workflows', () => {
    it('should validate constitutional compliance', async () => {
      const result = await validateConstitutionTool.handler({
        documentPath: 'test-doc.md',
        articles: ['I', 'II', 'III'],
      });

      expect(result.isError).toBeFalsy();
      const parsed = parseResult(result) as { action: string };
      expect(parsed.action).toBe('validate_constitution');
    });

    it('should validate traceability', async () => {
      const result = await validateTraceabilityTool.handler({
        projectPath: './test-project',
      });

      expect(result.isError).toBeFalsy();
      const parsed = parseResult(result) as { action: string };
      expect(parsed.action).toBe('validate_traceability');
    });
  });

  describe('End-to-End SDD Tool Workflow', () => {
    it('should complete tool sequence without errors', async () => {
      // 1. Create requirements
      const reqResult = await createRequirementsTool.handler({
        projectName: 'E2ETest',
        featureName: 'NotificationService',
        description: 'Notification service requirements',
      });
      expect(reqResult.isError).toBeFalsy();

      // 2. Validate requirements
      const validateReqResult = await validateRequirementsTool.handler({
        documentPath: 'requirements.md',
      });
      expect(validateReqResult.isError).toBeFalsy();

      // 3. Create design
      const designResult = await createDesignTool.handler({
        projectName: 'E2ETest',
        componentName: 'NotificationService',
        requirementsId: 'REQ-NOTIFICATION-001',
      });
      expect(designResult.isError).toBeFalsy();

      // 4. Validate design
      const validateDesignResult = await validateDesignTool.handler({
        documentPath: 'design.md',
      });
      expect(validateDesignResult.isError).toBeFalsy();

      // 5. Create tasks
      const taskResult = await createTasksTool.handler({
        designId: 'DES-NOTIFICATION-001',
        projectName: 'E2ETest',
      });
      expect(taskResult.isError).toBeFalsy();

      // 6. Update knowledge
      const knowledgeResult = await updateKnowledgeTool.handler({
        entityType: 'Component',
        entityId: 'NotificationService',
        properties: { patterns: ['strategy', 'adapter'] },
      });
      expect(knowledgeResult.isError).toBeFalsy();

      // 7. Validate constitution
      const constitutionResult = await validateConstitutionTool.handler({
        documentPath: 'requirements.md',
        articles: ['IV', 'V'],
      });
      expect(constitutionResult.isError).toBeFalsy();

      // 8. Validate traceability
      const traceResult = await validateTraceabilityTool.handler({
        projectPath: './E2ETest',
      });
      expect(traceResult.isError).toBeFalsy();
    });
  });

  describe('Error Handling', () => {
    it('should handle missing required parameters', async () => {
      // Most handlers have optional parameters or defaults
      // Test with minimal input
      const result = await createRequirementsTool.handler({
        projectName: 'Test',
        featureName: 'Feature',
      });
      expect(result.isError).toBeFalsy();
    });
  });
});

describe('Integration: Constitutional Article Compliance', () => {
  describe('Article IV: EARS Format', () => {
    it('should validate requirements in strict mode', async () => {
      const result = await validateRequirementsTool.handler({
        documentPath: 'requirements.md',
        strictMode: true,
      });

      expect(result.isError).toBeFalsy();
      const parsed = parseResult(result) as { action: string };
      expect(parsed.action).toBe('validate_requirements');
    });
  });

  describe('Article V: Traceability', () => {
    it('should validate full traceability chain', async () => {
      const result = await validateTraceabilityTool.handler({
        projectPath: './project',
        fullChain: true,
      });

      expect(result.isError).toBeFalsy();
      const parsed = parseResult(result) as { action: string };
      expect(parsed.action).toBe('validate_traceability');
    });
  });

  describe('Article VII: Design Patterns', () => {
    it('should create design with pattern documentation', async () => {
      const result = await createDesignTool.handler({
        projectName: 'PatternTest',
        componentName: 'ConfigManager',
        requirementsId: 'REQ-001',
        patterns: ['singleton', 'factory'],
      });

      expect(result.isError).toBeFalsy();
      const parsed = parseResult(result) as { status?: string; action?: string; needsClarification?: boolean };
      // v3.3.9: ヒアリング機能により、コンテキスト不足時は clarification_needed
      if (parsed.needsClarification) {
        expect(parsed.action).toBe('clarification_needed');
      } else {
        expect(parsed.status).toBe('template_created');
      }
    });
  });
});
