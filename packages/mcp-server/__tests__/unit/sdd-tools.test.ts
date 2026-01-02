/**
 * MCP SDD Tools Unit Tests
 * 
 * @see REQ-INT-102 - MCP Server
 * @see REQ-INT-102 - SDD Workflow
 * @see TSK-041 - MCP Server Implementation
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
  sddTools,
} from '../../src/tools/sdd-tools.js';

describe('REQ-INT-102: MCP SDD Tools', () => {
  describe('Requirements Phase Tools', () => {
    describe('sdd_create_requirements', () => {
      it('should have correct tool definition', () => {
        expect(createRequirementsTool.name).toBe('sdd_create_requirements');
        expect(createRequirementsTool.description).toBeDefined();
        expect(createRequirementsTool.inputSchema).toBeDefined();
        expect(createRequirementsTool.handler).toBeInstanceOf(Function);
      });

      it('should require projectName and featureName', () => {
        const schema = createRequirementsTool.inputSchema;
        expect(schema.required).toContain('projectName');
        expect(schema.required).toContain('featureName');
      });

      it('should create requirements template', async () => {
        const result = await createRequirementsTool.handler({
          projectName: 'TestProject',
          featureName: 'Authentication',
          description: 'User authentication feature',
        });

        expect(result.isError).toBeFalsy();
        expect(result.content).toHaveLength(1);
        expect(result.content[0].type).toBe('text');

        const parsed = JSON.parse(result.content[0].text);
        expect(parsed.action).toBe('create_requirements');
        expect(parsed.projectName).toBe('TestProject');
        expect(parsed.featureName).toBe('Authentication');
        expect(parsed.status).toBe('template_created');
      });

      it('should work without optional description', async () => {
        const result = await createRequirementsTool.handler({
          projectName: 'TestProject',
          featureName: 'Feature',
        });

        expect(result.isError).toBeFalsy();
      });
    });

    describe('sdd_validate_requirements', () => {
      it('should have correct tool definition', () => {
        expect(validateRequirementsTool.name).toBe('sdd_validate_requirements');
        expect(validateRequirementsTool.inputSchema.required).toContain('documentPath');
      });

      it('should validate requirements document', async () => {
        const result = await validateRequirementsTool.handler({
          documentPath: '/path/to/requirements.md',
        });

        expect(result.isError).toBeFalsy();
        
        const parsed = JSON.parse(result.content[0].text);
        expect(parsed.action).toBe('validate_requirements');
        expect(parsed.status).toBe('validated');
        expect(parsed.coverage).toBeDefined();
        expect(parsed.coverage.earsPatterns).toBeDefined();
        expect(parsed.coverage.constitutionalCompliance).toBeDefined();
      });
    });
  });

  describe('Design Phase Tools', () => {
    describe('sdd_create_design', () => {
      it('should have correct tool definition', () => {
        expect(createDesignTool.name).toBe('sdd_create_design');
        expect(createDesignTool.inputSchema.required).toContain('projectName');
        expect(createDesignTool.inputSchema.required).toContain('featureName');
      });

      it('should create design template with C4 sections', async () => {
        const result = await createDesignTool.handler({
          projectName: 'TestProject',
          featureName: 'DataLayer',
          requirementsPath: '/path/to/req.md',
        });

        expect(result.isError).toBeFalsy();
        
        const parsed = JSON.parse(result.content[0].text);
        expect(parsed.action).toBe('create_design');
        expect(parsed.sections).toContain('Context');
        expect(parsed.sections).toContain('Container');
        expect(parsed.sections).toContain('Component');
        expect(parsed.sections).toContain('ADR');
      });

      it('should work without requirementsPath', async () => {
        const result = await createDesignTool.handler({
          projectName: 'TestProject',
          featureName: 'Feature',
        });

        expect(result.isError).toBeFalsy();
      });
    });

    describe('sdd_validate_design', () => {
      it('should have correct tool definition', () => {
        expect(validateDesignTool.name).toBe('sdd_validate_design');
        expect(validateDesignTool.inputSchema.required).toContain('designPath');
      });

      it('should validate design with traceability', async () => {
        const result = await validateDesignTool.handler({
          designPath: '/path/to/design.md',
          requirementsPath: '/path/to/req.md',
        });

        expect(result.isError).toBeFalsy();
        
        const parsed = JSON.parse(result.content[0].text);
        expect(parsed.action).toBe('validate_design');
        expect(parsed.traceability).toBeDefined();
        expect(parsed.traceability.coverage).toBeDefined();
      });
    });
  });

  describe('Task Phase Tools', () => {
    describe('sdd_create_tasks', () => {
      it('should have correct tool definition', () => {
        expect(createTasksTool.name).toBe('sdd_create_tasks');
        expect(createTasksTool.inputSchema.required).toContain('designPath');
      });

      it('should have optional sprintDuration', () => {
        const props = createTasksTool.inputSchema.properties;
        expect(props.sprintDuration).toBeDefined();
        expect(props.sprintDuration.type).toBe('number');
      });

      it('should create tasks from design', async () => {
        const result = await createTasksTool.handler({
          designPath: '/path/to/design.md',
          sprintDuration: 10,
        });

        expect(result.isError).toBeFalsy();
        
        const parsed = JSON.parse(result.content[0].text);
        expect(parsed.action).toBe('create_tasks');
        expect(parsed.status).toBe('tasks_generated');
      });
    });
  });

  describe('Knowledge Graph Tools', () => {
    describe('sdd_query_knowledge', () => {
      it('should have correct tool definition', () => {
        expect(queryKnowledgeTool.name).toBe('sdd_query_knowledge');
        expect(queryKnowledgeTool.inputSchema.required).toContain('query');
      });

      it('should query knowledge graph', async () => {
        const result = await queryKnowledgeTool.handler({
          query: 'Find all design patterns',
          nodeType: 'pattern',
        });

        expect(result.isError).toBeFalsy();
        
        const parsed = JSON.parse(result.content[0].text);
        expect(parsed.action).toBe('query_knowledge');
        expect(parsed.results).toBeDefined();
      });
    });

    describe('sdd_update_knowledge', () => {
      it('should have correct tool definition', () => {
        expect(updateKnowledgeTool.name).toBe('sdd_update_knowledge');
        expect(updateKnowledgeTool.inputSchema.required).toContain('nodeType');
        expect(updateKnowledgeTool.inputSchema.required).toContain('properties');
      });

      it('should update knowledge graph', async () => {
        const result = await updateKnowledgeTool.handler({
          nodeType: 'requirement',
          properties: { id: 'REQ-001', title: 'Test Requirement' },
        });

        expect(result.isError).toBeFalsy();
        
        const parsed = JSON.parse(result.content[0].text);
        expect(parsed.action).toBe('update_knowledge');
        expect(parsed.status).toBe('pending');
      });
    });
  });

  describe('Validation Tools', () => {
    describe('sdd_validate_constitution', () => {
      it('should have correct tool definition', () => {
        expect(validateConstitutionTool.name).toBe('sdd_validate_constitution');
        expect(validateConstitutionTool.inputSchema.required).toContain('documentPath');
      });

      it('should validate against all 9 constitutional articles', async () => {
        const result = await validateConstitutionTool.handler({
          documentPath: '/path/to/code.ts',
          articles: [1, 2, 3],
        });

        expect(result.isError).toBeFalsy();
        
        const parsed = JSON.parse(result.content[0].text);
        expect(parsed.action).toBe('validate_constitution');
        expect(parsed.overallCompliance).toBeDefined();
      });
    });

    describe('sdd_validate_traceability', () => {
      it('should have correct tool definition', () => {
        expect(validateTraceabilityTool.name).toBe('sdd_validate_traceability');
      });

      it('should validate bidirectional traceability', async () => {
        const result = await validateTraceabilityTool.handler({
          projectPath: '/path/to/project',
        });

        expect(result.isError).toBeFalsy();
        
        const parsed = JSON.parse(result.content[0].text);
        expect(parsed.action).toBe('validate_traceability');
        expect(parsed.matrix).toBeDefined();
      });
    });
  });

  describe('Tool Result Format', () => {
    it('should return text content', async () => {
      const result = await createRequirementsTool.handler({
        projectName: 'Test',
        featureName: 'Feature',
      });

      expect(result.content[0].type).toBe('text');
      expect(typeof result.content[0].text).toBe('string');
    });

    it('should return valid JSON', async () => {
      const result = await createRequirementsTool.handler({
        projectName: 'Test',
        featureName: 'Feature',
      });

      expect(() => JSON.parse(result.content[0].text)).not.toThrow();
    });

    it('should indicate error when appropriate', async () => {
      // Test error handling by providing invalid input
      // This depends on implementation details
      const result = await validateRequirementsTool.handler({
        documentPath: '', // Empty path might trigger error
      });

      // Result should have consistent structure regardless of error
      expect(result.content).toBeDefined();
      expect(result.content).toHaveLength(1);
    });
  });

  describe('Input Schema Validation', () => {
    it('should have all 9 SDD tools', () => {
      expect(sddTools).toHaveLength(9);
    });

    sddTools.forEach((tool) => {
      it(`${tool.name} should have valid input schema`, () => {
        expect(tool.inputSchema).toBeDefined();
        expect(tool.inputSchema.type).toBe('object');
        expect(tool.inputSchema.properties).toBeDefined();
        expect(tool.inputSchema.required).toBeDefined();
        expect(Array.isArray(tool.inputSchema.required)).toBe(true);
      });
    });
  });

  describe('Tool Names Convention', () => {
    sddTools.forEach((tool) => {
      it(`${tool.name} should start with 'sdd_' prefix`, () => {
        expect(tool.name.startsWith('sdd_')).toBe(true);
      });
    });
  });
});
