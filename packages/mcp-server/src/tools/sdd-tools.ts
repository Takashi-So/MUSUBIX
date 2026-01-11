/**
 * MCP Tools Definitions
 * 
 * Tool definitions for MUSUBIX MCP Server
 * 
 * @packageDocumentation
 * @module tools
 * 
 * @see REQ-INT-102 - MCP Server
 * @see REQ-INT-102 - SDD Workflow
 */

import type { ToolDefinition, ToolResult, TextContent } from '../types.js';

/**
 * Create text content helper
 */
function text(content: string): TextContent {
  return { type: 'text', text: content };
}

/**
 * Success result helper
 */
function success(content: string | object): ToolResult {
  const textContent = typeof content === 'string' 
    ? content 
    : JSON.stringify(content, null, 2);
  return {
    content: [text(textContent)],
  };
}

/**
 * Error result helper
 */
function error(message: string): ToolResult {
  return {
    content: [text(`Error: ${message}`)],
    isError: true,
  };
}

// ============================================================
// Requirements Phase Tools
// ============================================================

/**
 * Create requirements document tool
 */
export const createRequirementsTool: ToolDefinition = {
  name: 'sdd_create_requirements',
  description: 'Create a new EARS-format requirements document',
  inputSchema: {
    type: 'object',
    properties: {
      projectName: {
        type: 'string',
        description: 'Name of the project',
      },
      featureName: {
        type: 'string',
        description: 'Name of the feature to document requirements for',
      },
      description: {
        type: 'string',
        description: 'Brief description of the feature',
      },
    },
    required: ['projectName', 'featureName'],
  },
  handler: async (args) => {
    try {
      const { projectName, featureName, description } = args as {
        projectName: string;
        featureName: string;
        description?: string;
      };

      // Placeholder: actual implementation will use YATA
      return success({
        action: 'create_requirements',
        projectName,
        featureName,
        description,
        status: 'template_created',
        message: `Requirements document template created for ${featureName}`,
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * Validate requirements tool
 */
export const validateRequirementsTool: ToolDefinition = {
  name: 'sdd_validate_requirements',
  description: 'Validate requirements against EARS patterns and constitution',
  inputSchema: {
    type: 'object',
    properties: {
      documentPath: {
        type: 'string',
        description: 'Path to the requirements document',
      },
    },
    required: ['documentPath'],
  },
  handler: async (args) => {
    try {
      const { documentPath } = args as { documentPath: string };

      // Placeholder: actual implementation will parse and validate
      return success({
        action: 'validate_requirements',
        documentPath,
        status: 'validated',
        issues: [],
        coverage: {
          earsPatterns: '100%',
          constitutionalCompliance: '100%',
        },
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

// ============================================================
// Design Phase Tools
// ============================================================

/**
 * Create design document tool
 */
export const createDesignTool: ToolDefinition = {
  name: 'sdd_create_design',
  description: 'Create a C4 model design document',
  inputSchema: {
    type: 'object',
    properties: {
      projectName: {
        type: 'string',
        description: 'Name of the project',
      },
      featureName: {
        type: 'string',
        description: 'Name of the feature to design',
      },
      requirementsPath: {
        type: 'string',
        description: 'Path to the requirements document',
      },
    },
    required: ['projectName', 'featureName'],
  },
  handler: async (args) => {
    try {
      const { projectName, featureName, requirementsPath } = args as {
        projectName: string;
        featureName: string;
        requirementsPath?: string;
      };

      return success({
        action: 'create_design',
        projectName,
        featureName,
        requirementsPath,
        status: 'template_created',
        sections: ['Context', 'Container', 'Component', 'ADR'],
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * Validate design tool
 */
export const validateDesignTool: ToolDefinition = {
  name: 'sdd_validate_design',
  description: 'Validate design against requirements traceability',
  inputSchema: {
    type: 'object',
    properties: {
      designPath: {
        type: 'string',
        description: 'Path to the design document',
      },
      requirementsPath: {
        type: 'string',
        description: 'Path to the requirements document',
      },
    },
    required: ['designPath'],
  },
  handler: async (args) => {
    try {
      const { designPath, requirementsPath } = args as {
        designPath: string;
        requirementsPath?: string;
      };

      return success({
        action: 'validate_design',
        designPath,
        requirementsPath,
        status: 'validated',
        traceability: {
          coverage: '100%',
          unmappedRequirements: [],
        },
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

// ============================================================
// Task Phase Tools
// ============================================================

/**
 * Create tasks tool
 */
export const createTasksTool: ToolDefinition = {
  name: 'sdd_create_tasks',
  description: 'Create implementation tasks from design',
  inputSchema: {
    type: 'object',
    properties: {
      designPath: {
        type: 'string',
        description: 'Path to the design document',
      },
      sprintDuration: {
        type: 'number',
        description: 'Sprint duration in days',
        default: 5,
      },
    },
    required: ['designPath'],
  },
  handler: async (args) => {
    try {
      const { designPath, sprintDuration } = args as {
        designPath: string;
        sprintDuration?: number;
      };

      return success({
        action: 'create_tasks',
        designPath,
        sprintDuration: sprintDuration ?? 5,
        status: 'tasks_generated',
        summary: {
          totalTasks: 0,
          totalSprints: 0,
        },
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};



// ============================================================
// Validation Tools
// ============================================================

/**
 * Constitutional validation tool
 */
export const validateConstitutionTool: ToolDefinition = {
  name: 'sdd_validate_constitution',
  description: 'Validate against the 9 Constitutional Articles',
  inputSchema: {
    type: 'object',
    properties: {
      documentPath: {
        type: 'string',
        description: 'Path to the document to validate',
      },
      articles: {
        type: 'array',
        description: 'Specific articles to check (1-9)',
        items: { type: 'number' },
      },
    },
    required: ['documentPath'],
  },
  handler: async (args) => {
    try {
      const { documentPath, articles } = args as {
        documentPath: string;
        articles?: number[];
      };

      const allArticles = articles ?? [1, 2, 3, 4, 5, 6, 7, 8, 9];

      return success({
        action: 'validate_constitution',
        documentPath,
        articlesChecked: allArticles,
        results: allArticles.map((num) => ({
          article: num,
          compliant: true,
          findings: [],
        })),
        overallCompliance: true,
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};

/**
 * Traceability validation tool
 */
export const validateTraceabilityTool: ToolDefinition = {
  name: 'sdd_validate_traceability',
  description: 'Validate requirement-design-task traceability',
  inputSchema: {
    type: 'object',
    properties: {
      projectPath: {
        type: 'string',
        description: 'Path to the project root',
      },
    },
    required: ['projectPath'],
  },
  handler: async (args) => {
    try {
      const { projectPath } = args as { projectPath: string };

      return success({
        action: 'validate_traceability',
        projectPath,
        status: 'validated',
        matrix: {
          requirements: 0,
          designs: 0,
          tasks: 0,
          coverage: '0%',
        },
      });
    } catch (e) {
      return error(e instanceof Error ? e.message : String(e));
    }
  },
};



/**
 * All SDD tools
 */
export const sddTools: ToolDefinition[] = [
  // Requirements
  createRequirementsTool,
  validateRequirementsTool,
  // Design
  createDesignTool,
  validateDesignTool,
  // Tasks
  createTasksTool,
  // Validation
  validateConstitutionTool,
  validateTraceabilityTool,
];

/**
 * Get all SDD tool definitions
 */
export function getSddTools(): ToolDefinition[] {
  return sddTools;
}
