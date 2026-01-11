/**
 * Policy Tools - MCP tools for Policy validation
 * 
 * @packageDocumentation
 * @module tools/policy-tools
 */

import { Tool } from '@modelcontextprotocol/sdk/types.js';
import {
  createPolicyEngine,
  PolicyEngine,
  ValidationContext,
  ValidationReport,
  constitutionPolicies,
  PolicyCategory,
} from '@musubix/policy';

// Singleton engine instance
let policyEngine: PolicyEngine | null = null;

/**
 * Get or create policy engine
 */
export function getPolicyEngine(): PolicyEngine {
  if (!policyEngine) {
    policyEngine = createPolicyEngine() as PolicyEngine;
  }
  return policyEngine;
}

/**
 * Reset policy engine (for testing)
 */
export function resetPolicyEngine(): void {
  policyEngine = null;
}

// Tool definitions
export const policyValidateTool: Tool = {
  name: 'policy_validate',
  description: 'Validate a project against all registered policies',
  inputSchema: {
    type: 'object',
    properties: {
      projectPath: { type: 'string', description: 'Path to the project to validate' },
      policyIds: { 
        type: 'array', 
        items: { type: 'string' },
        description: 'Specific policy IDs to validate (optional, defaults to all)' 
      },
    },
    required: [],
  },
};

export const policyListTool: Tool = {
  name: 'policy_list',
  description: 'List all registered policies',
  inputSchema: {
    type: 'object',
    properties: {
      category: { 
        type: 'string', 
        description: 'Filter by category (e.g., "constitution", "custom")' 
      },
    },
    required: [],
  },
};

export const policyGetTool: Tool = {
  name: 'policy_get',
  description: 'Get details of a specific policy',
  inputSchema: {
    type: 'object',
    properties: {
      id: { type: 'string', description: 'Policy ID' },
    },
    required: ['id'],
  },
};

export const policyCheckFileTool: Tool = {
  name: 'policy_check_file',
  description: 'Check a specific file against relevant policies',
  inputSchema: {
    type: 'object',
    properties: {
      filePath: { type: 'string', description: 'Path to the file to check' },
      content: { type: 'string', description: 'File content (optional, will be read if not provided)' },
    },
    required: ['filePath'],
  },
};

// Tool handlers
export async function handlePolicyValidate(
  input: { projectPath?: string; policyIds?: string[] }
): Promise<ValidationReport> {
  const engine = getPolicyEngine();
  const projectPath = input.projectPath || process.cwd();
  
  const context: ValidationContext = {
    projectPath,
  };
  
  return engine.validate(context, input.policyIds);
}

export async function handlePolicyList(
  input: { category?: PolicyCategory }
): Promise<{ policies: Array<{ id: string; name: string; description: string; severity: string; category: string }> }> {
  const engine = getPolicyEngine();
  const policies = engine.listPolicies(input.category);
  
  return {
    policies: policies.map(p => ({
      id: p.id,
      name: p.name,
      description: p.description,
      severity: p.severity,
      category: p.category,
    })),
  };
}

export async function handlePolicyGet(
  input: { id: string }
): Promise<{ policy: { id: string; name: string; description: string; severity: string; category: string } | null }> {
  const engine = getPolicyEngine();
  const policy = engine.getPolicy(input.id);
  
  if (!policy) {
    return { policy: null };
  }
  
  return {
    policy: {
      id: policy.id,
      name: policy.name,
      description: policy.description,
      severity: policy.severity,
      category: policy.category,
    },
  };
}

export async function handlePolicyCheckFile(
  input: { filePath: string; content?: string }
): Promise<{ violations: Array<{ policyId: string; message: string; severity: string }> }> {
  const engine = getPolicyEngine();
  
  // Read file content if not provided
  let content = input.content;
  if (!content) {
    const fs = await import('node:fs/promises');
    try {
      content = await fs.readFile(input.filePath, 'utf-8');
    } catch {
      return { violations: [] };
    }
  }
  
  const context: ValidationContext = {
    filePath: input.filePath,
    content,
  };
  
  // Run EARS validation for requirement files
  const report = await engine.validate(context, ['CONST-004']);
  
  return {
    violations: report.violations.map(v => ({
      policyId: v.policyId,
      message: v.message,
      severity: v.severity,
    })),
  };
}

// Tool collection
export const policyTools: Tool[] = [
  policyValidateTool,
  policyListTool,
  policyGetTool,
  policyCheckFileTool,
];

export function getPolicyTools(): Tool[] {
  return policyTools;
}

export async function handlePolicyTool(
  name: string,
  args: Record<string, unknown>
): Promise<unknown> {
  switch (name) {
    case 'policy_validate':
      return handlePolicyValidate(args as Parameters<typeof handlePolicyValidate>[0]);
    case 'policy_list':
      return handlePolicyList(args as Parameters<typeof handlePolicyList>[0]);
    case 'policy_get':
      return handlePolicyGet(args as Parameters<typeof handlePolicyGet>[0]);
    case 'policy_check_file':
      return handlePolicyCheckFile(args as Parameters<typeof handlePolicyCheckFile>[0]);
    default:
      throw new Error(`Unknown policy tool: ${name}`);
  }
}

// Re-export constitution policies for backward compatibility
export { constitutionPolicies };
