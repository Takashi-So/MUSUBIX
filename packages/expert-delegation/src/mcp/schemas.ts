/**
 * @nahisaho/musubix-expert-delegation
 * MCP Tool Schemas
 *
 * DES-MCP-001
 * Traces to: REQ-INT-001
 */

// Types are used in documentation/validation, not in TypeScript type checking
// ExpertType and ExecutionMode values are referenced in enum definitions below

/**
 * MCP Tool Schema定義
 */
export interface MCPToolSchema {
  name: string;
  description: string;
  inputSchema: {
    type: 'object';
    properties: Record<string, {
      type: string;
      description: string;
      enum?: string[];
      items?: { type: string };
      default?: unknown;
    }>;
    required: string[];
  };
}

/**
 * expert_delegate: 汎用委任ツール
 */
export const expertDelegateSchema: MCPToolSchema = {
  name: 'expert_delegate',
  description:
    'Delegate a task to a specialized AI expert. The system automatically selects the appropriate expert based on the message content, or you can specify one explicitly.',
  inputSchema: {
    type: 'object',
    properties: {
      message: {
        type: 'string',
        description: 'The task or question to delegate to the expert',
      },
      expert: {
        type: 'string',
        description: 'Optional: explicitly specify the expert type',
        enum: [
          'architect',
          'security-analyst',
          'code-reviewer',
          'plan-reviewer',
          'ears-analyst',
          'formal-verifier',
          'ontology-reasoner',
        ],
      },
      mode: {
        type: 'string',
        description: 'Execution mode: advisory (analysis only) or implementation (code generation)',
        enum: ['advisory', 'implementation'],
        default: 'advisory',
      },
      context: {
        type: 'object',
        description: 'Additional context for the delegation',
      },
    },
    required: ['message'],
  },
};

/**
 * expert_architect: アーキテクチャ委任
 */
export const expertArchitectSchema: MCPToolSchema = {
  name: 'expert_architect',
  description:
    'Delegate architecture-related tasks to the Architect expert. Use for system design, component structure, design patterns, and architectural decisions.',
  inputSchema: {
    type: 'object',
    properties: {
      message: {
        type: 'string',
        description: 'The architecture question or design task',
      },
      mode: {
        type: 'string',
        description: 'Execution mode',
        enum: ['advisory', 'implementation'],
        default: 'advisory',
      },
      constraints: {
        type: 'array',
        description: 'Architectural constraints to consider',
        items: { type: 'string' },
      },
    },
    required: ['message'],
  },
};

/**
 * expert_security: セキュリティ分析委任
 */
export const expertSecuritySchema: MCPToolSchema = {
  name: 'expert_security',
  description:
    'Delegate security analysis to the Security Analyst expert. Use for vulnerability detection, security code review, and threat modeling.',
  inputSchema: {
    type: 'object',
    properties: {
      code: {
        type: 'string',
        description: 'Code to analyze for security vulnerabilities',
      },
      context: {
        type: 'string',
        description: 'Additional context about the code or system',
      },
      threatModel: {
        type: 'boolean',
        description: 'Whether to include threat modeling analysis',
        default: false,
      },
    },
    required: ['code'],
  },
};

/**
 * expert_review: コードレビュー委任
 */
export const expertReviewSchema: MCPToolSchema = {
  name: 'expert_review',
  description:
    'Delegate code review to the Code Reviewer expert. Use for code quality analysis, best practices review, and refactoring suggestions.',
  inputSchema: {
    type: 'object',
    properties: {
      code: {
        type: 'string',
        description: 'Code to review',
      },
      language: {
        type: 'string',
        description: 'Programming language of the code',
      },
      focus: {
        type: 'array',
        description: 'Areas to focus on: performance, readability, patterns, bugs',
        items: { type: 'string' },
      },
    },
    required: ['code'],
  },
};

/**
 * expert_plan: 計画レビュー委任
 */
export const expertPlanSchema: MCPToolSchema = {
  name: 'expert_plan',
  description:
    'Delegate plan review to the Plan Reviewer expert. Use for validating designs, requirements, and implementation plans against MUSUBIX constitution.',
  inputSchema: {
    type: 'object',
    properties: {
      plan: {
        type: 'string',
        description: 'The plan or design document to review',
      },
      checkConstitution: {
        type: 'boolean',
        description: 'Whether to check against MUSUBIX 10 constitutional articles',
        default: true,
      },
      validateTraceability: {
        type: 'boolean',
        description: 'Whether to validate traceability links',
        default: true,
      },
    },
    required: ['plan'],
  },
};

/**
 * expert_ears: EARS分析委任
 */
export const expertEarsSchema: MCPToolSchema = {
  name: 'expert_ears',
  description:
    'Delegate requirements analysis to the EARS Analyst expert. Use for converting natural language requirements to EARS format.',
  inputSchema: {
    type: 'object',
    properties: {
      requirements: {
        type: 'string',
        description: 'Natural language requirements to analyze',
      },
      suggestedPattern: {
        type: 'string',
        description: 'Suggested EARS pattern',
        enum: ['ubiquitous', 'event-driven', 'state-driven', 'unwanted', 'optional'],
      },
      generateIds: {
        type: 'boolean',
        description: 'Whether to generate requirement IDs',
        default: true,
      },
    },
    required: ['requirements'],
  },
};

/**
 * expert_formal: 形式検証委任
 */
export const expertFormalSchema: MCPToolSchema = {
  name: 'expert_formal',
  description:
    'Delegate formal verification to the Formal Verifier expert. Use for generating Hoare logic conditions, Z3/SMT queries, and Lean 4 theorems.',
  inputSchema: {
    type: 'object',
    properties: {
      code: {
        type: 'string',
        description: 'Code to formally verify',
      },
      specification: {
        type: 'string',
        description: 'Formal specification or EARS requirement',
      },
      outputFormat: {
        type: 'string',
        description: 'Desired output format',
        enum: ['z3', 'lean4', 'hoare'],
        default: 'z3',
      },
    },
    required: ['code'],
  },
};

/**
 * expert_ontology: オントロジー推論委任
 */
export const expertOntologySchema: MCPToolSchema = {
  name: 'expert_ontology',
  description:
    'Delegate ontology reasoning to the Ontology Reasoner expert. Use for knowledge graph queries, inference, and consistency checking.',
  inputSchema: {
    type: 'object',
    properties: {
      query: {
        type: 'string',
        description: 'The reasoning query or question',
      },
      triples: {
        type: 'array',
        description: 'Context knowledge as triples',
        items: { type: 'object' },
      },
      checkConsistency: {
        type: 'boolean',
        description: 'Whether to check knowledge graph consistency',
        default: false,
      },
    },
    required: ['query'],
  },
};

/**
 * trigger_detect: トリガー検出
 */
export const triggerDetectSchema: MCPToolSchema = {
  name: 'trigger_detect',
  description:
    'Detect which expert should handle a given message. Returns the matched expert and confidence score.',
  inputSchema: {
    type: 'object',
    properties: {
      message: {
        type: 'string',
        description: 'Message to analyze for expert routing',
      },
    },
    required: ['message'],
  },
};

/**
 * delegation_retry: リトライ実行
 */
export const delegationRetrySchema: MCPToolSchema = {
  name: 'delegation_retry',
  description:
    'Retry a failed delegation with optional feedback. Implements exponential backoff.',
  inputSchema: {
    type: 'object',
    properties: {
      taskId: {
        type: 'string',
        description: 'ID of the task to retry',
      },
      feedback: {
        type: 'string',
        description: 'Feedback about why the previous attempt failed',
      },
    },
    required: ['taskId'],
  },
};

/**
 * provider_select: プロバイダー選択
 */
export const providerSelectSchema: MCPToolSchema = {
  name: 'provider_select',
  description:
    'Select and configure the LLM provider for expert delegation. Currently supports VS Code Language Model API.',
  inputSchema: {
    type: 'object',
    properties: {
      criteria: {
        type: 'object',
        description: 'Selection criteria (family, version, capabilities)',
      },
      temperature: {
        type: 'number',
        description: 'Temperature setting for LLM (0.0-1.0)',
        default: 0.3,
      },
    },
    required: [],
  },
};

/**
 * すべてのスキーマをエクスポート
 */
export const allSchemas: MCPToolSchema[] = [
  expertDelegateSchema,
  expertArchitectSchema,
  expertSecuritySchema,
  expertReviewSchema,
  expertPlanSchema,
  expertEarsSchema,
  expertFormalSchema,
  expertOntologySchema,
  triggerDetectSchema,
  delegationRetrySchema,
  providerSelectSchema,
];

/**
 * スキーマを名前で取得
 */
export function getSchema(name: string): MCPToolSchema | undefined {
  return allSchemas.find((s) => s.name === name);
}
