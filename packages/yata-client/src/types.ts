/**
 * YATA Client Types
 * 
 * Type definitions for YATA MCP client
 * 
 * @packageDocumentation
 * @module types
 * 
 * @see REQ-INT-102 - MCP Server
 */

/**
 * MCP Transport type
 */
export type MCPTransport = 'stdio' | 'sse';

/**
 * YATA Client configuration
 */
export interface YataClientConfig {
  /** Transport type */
  transport: MCPTransport;
  /** Server command (for stdio) or URL (for SSE) */
  server: string;
  /** Server arguments (for stdio) */
  args?: string[];
  /** Connection timeout in milliseconds */
  timeout: number;
  /** Auto-reconnect on connection loss */
  autoReconnect: boolean;
  /** Maximum reconnect attempts */
  maxReconnectAttempts: number;
  /** Reconnect delay in milliseconds */
  reconnectDelay: number;
}

/**
 * Default YATA client configuration
 */
export const DEFAULT_YATA_CONFIG: YataClientConfig = {
  transport: 'stdio',
  server: 'yata-mcp',
  timeout: 30000,
  autoReconnect: true,
  maxReconnectAttempts: 3,
  reconnectDelay: 1000,
};

/**
 * Connection state
 */
export type ConnectionState = 
  | 'disconnected'
  | 'connecting'
  | 'connected'
  | 'reconnecting'
  | 'error';

/**
 * YATA tool names
 */
export type YataToolName =
  | 'query_knowledge'
  | 'add_knowledge'
  | 'update_knowledge'
  | 'delete_knowledge'
  | 'search_patterns'
  | 'validate_constraints'
  | 'infer_relationships'
  | 'get_reasoning_chain';

/**
 * Tool call request
 */
export interface ToolCallRequest {
  /** Tool name */
  name: YataToolName | string;
  /** Tool arguments */
  arguments: Record<string, unknown>;
}

/**
 * Tool call response
 */
export interface ToolCallResponse<T = unknown> {
  /** Whether call succeeded */
  success: boolean;
  /** Result data */
  result?: T;
  /** Error message if failed */
  error?: string;
  /** Execution time in milliseconds */
  executionTime: number;
}

/**
 * Knowledge node
 */
export interface KnowledgeNode {
  /** Node identifier */
  id: string;
  /** Node type */
  type: string;
  /** Node label */
  label: string;
  /** Node properties */
  properties: Record<string, unknown>;
  /** Creation timestamp */
  createdAt: string;
  /** Update timestamp */
  updatedAt: string;
}

/**
 * Knowledge edge (relationship)
 */
export interface KnowledgeEdge {
  /** Edge identifier */
  id: string;
  /** Source node ID */
  sourceId: string;
  /** Target node ID */
  targetId: string;
  /** Relationship type */
  type: string;
  /** Edge properties */
  properties: Record<string, unknown>;
}

/**
 * Knowledge query result
 */
export interface KnowledgeQueryResult {
  /** Matched nodes */
  nodes: KnowledgeNode[];
  /** Matched edges */
  edges: KnowledgeEdge[];
  /** Total count */
  totalCount: number;
  /** Query execution time */
  executionTime: number;
}

/**
 * Pattern match result
 */
export interface PatternMatchResult {
  /** Pattern name */
  pattern: string;
  /** Match confidence */
  confidence: number;
  /** Matched elements */
  matches: Array<{
    nodeId: string;
    role: string;
  }>;
}

/**
 * Constraint validation result
 */
export interface ConstraintValidationResult {
  /** Whether all constraints are satisfied */
  valid: boolean;
  /** Violations found */
  violations: Array<{
    constraint: string;
    message: string;
    severity: 'error' | 'warning';
    affectedNodes: string[];
  }>;
}

/**
 * Reasoning step
 */
export interface ReasoningStep {
  /** Step number */
  step: number;
  /** Reasoning type */
  type: 'deduction' | 'induction' | 'abduction' | 'analogy';
  /** Premises used */
  premises: string[];
  /** Conclusion drawn */
  conclusion: string;
  /** Confidence score */
  confidence: number;
}

/**
 * Reasoning chain result
 */
export interface ReasoningChainResult {
  /** Query that initiated reasoning */
  query: string;
  /** Reasoning steps */
  steps: ReasoningStep[];
  /** Final conclusion */
  conclusion: string;
  /** Overall confidence */
  confidence: number;
  /** Supporting evidence */
  evidence: string[];
}
