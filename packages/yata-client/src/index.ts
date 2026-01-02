/**
 * @musubix/yata-client - MUSUBIX YATA Client
 * 
 * Knowledge Graph Client Library for YATA MCP Server
 * 
 * Features:
 * - Knowledge graph queries
 * - Symbolic reasoning
 * - Pattern matching
 * - Constraint validation
 * 
 * @packageDocumentation
 * @module @musubix/yata-client
 * 
 * @see REQ-INT-001 - Neuro-Symbolic Integration
 * @see DES-MUSUBIX-001 Section 2.2 - Container Diagram
 */

// Version
export const VERSION = '0.1.0';

// Types
export type {
  MCPTransport,
  YataClientConfig,
  ConnectionState,
  YataToolName,
  ToolCallRequest,
  ToolCallResponse,
  KnowledgeNode,
  KnowledgeEdge,
  KnowledgeQueryResult,
  PatternMatchResult,
  ConstraintValidationResult,
  ReasoningStep,
  ReasoningChainResult,
} from './types.js';

export { DEFAULT_YATA_CONFIG } from './types.js';

// MCP Client
export { YataMCPClient, createYataClient, type YataClientEvents } from './mcp/index.js';

// Knowledge Module
export {
  GraphQueryInterface,
  createGraphQuery,
  OntologyMapper,
  createOntologyMapper,
  type QueryOptions,
  type GraphPath,
  type Subgraph,
  type OntologyNamespace,
  type OntologyConcept,
  type OntologyProperty,
  type OntologyRelation,
  type MappingRule,
  MUSUBIX_NAMESPACES,
  MUSUBIX_CONCEPTS,
  DEFAULT_QUERY_OPTIONS,
} from './knowledge/index.js';

// Reasoning Module
export {
  NeuroSymbolicIntegrator,
  createNeuroSymbolicIntegrator,
  ConfidenceEvaluator,
  createConfidenceEvaluator,
  combineConfidence,
  ContradictionDetector,
  createContradictionDetector,
  type IntegrationMode,
  type IntegratorConfig,
  type NeuralInput,
  type SymbolicConstraints,
  type ValidationRule,
  type ValidationContext,
  type IntegrationResult,
  type ConfidenceSource,
  type ConfidenceScore,
  type CombinedConfidence,
  type CombinationMethod,
  type ContradictionType,
  type Contradiction,
  type Resolution,
  type DetectionReport,
  DEFAULT_INTEGRATOR_CONFIG,
  DEFAULT_EVALUATOR_CONFIG,
  DEFAULT_DETECTOR_CONFIG,
} from './reasoning/index.js';

/**
 * YATA Client Entry Point
 * 
 * This module provides the client interface for YATA knowledge graph.
 * 
 * @example
 * ```typescript
 * import { createYataClient, VERSION } from '@musubix/yata-client';
 * 
 * const client = createYataClient({
 *   server: 'yata-server',
 *   transport: 'stdio',
 * });
 * 
 * await client.connect();
 * console.log(`MUSUBIX YATA Client v${VERSION} connected`);
 * ```
 */
