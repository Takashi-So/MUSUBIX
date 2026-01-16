// Deep Research Integration - Public API
// Version: 3.4.0
// REQ: REQ-DR-CORE-001 through REQ-DR-NFR-006

// Core Engine
export { ResearchEngine } from './engine/research-engine.js';
export { KnowledgeBase } from './knowledge/knowledge-base.js';

// Providers
export { SearchProviderFactory, createSearchProviderFactory } from './providers/provider-factory.js';
export type { ProviderConfig } from './providers/provider-factory.js';
export { JinaProvider, createJinaProvider } from './providers/jina-provider.js';
export { BraveProvider, createBraveProvider } from './providers/brave-provider.js';
export { DuckDuckGoProvider, createDuckDuckGoProvider } from './providers/duckduckgo-provider.js';

// Reasoning (TSK-DR-010~012)
export { LMReasoning, createLMReasoning } from './reasoning/lm-reasoning.js';
export type { LMProvider, LMGenerationOptions } from './reasoning/lm-reasoning.js';
export { VSCodeLMProvider, createVSCodeLMProvider } from './providers/vscode-lm-provider.js';
export { ExpertIntegration, createExpertIntegration } from './providers/expert-integration.js';

// Security (TSK-DR-013~015)
export { SecretManager } from './security/secret-manager.js';
export { ContentSanitizer } from './security/content-sanitizer.js';
export { SecureLogger } from './security/secure-logger.js';

// Performance (TSK-DR-016~018)
export * from './performance/index.js';

// Utils
export { TokenTracker } from './utils/token-tracker.js';
export { TrajectoryLogger } from './utils/trajectory-logger.js';
export { ReportGenerator } from './reporters/report-generator.js';

// MCP Tools (TSK-DR-020)
export * from './mcp/index.js';

// CLI (TSK-DR-019 - Implemented in @nahisaho/musubix-core)
// See: packages/core/src/cli/commands/deep-research.ts

// Integrations (TSK-DR-021~025 - Not yet implemented)
// export { ExpertIntegration } from './integrations/expert-integration.js';
// export { KnowledgeStoreIntegration } from './integrations/knowledge-store-integration.js';
// export { NeuralSearchIntegration } from './integrations/neural-search-integration.js';
// export { AgentOrchestratorIntegration } from './integrations/orchestrator-integration.js';
// export { WorkflowIntegration } from './integrations/workflow-integration.js';

// Types
export type * from './types/index.js';

// Errors
export * from './types/errors.js';
