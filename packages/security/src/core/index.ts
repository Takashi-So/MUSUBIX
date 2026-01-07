/**
 * @fileoverview Core orchestration components
 * @module @nahisaho/musubix-security/core
 * @trace DES-SEC2-ORCH-001, DES-SEC2-ORCH-002, DES-SEC2-ORCH-003
 */

// Pipeline Manager
export {
  PipelineManager,
  createPipelineManager,
  createStandardPipeline,
} from './pipeline-manager.js';

// Result Aggregator
export {
  ResultAggregator,
  createResultAggregator,
  mergeSimilarByLocation,
} from './result-aggregator.js';
