/**
 * Pipeline Module - Synthesis Pipeline Configuration
 *
 * @module @nahisaho/musubix-core/pipeline
 * @see TSK-INT-102
 */

export type {
  PipelineConfig,
  PipelineStage,
  PipelineInput,
  PipelineOutput,
  PipelineExecutionResult,
  PipelineConfigOptions,
  PipelineConfigJSON,
  ParallelGroup,
} from './PipelineConfig.js';

export { createPipelineConfig, DefaultPipelineConfig } from './PipelineConfig.js';
