/**
 * Synthesis module - E2E synthesis pipeline integration
 * @module @nahisaho/musubix-core/synthesis
 */

export {
  createSynthesisOrchestrator,
  DefaultSynthesisOrchestrator,
} from './SynthesisOrchestrator.js';

export type {
  SynthesisOrchestrator,
  OrchestratorConfig,
  PipelinePreset,
  SynthesisRequest,
  SynthesisResponse,
  SynthesisTiming,
  SynthesisStatus,
  OrchestratorStatistics,
  IOExample,
  LibraryPattern,
} from './SynthesisOrchestrator.js';
