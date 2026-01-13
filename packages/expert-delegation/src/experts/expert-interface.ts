/**
 * @nahisaho/musubix-expert-delegation
 * Expert Interface
 *
 * DES-EXP-001
 * Traces to: REQ-EXP-001
 */

// Re-export from types
export type {
  Expert,
  ExpertType,
  ExpertCapability,
  TriggerPattern,
  ExecutionMode,
} from '../types/index.js';

/**
 * エキスパート生成ヘルパー
 */
export function createExpert(config: {
  type: import('../types/index.js').ExpertType;
  name: string;
  description: string;
  systemPrompt: string;
  triggers: import('../types/index.js').TriggerPattern[];
  ontologyClass: string;
  capabilities: import('../types/index.js').ExpertCapability[];
}): import('../types/index.js').Expert {
  return {
    type: config.type,
    name: config.name,
    description: config.description,
    systemPrompt: config.systemPrompt,
    triggers: config.triggers,
    ontologyClass: config.ontologyClass,
    capabilities: config.capabilities,
  };
}
