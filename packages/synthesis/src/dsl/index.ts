/**
 * DSL Module Exports
 * @module @nahisaho/musubix-synthesis/dsl
 */

export { DSL } from './DSL.js';
export { DSLBuilder } from './DSLBuilder.js';
export { TypeSystem } from './TypeSystem.js';

// DSL Extension (v2.2.0 NEW!)
export { createDSLExtender } from './DSLExtender.js';
export type {
  DSLExtender,
  DSLExtenderConfig,
  DSLGap,
  OperatorSuggestion,
  OperatorValidationResult,
  Example,
} from './DSLExtender.js';
