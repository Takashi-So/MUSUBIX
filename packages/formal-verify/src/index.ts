/**
 * @nahisaho/musubix-formal-verify
 * 
 * MUSUBIX v1.7.5 Formal Verification Edition
 * 形式検証ツールパッケージ
 * 
 * @packageDocumentation
 */

// Z3 Integration
export { Z3Adapter } from './z3/Z3Adapter.js';
export { Z3WasmClient } from './z3/Z3WasmClient.js';
export { Z3ProcessFallback } from './z3/Z3ProcessFallback.js';
export type { Z3Client, Z3Result, Z3Options } from './z3/types.js';

// Verifiers
export { PreconditionVerifier } from './verifiers/PreconditionVerifier.js';
export { PostconditionVerifier } from './verifiers/PostconditionVerifier.js';
export type { 
  VerificationResult, 
  VerificationOptions,
  Condition,
  VariableDeclaration 
} from './verifiers/types.js';

// Converters
export { EarsToSmtConverter } from './converters/EarsToSmtConverter.js';
export type { 
  EarsPattern, 
  SmtFormula, 
  ConversionResult 
} from './converters/types.js';

// Traceability
export { TraceabilityDB } from './traceability/TraceabilityDB.js';
export { ImpactAnalyzer } from './traceability/ImpactAnalyzer.js';
export type { 
  TraceLink, 
  TraceLinkType, 
  ImpactResult,
  TraceNode 
} from './traceability/types.js';

// MCP Tools
export {
  verifyPreconditionTool,
  verifyPostconditionTool,
  earsToSmtTool,
  traceAddLinkTool,
  traceQueryTool,
  traceImpactTool,
  formalVerifyTools,
  getFormalVerifyTools,
  handleFormalVerifyTool,
} from './tools/index.js';
