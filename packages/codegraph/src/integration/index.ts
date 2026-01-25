/**
 * @fileoverview Integration exports for codegraph package
 * @module @nahisaho/musubix-codegraph/integration
 */

// Codemap Bridge
export {
  createCodemapBridge,
  formatCodemapAsMermaid,
} from './codemap-bridge.js';

// Codemap Types
export type {
  PackageInfo,
  DirectoryNode,
  EntryPoint,
  FrameworkInfo,
  ModuleExport,
  ModuleImport,
  ModuleAnalysisResult,
  CodemapDocument,
  Codemap,
  CodemapDiff,
  CodemapBridgeConfig,
  CodemapBridge,
} from './codemap-types.js';

export {
  DEFAULT_CODEMAP_BRIDGE_CONFIG,
} from './codemap-types.js';
