/**
 * @fileoverview Environment module exports
 * @module @nahisaho/musubix-lean/environment
 */

export {
  LeanEnvironmentDetector,
  detectLeanEnvironment,
  validateLeanVersion,
  ensureLeanInstalled,
  getInstallationInstructions,
  clearEnvironmentCache,
} from './LeanEnvironmentDetector.js';

export {
  LeanProjectInitializer,
  initializeLeanProject,
  isLeanProject,
  type InitializeOptions,
} from './LeanProjectInitializer.js';
