/**
 * @musubix/core - MUSUBIX Core Library
 * 
 * Neuro-Symbolic AI Integration Engine
 * 
 * @packageDocumentation
 * @module @musubix/core
 * 
 * @see REQ-ARC-001 - Library-First Architecture
 * @see DES-MUSUBIX-001 Section 3.1 - Project Structure
 */

// Version
export { VERSION } from './version.js';

// Export types
export * from './types/index.js';

// Export utilities
export * from './utils/index.js';

// Export CLI
export * from './cli/index.js';

// Export validators
export * from './validators/index.js';

// Export traceability
export * from './traceability/index.js';

// Export design
export * from './design/index.js';

// Export code generation
export * from './codegen/index.js';

// Export explanation
export * from './explanation/index.js';

// Export error recovery
export * from './error/index.js';

// Export learning system
export * from './learning/index.js';

// Re-export modules (will be implemented in subsequent tasks)
// export * from './integrator/index.js';
// export * from './requirements/index.js';
// export * from './testing/index.js';

/**
 * Core Library Entry Point
 * 
 * This module exports all public APIs of the MUSUBIX core library.
 * 
 * @example
 * ```typescript
 * import { VERSION } from '@musubix/core';
 * console.log(`MUSUBIX Core v${VERSION}`);
 * ```
 */
