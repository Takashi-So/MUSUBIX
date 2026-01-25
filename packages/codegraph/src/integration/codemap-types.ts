/**
 * @fileoverview Codemap Bridge Types for Agent Skills Integration
 * @traceability REQ-CM-001, REQ-CM-002, REQ-CM-003, REQ-CM-004
 */

import type { Language } from '../types.js';

// ============================================================================
// Package Structure Types
// ============================================================================

/**
 * Workspace/package information
 */
export interface PackageInfo {
  /** Package name */
  name: string;
  /** Package version */
  version?: string;
  /** Package path relative to workspace root */
  path: string;
  /** Package description */
  description?: string;
  /** Main entry point */
  main?: string;
  /** Export paths */
  exports?: Record<string, string>;
  /** Internal dependencies */
  dependencies: string[];
  /** Dev dependencies */
  devDependencies?: string[];
}

/**
 * Directory structure node
 */
export interface DirectoryNode {
  /** Directory/file name */
  name: string;
  /** Full path */
  path: string;
  /** Is directory */
  isDirectory: boolean;
  /** Children (if directory) */
  children?: DirectoryNode[];
  /** File language (if file) */
  language?: Language;
  /** Entity count (if file) */
  entityCount?: number;
}

/**
 * Entry point information
 */
export interface EntryPoint {
  /** Entry point type */
  type: 'cli' | 'library' | 'api' | 'worker' | 'test' | 'config';
  /** File path */
  path: string;
  /** Export name (if applicable) */
  exportName?: string;
  /** Description */
  description?: string;
}

/**
 * Framework detection result
 */
export interface FrameworkInfo {
  /** Framework name */
  name: string;
  /** Framework version */
  version?: string;
  /** Framework type */
  type: 'frontend' | 'backend' | 'fullstack' | 'build' | 'test' | 'other';
  /** Indicator files */
  indicators: string[];
}

// ============================================================================
// Module Analysis Types
// ============================================================================

/**
 * Module export information
 */
export interface ModuleExport {
  /** Export name */
  name: string;
  /** Export type */
  type: 'function' | 'class' | 'interface' | 'type' | 'const' | 'enum' | 'namespace' | 'default';
  /** Is re-export */
  isReExport: boolean;
  /** Source file */
  sourceFile: string;
  /** Line number */
  line?: number;
}

/**
 * Module import information
 */
export interface ModuleImport {
  /** Import source */
  source: string;
  /** Is external (node_modules) */
  isExternal: boolean;
  /** Imported items */
  items: string[];
  /** Is type-only import */
  isTypeOnly?: boolean;
}

/**
 * Complete module analysis
 */
export interface ModuleAnalysisResult {
  /** Module path */
  path: string;
  /** Module name */
  name: string;
  /** Exports */
  exports: ModuleExport[];
  /** Imports */
  imports: ModuleImport[];
  /** Entity count by type */
  entityCounts: Record<string, number>;
  /** Lines of code */
  linesOfCode?: number;
  /** Complexity score */
  complexity?: number;
}

// ============================================================================
// Codemap Generation Types
// ============================================================================

/**
 * Codemap document structure
 */
export interface CodemapDocument {
  /** Document type */
  type: 'index' | 'frontend' | 'backend' | 'packages' | 'database' | 'integrations' | 'workers';
  /** Document title */
  title: string;
  /** Document content (Markdown) */
  content: string;
  /** Related packages */
  packages?: string[];
  /** Last updated */
  updatedAt: string;
}

/**
 * Complete codemap
 */
export interface Codemap {
  /** Project name */
  projectName: string;
  /** Project version */
  projectVersion?: string;
  /** Generation timestamp */
  generatedAt: string;
  /** Documents */
  documents: CodemapDocument[];
  /** Package structure */
  packages: PackageInfo[];
  /** Entry points */
  entryPoints: EntryPoint[];
  /** Detected frameworks */
  frameworks: FrameworkInfo[];
  /** Directory structure (top-level) */
  structure: DirectoryNode;
}

/**
 * Codemap diff result
 */
export interface CodemapDiff {
  /** Previous codemap hash */
  previousHash: string;
  /** Current codemap hash */
  currentHash: string;
  /** Diff percentage */
  diffPercentage: number;
  /** Added packages */
  addedPackages: string[];
  /** Removed packages */
  removedPackages: string[];
  /** Modified packages */
  modifiedPackages: string[];
  /** Added entry points */
  addedEntryPoints: string[];
  /** Removed entry points */
  removedEntryPoints: string[];
  /** Major changes description */
  majorChanges: string[];
}

// ============================================================================
// Bridge Configuration
// ============================================================================

/**
 * Codemap bridge configuration
 */
export interface CodemapBridgeConfig {
  /** Output directory */
  outputDir: string;
  /** Include tests */
  includeTests: boolean;
  /** Include node_modules */
  includeNodeModules: boolean;
  /** Max directory depth */
  maxDepth: number;
  /** Diff threshold for user approval */
  diffThreshold: number;
  /** Report output path */
  reportOutputPath: string;
}

/**
 * Default codemap bridge configuration
 */
export const DEFAULT_CODEMAP_BRIDGE_CONFIG: CodemapBridgeConfig = {
  outputDir: 'docs/CODEMAPS',
  includeTests: false,
  includeNodeModules: false,
  maxDepth: 5,
  diffThreshold: 30,
  reportOutputPath: '.reports/codemap-diff.txt',
};

// ============================================================================
// Bridge Interface
// ============================================================================

/**
 * Codemap skill bridge interface
 */
export interface CodemapBridge {
  /**
   * Analyze repository structure
   * @param rootPath Root path to analyze
   * @returns Package and structure information
   */
  analyzeStructure(rootPath: string): Promise<{
    packages: PackageInfo[];
    structure: DirectoryNode;
    entryPoints: EntryPoint[];
    frameworks: FrameworkInfo[];
  }>;

  /**
   * Analyze a specific module
   * @param modulePath Path to the module
   * @returns Module analysis result
   */
  analyzeModule(modulePath: string): Promise<ModuleAnalysisResult>;

  /**
   * Generate codemap
   * @param rootPath Root path
   * @returns Generated codemap
   */
  generateCodemap(rootPath: string): Promise<Codemap>;

  /**
   * Compare codemaps
   * @param previous Previous codemap
   * @param current Current codemap
   * @returns Diff result
   */
  compareCodemaps(previous: Codemap, current: Codemap): CodemapDiff;

  /**
   * Write codemap to files
   * @param codemap Codemap to write
   * @param outputDir Output directory
   */
  writeCodemap(codemap: Codemap, outputDir?: string): Promise<void>;

  /**
   * Format codemap as Markdown
   * @param codemap Codemap to format
   * @returns Markdown string
   */
  formatAsMarkdown(codemap: Codemap): string;

  /**
   * Format diff as report
   * @param diff Diff result
   * @returns Report string
   */
  formatDiffReport(diff: CodemapDiff): string;

  /**
   * Get configuration
   */
  getConfig(): CodemapBridgeConfig;

  /**
   * Update configuration
   * @param config Partial config to update
   */
  updateConfig(config: Partial<CodemapBridgeConfig>): void;
}
