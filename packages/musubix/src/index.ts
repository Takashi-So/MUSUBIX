/**
 * MUSUBIX - Neuro-Symbolic AI Integration System
 *
 * This is the main entry point that re-exports all MUSUBIX packages.
 * Install with: npm install musubix
 *
 * @packageDocumentation
 */

// Core functionality
export * from '@nahisaho/musubix-core';

// Security analysis
export * as security from '@nahisaho/musubix-security';

// Formal verification
export * as formalVerify from '@nahisaho/musubix-formal-verify';

// YATA Knowledge Graph
export * as yataClient from '@nahisaho/musubix-yata-client';
export * as yataLocal from '@nahisaho/yata-local';
export * as yataGlobal from '@nahisaho/yata-global';
export * as yataScale from '@nahisaho/yata-scale';

// Pattern and Ontology MCP
export * as patternMcp from '@nahisaho/musubix-pattern-mcp';
export * as ontologyMcp from '@nahisaho/musubix-ontology-mcp';

// Wake-Sleep learning
export * as wakeSleep from '@nahisaho/musubix-wake-sleep';

// SDD Ontology
export * as sddOntology from '@nahisaho/musubix-sdd-ontology';

// v2.0.0 packages
export * as dfg from '@nahisaho/musubix-dfg';
export * as lean from '@nahisaho/musubix-lean';

// v2.2.0 Advanced Learning packages
export * as libraryLearner from '@nahisaho/musubix-library-learner';
export * as neuralSearch from '@nahisaho/musubix-neural-search';
export * as synthesis from '@nahisaho/musubix-synthesis';
