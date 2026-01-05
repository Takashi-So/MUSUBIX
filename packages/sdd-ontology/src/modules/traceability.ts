/**
 * @fileoverview Traceability ontology module
 * @traceability TSK-SDD-ONTO-004
 */

import type { OntologyModule, TraceLink, TraceLinkType } from '../types.js';

/**
 * Traceability ontology module
 */
export const traceModule: OntologyModule = {
  id: 'sdd-trace',
  name: 'SDD Traceability Ontology',
  namespace: 'https://musubix.dev/ontology/sdd/trace#',
  version: '1.0.0',
  description: 'Traceability concepts for requirements tracking',
  dependencies: ['sdd-core', 'sdd-ears', 'sdd-c4'],
  filePath: 'ttl/sdd-trace.ttl',
};

/**
 * Traceability namespace prefixes
 */
export const tracePrefixes = {
  'trace': 'https://musubix.dev/ontology/sdd/trace#',
};

/**
 * Valid trace link types between artifact types
 */
export const validTracePaths: Record<string, TraceLinkType[]> = {
  'requirement->design': ['satisfies', 'derives-from'],
  'design->task': ['implements', 'refines'],
  'task->code': ['implements'],
  'code->test': ['tests'],
  'requirement->test': ['tests'],
};

/**
 * Validate trace link between source and target types
 */
export function validateTraceLink(
  sourceType: string,
  targetType: string,
  linkType: TraceLinkType
): boolean {
  const path = `${sourceType}->${targetType}`;
  const validTypes = validTracePaths[path];
  return validTypes?.includes(linkType) ?? false;
}

/**
 * Create trace link
 */
export function createTraceLink(
  source: string,
  target: string,
  type: TraceLinkType,
  rationale?: string
): TraceLink {
  return {
    source,
    target,
    type,
    rationale,
  };
}

/**
 * Get traceability module metadata
 */
export function getTraceModule(): OntologyModule {
  return { ...traceModule };
}
