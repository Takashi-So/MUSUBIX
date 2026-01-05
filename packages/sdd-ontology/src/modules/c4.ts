/**
 * @fileoverview C4 model ontology module
 * @traceability TSK-SDD-ONTO-003
 */

import type { OntologyModule, C4Level, C4Element } from '../types.js';

/**
 * C4 ontology module
 */
export const c4Module: OntologyModule = {
  id: 'sdd-c4',
  name: 'SDD C4 Model Ontology',
  namespace: 'https://musubix.dev/ontology/sdd/c4#',
  version: '1.0.0',
  description: 'C4 model (Context, Container, Component, Code) concepts',
  dependencies: ['sdd-core'],
  filePath: 'ttl/sdd-c4.ttl',
};

/**
 * C4 namespace prefixes
 */
export const c4Prefixes = {
  'c4': 'https://musubix.dev/ontology/sdd/c4#',
};

/**
 * C4 level hierarchy
 */
export const c4LevelHierarchy: C4Level[] = ['context', 'container', 'component', 'code'];

/**
 * Validate C4 element parent-child relationship
 */
export function validateC4Hierarchy(parent: C4Element, child: C4Element): boolean {
  const parentIndex = c4LevelHierarchy.indexOf(parent.level);
  const childIndex = c4LevelHierarchy.indexOf(child.level);
  
  // Child must be exactly one level deeper
  return childIndex === parentIndex + 1;
}

/**
 * Get valid child level for a parent level
 */
export function getChildLevel(parentLevel: C4Level): C4Level | null {
  const parentIndex = c4LevelHierarchy.indexOf(parentLevel);
  if (parentIndex < 0 || parentIndex >= c4LevelHierarchy.length - 1) {
    return null;
  }
  return c4LevelHierarchy[parentIndex + 1];
}

/**
 * Get C4 module metadata
 */
export function getC4Module(): OntologyModule {
  return { ...c4Module };
}
