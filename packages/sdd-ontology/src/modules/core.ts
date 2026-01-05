/**
 * @fileoverview Core ontology module metadata
 * @traceability TSK-SDD-ONTO-001
 */

import type { OntologyModule } from '../types.js';

/**
 * Core SDD ontology module
 */
export const coreModule: OntologyModule = {
  id: 'sdd-core',
  name: 'SDD Core Ontology',
  namespace: 'https://musubix.dev/ontology/sdd#',
  version: '1.0.0',
  description: 'Core concepts for SDD methodology',
  dependencies: [],
  filePath: 'sdd-core.ttl',
};

/**
 * Core namespace prefixes
 */
export const corePrefixes = {
  'sdd': 'https://musubix.dev/ontology/sdd/core#',
  'owl': 'http://www.w3.org/2002/07/owl#',
  'rdf': 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
  'rdfs': 'http://www.w3.org/2000/01/rdf-schema#',
  'xsd': 'http://www.w3.org/2001/XMLSchema#',
};

/**
 * Get core module metadata
 */
export function getCoreModule(): OntologyModule {
  return { ...coreModule };
}
