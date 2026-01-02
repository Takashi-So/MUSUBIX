/**
 * Knowledge Module
 * 
 * Knowledge graph operations and queries
 * 
 * @packageDocumentation
 * @module knowledge
 */

export {
  GraphQueryInterface,
  createGraphQuery,
  type QueryOptions,
  type GraphPath,
  type Subgraph,
  DEFAULT_QUERY_OPTIONS,
} from './query.js';

export {
  OntologyMapper,
  createOntologyMapper,
  type OntologyNamespace,
  type OntologyConcept,
  type OntologyProperty,
  type PropertyConstraint,
  type OntologyRelation,
  type MappingRule,
  type PropertyMapping,
  type ValidationResult,
  MUSUBIX_NAMESPACES,
  MUSUBIX_CONCEPTS,
} from './ontology.js';
