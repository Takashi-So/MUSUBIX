/**
 * Ontology Mapper
 * 
 * Maps between MUSUBIX concepts and YATA ontology
 * 
 * @packageDocumentation
 * @module knowledge/ontology
 * 
 * @see REQ-INT-101 - YATA Integration
 * @see REQ-NS-102 - Knowledge Base
 */

import type { KnowledgeNode, KnowledgeEdge } from '../types.js';

/**
 * Ontology namespace
 */
export interface OntologyNamespace {
  prefix: string;
  uri: string;
}

/**
 * Concept definition in ontology
 */
export interface OntologyConcept {
  /** Concept ID */
  id: string;
  /** Namespace prefix */
  namespace: string;
  /** Local name */
  localName: string;
  /** Human-readable label */
  label: string;
  /** Description */
  description?: string;
  /** Parent concepts */
  parents?: string[];
  /** Properties */
  properties?: Record<string, OntologyProperty>;
}

/**
 * Property definition
 */
export interface OntologyProperty {
  /** Property name */
  name: string;
  /** Property type */
  type: 'string' | 'number' | 'boolean' | 'date' | 'uri' | 'object';
  /** Is required */
  required: boolean;
  /** Is array */
  isArray?: boolean;
  /** Default value */
  default?: unknown;
  /** Constraints */
  constraints?: PropertyConstraint[];
}

/**
 * Property constraint
 */
export interface PropertyConstraint {
  type: 'min' | 'max' | 'pattern' | 'enum' | 'range';
  value: unknown;
}

/**
 * Relation definition
 */
export interface OntologyRelation {
  /** Relation ID */
  id: string;
  /** Source concept ID */
  sourceConceptId: string;
  /** Target concept ID */
  targetConceptId: string;
  /** Relation type */
  type: string;
  /** Cardinality */
  cardinality: 'one-to-one' | 'one-to-many' | 'many-to-one' | 'many-to-many';
  /** Is inverse relation */
  inverse?: string;
}

/**
 * Mapping rule
 */
export interface MappingRule {
  /** Rule ID */
  id: string;
  /** Source concept */
  sourceConcept: string;
  /** Target concept */
  targetConcept: string;
  /** Property mappings */
  propertyMappings: PropertyMapping[];
  /** Transformation function */
  transform?: (node: KnowledgeNode) => KnowledgeNode;
  /** Condition for applying rule */
  condition?: (node: KnowledgeNode) => boolean;
}

/**
 * Property mapping
 */
export interface PropertyMapping {
  /** Source property path */
  source: string;
  /** Target property path */
  target: string;
  /** Value transformer */
  transformer?: (value: unknown) => unknown;
}

/**
 * MUSUBIX domain ontology namespaces
 */
export const MUSUBIX_NAMESPACES: Record<string, OntologyNamespace> = {
  musubix: {
    prefix: 'musubix',
    uri: 'https://musubix.dev/ontology#',
  },
  ears: {
    prefix: 'ears',
    uri: 'https://musubix.dev/ontology/ears#',
  },
  c4: {
    prefix: 'c4',
    uri: 'https://musubix.dev/ontology/c4#',
  },
  task: {
    prefix: 'task',
    uri: 'https://musubix.dev/ontology/task#',
  },
};

/**
 * Built-in MUSUBIX concepts
 */
export const MUSUBIX_CONCEPTS: Record<string, OntologyConcept> = {
  // EARS Requirements
  'ears:Requirement': {
    id: 'ears:Requirement',
    namespace: 'ears',
    localName: 'Requirement',
    label: 'Requirement',
    description: 'EARS format requirement',
    properties: {
      id: { name: 'id', type: 'string', required: true },
      pattern: { name: 'pattern', type: 'string', required: true },
      text: { name: 'text', type: 'string', required: true },
      priority: { name: 'priority', type: 'string', required: false },
      rationale: { name: 'rationale', type: 'string', required: false },
    },
  },
  // C4 Architecture
  'c4:System': {
    id: 'c4:System',
    namespace: 'c4',
    localName: 'System',
    label: 'System',
    description: 'C4 System context',
    parents: ['c4:Container'],
  },
  'c4:Container': {
    id: 'c4:Container',
    namespace: 'c4',
    localName: 'Container',
    label: 'Container',
    description: 'C4 Container',
    parents: ['c4:Component'],
  },
  'c4:Component': {
    id: 'c4:Component',
    namespace: 'c4',
    localName: 'Component',
    label: 'Component',
    description: 'C4 Component',
  },
  // Task
  'task:Task': {
    id: 'task:Task',
    namespace: 'task',
    localName: 'Task',
    label: 'Task',
    description: 'Implementation task',
    properties: {
      id: { name: 'id', type: 'string', required: true },
      title: { name: 'title', type: 'string', required: true },
      status: { name: 'status', type: 'string', required: true },
      estimatedHours: { name: 'estimatedHours', type: 'number', required: false },
    },
  },
};

/**
 * Ontology Mapper
 * 
 * Maps between different ontology systems
 */
export class OntologyMapper {
  private namespaces: Map<string, OntologyNamespace> = new Map();
  private concepts: Map<string, OntologyConcept> = new Map();
  private relations: Map<string, OntologyRelation> = new Map();
  private mappingRules: Map<string, MappingRule> = new Map();

  constructor() {
    // Initialize with MUSUBIX defaults
    this.loadNamespaces(MUSUBIX_NAMESPACES);
    this.loadConcepts(MUSUBIX_CONCEPTS);
  }

  /**
   * Load namespaces
   */
  loadNamespaces(namespaces: Record<string, OntologyNamespace>): void {
    for (const [key, ns] of Object.entries(namespaces)) {
      this.namespaces.set(key, ns);
    }
  }

  /**
   * Load concepts
   */
  loadConcepts(concepts: Record<string, OntologyConcept>): void {
    for (const [key, concept] of Object.entries(concepts)) {
      this.concepts.set(key, concept);
    }
  }

  /**
   * Add mapping rule
   */
  addMappingRule(rule: MappingRule): void {
    this.mappingRules.set(rule.id, rule);
  }

  /**
   * Get concept by ID
   */
  getConcept(id: string): OntologyConcept | undefined {
    return this.concepts.get(id);
  }

  /**
   * Get namespace by prefix
   */
  getNamespace(prefix: string): OntologyNamespace | undefined {
    return this.namespaces.get(prefix);
  }

  /**
   * Resolve full URI
   */
  resolveUri(prefixedName: string): string {
    const [prefix, localName] = prefixedName.split(':');
    const ns = this.namespaces.get(prefix);
    if (!ns) {
      return prefixedName;
    }
    return `${ns.uri}${localName}`;
  }

  /**
   * Compress URI to prefixed name
   */
  compressUri(uri: string): string {
    for (const [prefix, ns] of this.namespaces) {
      if (uri.startsWith(ns.uri)) {
        return `${prefix}:${uri.slice(ns.uri.length)}`;
      }
    }
    return uri;
  }

  /**
   * Map node to target concept
   */
  mapNode(
    node: KnowledgeNode,
    targetConceptId: string
  ): KnowledgeNode {
    const sourceType = node.type;
    const ruleKey = `${sourceType}->${targetConceptId}`;
    const rule = this.mappingRules.get(ruleKey);

    if (rule && rule.transform) {
      return rule.transform(node);
    }

    // Default mapping: just change type
    return {
      ...node,
      type: targetConceptId,
    };
  }

  /**
   * Map edge type
   */
  mapEdgeType(
    edge: KnowledgeEdge,
    _sourceMapping: string,
    _targetMapping: string
  ): KnowledgeEdge {
    const relation = this.relations.get(edge.type);
    if (!relation) {
      return edge;
    }

    return {
      ...edge,
      type: relation.type,
    };
  }

  /**
   * Validate node against concept
   */
  validateNode(node: KnowledgeNode, conceptId: string): ValidationResult {
    const concept = this.concepts.get(conceptId);
    if (!concept) {
      return {
        valid: false,
        errors: [`Unknown concept: ${conceptId}`],
      };
    }

    const errors: string[] = [];

    // Validate required properties
    if (concept.properties) {
      for (const [name, prop] of Object.entries(concept.properties)) {
        if (prop.required && !(name in node.properties)) {
          errors.push(`Missing required property: ${name}`);
        }
      }
    }

    return {
      valid: errors.length === 0,
      errors,
    };
  }

  /**
   * Get concept hierarchy
   */
  getConceptHierarchy(conceptId: string): string[] {
    const hierarchy: string[] = [conceptId];
    const concept = this.concepts.get(conceptId);
    
    if (concept?.parents) {
      for (const parentId of concept.parents) {
        hierarchy.push(...this.getConceptHierarchy(parentId));
      }
    }

    return hierarchy;
  }

  /**
   * Check if concept is subtype of another
   */
  isSubtypeOf(conceptId: string, parentConceptId: string): boolean {
    if (conceptId === parentConceptId) {
      return true;
    }

    const concept = this.concepts.get(conceptId);
    if (!concept?.parents) {
      return false;
    }

    return concept.parents.some(
      (parentId) => this.isSubtypeOf(parentId, parentConceptId)
    );
  }

  /**
   * Get all concepts of type
   */
  getConceptsOfType(typeId: string): OntologyConcept[] {
    const results: OntologyConcept[] = [];
    for (const concept of this.concepts.values()) {
      if (this.isSubtypeOf(concept.id, typeId)) {
        results.push(concept);
      }
    }
    return results;
  }
}

/**
 * Validation result
 */
export interface ValidationResult {
  valid: boolean;
  errors: string[];
  warnings?: string[];
}

/**
 * Create ontology mapper instance
 */
export function createOntologyMapper(): OntologyMapper {
  return new OntologyMapper();
}
