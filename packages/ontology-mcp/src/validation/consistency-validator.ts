/**
 * @fileoverview Consistency validator for ontology stores
 * @traceability REQ-ONTO-001-F003, DES-ONTO-001
 */

import type {
  Triple,
  ConsistencyResult,
  ConsistencyViolation,
  ConsistencySuggestion,
  TripleValidationResult,
} from '../types.js';

/**
 * OWL/RDF namespace URIs
 */
const RDF = {
  type: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
};

const OWL = {
  disjointWith: 'http://www.w3.org/2002/07/owl#disjointWith',
  FunctionalProperty: 'http://www.w3.org/2002/07/owl#FunctionalProperty',
  InverseFunctionalProperty: 'http://www.w3.org/2002/07/owl#InverseFunctionalProperty',
  AsymmetricProperty: 'http://www.w3.org/2002/07/owl#AsymmetricProperty',
  IrreflexiveProperty: 'http://www.w3.org/2002/07/owl#IrreflexiveProperty',
};

/**
 * Interface for triple store abstraction
 */
export interface TripleStore {
  getTriples(pattern?: Partial<Triple>): Triple[];
}

/**
 * Consistency validator configuration
 */
export interface ConsistencyValidatorConfig {
  /** Enable disjoint class checking */
  checkDisjointClasses: boolean;
  /** Enable functional property checking */
  checkFunctionalProperties: boolean;
  /** Enable inverse functional property checking */
  checkInverseFunctionalProperties: boolean;
  /** Enable asymmetric property checking */
  checkAsymmetricProperties: boolean;
  /** Enable irreflexive property checking */
  checkIrreflexiveProperties: boolean;
  /** Enable duplicate detection */
  checkDuplicates: boolean;
  /** Enable circular dependency detection */
  checkCircularDependencies: boolean;
}

const DEFAULT_CONFIG: ConsistencyValidatorConfig = {
  checkDisjointClasses: true,
  checkFunctionalProperties: true,
  checkInverseFunctionalProperties: true,
  checkAsymmetricProperties: true,
  checkIrreflexiveProperties: true,
  checkDuplicates: true,
  checkCircularDependencies: true,
};

/**
 * Consistency validator for RDF/OWL ontologies
 * 
 * @description
 * Validates ontology consistency according to OWL semantics:
 * - Disjoint class membership violations
 * - Functional property constraints
 * - Inverse functional property constraints
 * - Asymmetric property violations
 * - Irreflexive property violations
 * - Duplicate triple detection
 * - Circular dependency detection
 * 
 * @traceability REQ-ONTO-001-F003
 */
export class ConsistencyValidator {
  private config: ConsistencyValidatorConfig;

  constructor(config: Partial<ConsistencyValidatorConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  /**
   * Validate entire store for consistency
   */
  validate(store: TripleStore): ConsistencyResult {
    const violations: ConsistencyViolation[] = [];
    const triples = store.getTriples();

    if (this.config.checkDisjointClasses) {
      violations.push(...this.checkDisjointClasses(triples));
    }

    if (this.config.checkFunctionalProperties) {
      violations.push(...this.checkFunctionalProperties(triples));
    }

    if (this.config.checkInverseFunctionalProperties) {
      violations.push(...this.checkInverseFunctionalProperties(triples));
    }

    if (this.config.checkAsymmetricProperties) {
      violations.push(...this.checkAsymmetricProperties(triples));
    }

    if (this.config.checkIrreflexiveProperties) {
      violations.push(...this.checkIrreflexiveProperties(triples));
    }

    if (this.config.checkDuplicates) {
      violations.push(...this.checkDuplicates(triples));
    }

    if (this.config.checkCircularDependencies) {
      violations.push(...this.checkCircularDependencies(triples));
    }

    const suggestions = this.generateSuggestions(violations);
    const hasErrors = violations.some(v => v.severity === 'error');

    return {
      consistent: !hasErrors,
      violations,
      suggestions,
    };
  }

  /**
   * Validate a single triple before adding
   */
  validateTriple(triple: Triple, existingTriples: Triple[]): TripleValidationResult {
    const errors: string[] = [];
    const warnings: string[] = [];

    // Check for exact duplicate
    const duplicate = existingTriples.find(
      t => t.subject === triple.subject &&
           t.predicate === triple.predicate &&
           t.object === triple.object
    );

    if (duplicate) {
      warnings.push(`Duplicate triple already exists`);
      return { valid: true, errors, warnings, duplicateOf: duplicate };
    }

    // Check URI format
    if (!this.isValidUri(triple.subject)) {
      errors.push(`Invalid subject URI: ${triple.subject}`);
    }
    if (!this.isValidUri(triple.predicate)) {
      errors.push(`Invalid predicate URI: ${triple.predicate}`);
    }

    // Check functional property violation
    if (this.config.checkFunctionalProperties) {
      const functionalProps = this.findFunctionalProperties(existingTriples);
      if (functionalProps.has(triple.predicate)) {
        const existing = existingTriples.find(
          t => t.subject === triple.subject &&
               t.predicate === triple.predicate &&
               t.object !== triple.object
        );
        if (existing) {
          errors.push(
            `Functional property violation: ${triple.predicate} already has value ${existing.object} for subject ${triple.subject}`
          );
        }
      }
    }

    // Check inverse functional property violation
    if (this.config.checkInverseFunctionalProperties) {
      const invFunctionalProps = this.findInverseFunctionalProperties(existingTriples);
      if (invFunctionalProps.has(triple.predicate)) {
        const existing = existingTriples.find(
          t => t.predicate === triple.predicate &&
               t.object === triple.object &&
               t.subject !== triple.subject
        );
        if (existing) {
          errors.push(
            `Inverse functional property violation: ${triple.object} is already the value of ${triple.predicate} for subject ${existing.subject}`
          );
        }
      }
    }

    // Check asymmetric property violation
    if (this.config.checkAsymmetricProperties) {
      const asymmetricProps = this.findAsymmetricProperties(existingTriples);
      if (asymmetricProps.has(triple.predicate)) {
        const inverse = existingTriples.find(
          t => t.subject === triple.object &&
               t.predicate === triple.predicate &&
               t.object === triple.subject
        );
        if (inverse) {
          errors.push(
            `Asymmetric property violation: inverse triple exists for ${triple.predicate}`
          );
        }
      }
    }

    // Check irreflexive property violation
    if (this.config.checkIrreflexiveProperties) {
      const irreflexiveProps = this.findIrreflexiveProperties(existingTriples);
      if (irreflexiveProps.has(triple.predicate) && triple.subject === triple.object) {
        errors.push(
          `Irreflexive property violation: ${triple.predicate} cannot relate a resource to itself`
        );
      }
    }

    return {
      valid: errors.length === 0,
      errors,
      warnings,
    };
  }

  /**
   * Find duplicate triples (exact match)
   */
  findDuplicates(triples: Triple[]): Triple[][] {
    const groups = new Map<string, Triple[]>();

    for (const triple of triples) {
      const key = `${triple.subject}|${triple.predicate}|${triple.object}`;
      const existing = groups.get(key) ?? [];
      existing.push(triple);
      groups.set(key, existing);
    }

    return Array.from(groups.values()).filter(g => g.length > 1);
  }

  /**
   * Find semantically equivalent triples
   */
  findSemanticDuplicates(triples: Triple[]): Triple[][] {
    const groups: Triple[][] = [];
    const processed = new Set<number>();

    for (let i = 0; i < triples.length; i++) {
      if (processed.has(i)) continue;

      const group = [triples[i]];
      processed.add(i);

      for (let j = i + 1; j < triples.length; j++) {
        if (processed.has(j)) continue;

        if (this.areSemanticallyEquivalent(triples[i], triples[j])) {
          group.push(triples[j]);
          processed.add(j);
        }
      }

      if (group.length > 1) {
        groups.push(group);
      }
    }

    return groups;
  }

  // ========== Private Methods ==========

  private checkDisjointClasses(triples: Triple[]): ConsistencyViolation[] {
    const violations: ConsistencyViolation[] = [];

    // Find all disjoint class declarations
    const disjointPairs = triples
      .filter(t => t.predicate === OWL.disjointWith)
      .map(t => ({ class1: t.subject, class2: t.object }));

    // Find all type assertions
    const typeAssertions = triples.filter(t => t.predicate === RDF.type);
    const instanceToClasses = new Map<string, Set<string>>();

    for (const assertion of typeAssertions) {
      const classes = instanceToClasses.get(assertion.subject) ?? new Set();
      classes.add(assertion.object);
      instanceToClasses.set(assertion.subject, classes);
    }

    // Check for violations
    for (const { class1, class2 } of disjointPairs) {
      for (const [instance, classes] of instanceToClasses) {
        if (classes.has(class1) && classes.has(class2)) {
          violations.push({
            type: 'disjoint-class-membership',
            message: `Instance ${instance} is member of disjoint classes ${class1} and ${class2}`,
            triples: [
              { subject: instance, predicate: RDF.type, object: class1 },
              { subject: instance, predicate: RDF.type, object: class2 },
            ],
            severity: 'error',
          });
        }
      }
    }

    return violations;
  }

  private checkFunctionalProperties(triples: Triple[]): ConsistencyViolation[] {
    const violations: ConsistencyViolation[] = [];
    const functionalProps = this.findFunctionalProperties(triples);

    for (const prop of functionalProps) {
      const propTriples = triples.filter(t => t.predicate === prop);
      const subjectToValues = new Map<string, Triple[]>();

      for (const triple of propTriples) {
        const existing = subjectToValues.get(triple.subject) ?? [];
        existing.push(triple);
        subjectToValues.set(triple.subject, existing);
      }

      for (const [subject, values] of subjectToValues) {
        const distinctValues = new Set(values.map(v => v.object));
        if (distinctValues.size > 1) {
          violations.push({
            type: 'functional-property-violation',
            message: `Subject ${subject} has ${distinctValues.size} distinct values for functional property ${prop}`,
            triples: values,
            severity: 'error',
          });
        }
      }
    }

    return violations;
  }

  private checkInverseFunctionalProperties(triples: Triple[]): ConsistencyViolation[] {
    const violations: ConsistencyViolation[] = [];
    const invFunctionalProps = this.findInverseFunctionalProperties(triples);

    for (const prop of invFunctionalProps) {
      const propTriples = triples.filter(t => t.predicate === prop);
      const valueToSubjects = new Map<string, Triple[]>();

      for (const triple of propTriples) {
        const existing = valueToSubjects.get(triple.object) ?? [];
        existing.push(triple);
        valueToSubjects.set(triple.object, existing);
      }

      for (const [value, subjects] of valueToSubjects) {
        const distinctSubjects = new Set(subjects.map(s => s.subject));
        if (distinctSubjects.size > 1) {
          violations.push({
            type: 'inverse-functional-violation',
            message: `Value ${value} is shared by ${distinctSubjects.size} distinct subjects for inverse functional property ${prop}`,
            triples: subjects,
            severity: 'error',
          });
        }
      }
    }

    return violations;
  }

  private checkAsymmetricProperties(triples: Triple[]): ConsistencyViolation[] {
    const violations: ConsistencyViolation[] = [];
    const asymmetricProps = this.findAsymmetricProperties(triples);

    for (const prop of asymmetricProps) {
      const propTriples = triples.filter(t => t.predicate === prop);
      
      for (const triple of propTriples) {
        const inverse = propTriples.find(
          t => t.subject === triple.object && t.object === triple.subject
        );

        if (inverse) {
          // Avoid duplicate reporting
          if (triple.subject < triple.object) {
            violations.push({
              type: 'asymmetric-violation',
              message: `Asymmetric property ${prop} has both (${triple.subject}, ${triple.object}) and inverse`,
              triples: [triple, inverse],
              severity: 'error',
            });
          }
        }
      }
    }

    return violations;
  }

  private checkIrreflexiveProperties(triples: Triple[]): ConsistencyViolation[] {
    const violations: ConsistencyViolation[] = [];
    const irreflexiveProps = this.findIrreflexiveProperties(triples);

    for (const prop of irreflexiveProps) {
      const reflexiveTriples = triples.filter(
        t => t.predicate === prop && t.subject === t.object
      );

      for (const triple of reflexiveTriples) {
        violations.push({
          type: 'irreflexive-violation',
          message: `Irreflexive property ${prop} relates ${triple.subject} to itself`,
          triples: [triple],
          severity: 'error',
        });
      }
    }

    return violations;
  }

  private checkDuplicates(triples: Triple[]): ConsistencyViolation[] {
    const violations: ConsistencyViolation[] = [];
    const duplicateGroups = this.findDuplicates(triples);

    for (const group of duplicateGroups) {
      violations.push({
        type: 'duplicate-triple',
        message: `Found ${group.length} duplicate triples`,
        triples: group,
        severity: 'warning',
      });
    }

    return violations;
  }

  private checkCircularDependencies(triples: Triple[]): ConsistencyViolation[] {
    const violations: ConsistencyViolation[] = [];

    // Check for subClassOf cycles
    const subClassTriples = triples.filter(
      t => t.predicate === 'http://www.w3.org/2000/01/rdf-schema#subClassOf'
    );

    const cycles = this.findCycles(subClassTriples);
    for (const cycle of cycles) {
      violations.push({
        type: 'circular-dependency',
        message: `Circular subClassOf dependency: ${cycle.map(t => t.subject).join(' -> ')}`,
        triples: cycle,
        severity: 'error',
      });
    }

    return violations;
  }

  private findCycles(triples: Triple[]): Triple[][] {
    const cycles: Triple[][] = [];
    const graph = new Map<string, string[]>();

    // Build adjacency list
    for (const triple of triples) {
      const edges = graph.get(triple.subject) ?? [];
      edges.push(triple.object);
      graph.set(triple.subject, edges);
    }

    // DFS to find cycles
    const visited = new Set<string>();
    const recursionStack = new Set<string>();
    const path: string[] = [];

    const dfs = (node: string): boolean => {
      visited.add(node);
      recursionStack.add(node);
      path.push(node);

      const neighbors = graph.get(node) ?? [];
      for (const neighbor of neighbors) {
        if (!visited.has(neighbor)) {
          if (dfs(neighbor)) return true;
        } else if (recursionStack.has(neighbor)) {
          // Found cycle
          const cycleStart = path.indexOf(neighbor);
          const cyclePath = path.slice(cycleStart);
          cyclePath.push(neighbor);

          const cycleTriples: Triple[] = [];
          for (let i = 0; i < cyclePath.length - 1; i++) {
            const triple = triples.find(
              t => t.subject === cyclePath[i] && t.object === cyclePath[i + 1]
            );
            if (triple) cycleTriples.push(triple);
          }
          
          if (cycleTriples.length > 0) {
            cycles.push(cycleTriples);
          }
          return true;
        }
      }

      path.pop();
      recursionStack.delete(node);
      return false;
    };

    for (const node of graph.keys()) {
      if (!visited.has(node)) {
        dfs(node);
      }
    }

    return cycles;
  }

  private findFunctionalProperties(triples: Triple[]): Set<string> {
    return new Set(
      triples
        .filter(t => t.predicate === RDF.type && t.object === OWL.FunctionalProperty)
        .map(t => t.subject)
    );
  }

  private findInverseFunctionalProperties(triples: Triple[]): Set<string> {
    return new Set(
      triples
        .filter(t => t.predicate === RDF.type && t.object === OWL.InverseFunctionalProperty)
        .map(t => t.subject)
    );
  }

  private findAsymmetricProperties(triples: Triple[]): Set<string> {
    return new Set(
      triples
        .filter(t => t.predicate === RDF.type && t.object === OWL.AsymmetricProperty)
        .map(t => t.subject)
    );
  }

  private findIrreflexiveProperties(triples: Triple[]): Set<string> {
    return new Set(
      triples
        .filter(t => t.predicate === RDF.type && t.object === OWL.IrreflexiveProperty)
        .map(t => t.subject)
    );
  }

  private isValidUri(uri: string): boolean {
    // Accept URIs and literals
    if (uri.startsWith('http://') || uri.startsWith('https://')) {
      return true;
    }
    // Accept blank nodes
    if (uri.startsWith('_:')) {
      return true;
    }
    // Accept prefixed names (simple check)
    if (/^[a-zA-Z][a-zA-Z0-9]*:[a-zA-Z_][a-zA-Z0-9_-]*$/.test(uri)) {
      return true;
    }
    // Accept literals (anything else)
    return true;
  }

  private areSemanticallyEquivalent(t1: Triple, t2: Triple): boolean {
    // Exact match
    if (t1.subject === t2.subject && t1.predicate === t2.predicate && t1.object === t2.object) {
      return true;
    }

    // Check for equivalent URIs (with/without trailing slash, http vs https)
    const normalizeUri = (uri: string): string => {
      return uri
        .replace(/\/$/, '')
        .replace(/^https:/, 'http:');
    };

    return (
      normalizeUri(t1.subject) === normalizeUri(t2.subject) &&
      normalizeUri(t1.predicate) === normalizeUri(t2.predicate) &&
      normalizeUri(t1.object) === normalizeUri(t2.object)
    );
  }

  private generateSuggestions(violations: ConsistencyViolation[]): ConsistencySuggestion[] {
    return violations.map(v => {
      switch (v.type) {
        case 'disjoint-class-membership':
          return {
            violation: v,
            suggestion: 'Remove one of the class memberships or reconsider disjointness declaration',
            autoFixable: false,
          };
        case 'functional-property-violation':
          return {
            violation: v,
            suggestion: 'Keep only one value for the functional property',
            autoFixable: true,
          };
        case 'inverse-functional-violation':
          return {
            violation: v,
            suggestion: 'Ensure each value uniquely identifies at most one subject',
            autoFixable: false,
          };
        case 'asymmetric-violation':
          return {
            violation: v,
            suggestion: 'Remove one direction of the relationship',
            autoFixable: true,
          };
        case 'irreflexive-violation':
          return {
            violation: v,
            suggestion: 'Remove the self-referencing triple',
            autoFixable: true,
          };
        case 'duplicate-triple':
          return {
            violation: v,
            suggestion: 'Remove duplicate triples',
            autoFixable: true,
          };
        case 'circular-dependency':
          return {
            violation: v,
            suggestion: 'Break the circular dependency by removing one edge',
            autoFixable: false,
          };
        default:
          return {
            violation: v,
            suggestion: 'Review and fix the constraint violation',
            autoFixable: false,
          };
      }
    });
  }
}
