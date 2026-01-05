/**
 * @fileoverview Inference Rule Engine for Ontology Store
 * @traceability TSK-ONTO-002, REQ-ONTO-001
 */

import type { Triple } from '../types.js';

/**
 * Rule condition types
 */
export type RuleCondition = {
  type: 'triple-pattern';
  subject?: string | { variable: string };
  predicate?: string | { variable: string };
  object?: string | { variable: string };
} | {
  type: 'transitive';
  predicate: string;
} | {
  type: 'symmetric';
  predicate: string;
} | {
  type: 'inverse';
  predicate1: string;
  predicate2: string;
};

/**
 * Rule action types
 */
export type RuleAction = {
  type: 'add-triple';
  subject: string | { variable: string };
  predicate: string;
  object: string | { variable: string };
};

/**
 * Inference rule definition
 */
export interface InferenceRuleDefinition {
  id: string;
  name: string;
  description?: string;
  priority: number;
  conditions: RuleCondition[];
  actions: RuleAction[];
}

/**
 * Binding map for variables
 */
export type Bindings = Record<string, string>;

/**
 * Rule match result
 */
export interface RuleMatch {
  ruleId: string;
  bindings: Bindings;
  inferredTriples: Triple[];
}

/**
 * Inference statistics
 */
export interface InferenceStats {
  rulesApplied: number;
  triplesInferred: number;
  iterationsUsed: number;
  timeMs: number;
}

/**
 * RDFS namespace constants
 */
const RDFS = {
  subClassOf: 'http://www.w3.org/2000/01/rdf-schema#subClassOf',
  subPropertyOf: 'http://www.w3.org/2000/01/rdf-schema#subPropertyOf',
  domain: 'http://www.w3.org/2000/01/rdf-schema#domain',
  range: 'http://www.w3.org/2000/01/rdf-schema#range',
};

const RDF = {
  type: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
};

const OWL = {
  TransitiveProperty: 'http://www.w3.org/2002/07/owl#TransitiveProperty',
  SymmetricProperty: 'http://www.w3.org/2002/07/owl#SymmetricProperty',
  InverseFunctionalProperty: 'http://www.w3.org/2002/07/owl#InverseFunctionalProperty',
  inverseOf: 'http://www.w3.org/2002/07/owl#inverseOf',
  sameAs: 'http://www.w3.org/2002/07/owl#sameAs',
};

/**
 * Rule Engine for applying inference rules
 */
export class RuleEngine {
  private rules: Map<string, InferenceRuleDefinition> = new Map();
  private maxIterations: number;

  constructor(options?: { maxIterations?: number }) {
    this.maxIterations = options?.maxIterations ?? 10;
    this.loadBuiltinRules();
  }

  /**
   * Load built-in RDFS/OWL inference rules
   */
  private loadBuiltinRules(): void {
    // RDFS9: subClassOf transitivity
    this.addRule({
      id: 'rdfs9',
      name: 'RDFS SubClass Transitivity',
      description: 'If X subClassOf Y and Y subClassOf Z, then X subClassOf Z',
      priority: 100,
      conditions: [
        { type: 'transitive', predicate: RDFS.subClassOf },
      ],
      actions: [],
    });

    // RDFS7: subPropertyOf transitivity
    this.addRule({
      id: 'rdfs7',
      name: 'RDFS SubProperty Transitivity',
      description: 'If P subPropertyOf Q and Q subPropertyOf R, then P subPropertyOf R',
      priority: 100,
      conditions: [
        { type: 'transitive', predicate: RDFS.subPropertyOf },
      ],
      actions: [],
    });

    // RDFS11: type inheritance through subClassOf
    this.addRule({
      id: 'rdfs11',
      name: 'RDFS Type Inheritance',
      description: 'If X type C and C subClassOf D, then X type D',
      priority: 90,
      conditions: [
        {
          type: 'triple-pattern',
          subject: { variable: 'x' },
          predicate: RDF.type,
          object: { variable: 'c' },
        },
        {
          type: 'triple-pattern',
          subject: { variable: 'c' },
          predicate: RDFS.subClassOf,
          object: { variable: 'd' },
        },
      ],
      actions: [
        {
          type: 'add-triple',
          subject: { variable: 'x' },
          predicate: RDF.type,
          object: { variable: 'd' },
        },
      ],
    });

    // OWL symmetric property
    this.addRule({
      id: 'owl-symmetric',
      name: 'OWL Symmetric Property',
      description: 'If P is symmetric and X P Y, then Y P X',
      priority: 80,
      conditions: [
        { type: 'symmetric', predicate: '' }, // Placeholder, matched dynamically
      ],
      actions: [],
    });

    // OWL inverse property
    this.addRule({
      id: 'owl-inverse',
      name: 'OWL Inverse Property',
      description: 'If P inverseOf Q and X P Y, then Y Q X',
      priority: 80,
      conditions: [
        { type: 'inverse', predicate1: '', predicate2: '' },
      ],
      actions: [],
    });

    // OWL sameAs transitivity
    this.addRule({
      id: 'owl-sameas-trans',
      name: 'OWL SameAs Transitivity',
      description: 'If X sameAs Y and Y sameAs Z, then X sameAs Z',
      priority: 70,
      conditions: [
        { type: 'transitive', predicate: OWL.sameAs },
      ],
      actions: [],
    });

    // OWL sameAs symmetry
    this.addRule({
      id: 'owl-sameas-sym',
      name: 'OWL SameAs Symmetry',
      description: 'If X sameAs Y, then Y sameAs X',
      priority: 70,
      conditions: [
        { type: 'symmetric', predicate: OWL.sameAs },
      ],
      actions: [],
    });
  }

  /**
   * Add a rule to the engine
   */
  addRule(rule: InferenceRuleDefinition): void {
    this.rules.set(rule.id, rule);
  }

  /**
   * Remove a rule
   */
  removeRule(ruleId: string): boolean {
    return this.rules.delete(ruleId);
  }

  /**
   * Get all rules
   */
  getRules(): InferenceRuleDefinition[] {
    return Array.from(this.rules.values())
      .sort((a, b) => b.priority - a.priority);
  }

  /**
   * Apply all rules to triples until fixpoint
   */
  applyRules(triples: Triple[]): { triples: Triple[]; stats: InferenceStats } {
    const startTime = Date.now();
    const tripleSet = new Set(triples.map(t => this.tripleKey(t)));
    const allTriples = [...triples];
    let rulesApplied = 0;
    let triplesInferred = 0;

    // Get symmetric and inverse properties
    const symmetricProps = this.getSymmetricProperties(allTriples);
    const inverseProps = this.getInverseProperties(allTriples);

    for (let iteration = 0; iteration < this.maxIterations; iteration++) {
      const newTriples: Triple[] = [];

      // Apply transitive closure rules
      for (const rule of this.getRules()) {
        for (const condition of rule.conditions) {
          if (condition.type === 'transitive') {
            const inferred = this.applyTransitiveClosure(
              allTriples,
              condition.predicate,
              tripleSet
            );
            newTriples.push(...inferred);
            if (inferred.length > 0) rulesApplied++;
          }

          if (condition.type === 'symmetric') {
            const predicate = condition.predicate || '';
            const predicates = predicate ? [predicate] : symmetricProps;
            for (const p of predicates) {
              const inferred = this.applySymmetry(allTriples, p, tripleSet);
              newTriples.push(...inferred);
              if (inferred.length > 0) rulesApplied++;
            }
          }

          if (condition.type === 'inverse') {
            for (const [p1, p2] of inverseProps) {
              const inferred = this.applyInverse(allTriples, p1, p2, tripleSet);
              newTriples.push(...inferred);
              if (inferred.length > 0) rulesApplied++;
            }
          }
        }
      }

      // Apply pattern-based rules
      for (const rule of this.getRules()) {
        const matches = this.matchRule(rule, allTriples);
        for (const match of matches) {
          for (const triple of match.inferredTriples) {
            const key = this.tripleKey(triple);
            if (!tripleSet.has(key)) {
              tripleSet.add(key);
              newTriples.push(triple);
              rulesApplied++;
            }
          }
        }
      }

      if (newTriples.length === 0) {
        // Fixpoint reached
        return {
          triples: allTriples,
          stats: {
            rulesApplied,
            triplesInferred,
            iterationsUsed: iteration + 1,
            timeMs: Date.now() - startTime,
          },
        };
      }

      triplesInferred += newTriples.length;
      allTriples.push(...newTriples);
    }

    return {
      triples: allTriples,
      stats: {
        rulesApplied,
        triplesInferred,
        iterationsUsed: this.maxIterations,
        timeMs: Date.now() - startTime,
      },
    };
  }

  /**
   * Apply transitive closure for a predicate
   */
  private applyTransitiveClosure(
    triples: Triple[],
    predicate: string,
    existingKeys: Set<string>
  ): Triple[] {
    const inferred: Triple[] = [];
    const edges = triples.filter(t => t.predicate === predicate);

    // Build adjacency map
    const adjacency = new Map<string, Set<string>>();
    for (const edge of edges) {
      if (!adjacency.has(edge.subject)) {
        adjacency.set(edge.subject, new Set());
      }
      adjacency.get(edge.subject)!.add(edge.object);
    }

    // Compute transitive closure using Warshall-like algorithm
    for (const [start, directTargets] of adjacency) {
      const visited = new Set<string>();
      const queue = [...directTargets];

      while (queue.length > 0) {
        const current = queue.shift()!;
        if (visited.has(current)) continue;
        visited.add(current);

        const nextTargets = adjacency.get(current);
        if (nextTargets) {
          for (const next of nextTargets) {
            if (!visited.has(next)) {
              const newTriple: Triple = {
                subject: start,
                predicate,
                object: next,
              };
              const key = this.tripleKey(newTriple);
              if (!existingKeys.has(key)) {
                existingKeys.add(key);
                inferred.push(newTriple);
              }
              queue.push(next);
            }
          }
        }
      }
    }

    return inferred;
  }

  /**
   * Apply symmetry for a predicate
   */
  private applySymmetry(
    triples: Triple[],
    predicate: string,
    existingKeys: Set<string>
  ): Triple[] {
    const inferred: Triple[] = [];
    const edges = triples.filter(t => t.predicate === predicate);

    for (const edge of edges) {
      const inverse: Triple = {
        subject: edge.object,
        predicate: edge.predicate,
        object: edge.subject,
      };
      const key = this.tripleKey(inverse);
      if (!existingKeys.has(key)) {
        existingKeys.add(key);
        inferred.push(inverse);
      }
    }

    return inferred;
  }

  /**
   * Apply inverse property rule
   */
  private applyInverse(
    triples: Triple[],
    predicate1: string,
    predicate2: string,
    existingKeys: Set<string>
  ): Triple[] {
    const inferred: Triple[] = [];

    // P1(X, Y) => P2(Y, X)
    for (const t of triples.filter(t => t.predicate === predicate1)) {
      const inverse: Triple = {
        subject: t.object,
        predicate: predicate2,
        object: t.subject,
      };
      const key = this.tripleKey(inverse);
      if (!existingKeys.has(key)) {
        existingKeys.add(key);
        inferred.push(inverse);
      }
    }

    // P2(X, Y) => P1(Y, X)
    for (const t of triples.filter(t => t.predicate === predicate2)) {
      const inverse: Triple = {
        subject: t.object,
        predicate: predicate1,
        object: t.subject,
      };
      const key = this.tripleKey(inverse);
      if (!existingKeys.has(key)) {
        existingKeys.add(key);
        inferred.push(inverse);
      }
    }

    return inferred;
  }

  /**
   * Get symmetric properties from triples
   */
  private getSymmetricProperties(triples: Triple[]): string[] {
    return triples
      .filter(t =>
        t.predicate === RDF.type &&
        t.object === OWL.SymmetricProperty
      )
      .map(t => t.subject);
  }

  /**
   * Get inverse property pairs from triples
   */
  private getInverseProperties(triples: Triple[]): [string, string][] {
    return triples
      .filter(t => t.predicate === OWL.inverseOf)
      .map(t => [t.subject, t.object] as [string, string]);
  }

  /**
   * Match a rule against triples
   */
  private matchRule(rule: InferenceRuleDefinition, triples: Triple[]): RuleMatch[] {
    const matches: RuleMatch[] = [];

    // Only handle pattern-based rules here
    const patternConditions = rule.conditions.filter(
      c => c.type === 'triple-pattern'
    ) as Extract<RuleCondition, { type: 'triple-pattern' }>[];

    if (patternConditions.length === 0 || rule.actions.length === 0) {
      return matches;
    }

    // For simplicity, handle single and dual pattern rules
    if (patternConditions.length === 1) {
      const pattern = patternConditions[0];
      for (const triple of triples) {
        const bindings = this.matchPattern(pattern, triple);
        if (bindings) {
          const inferredTriples = this.applyActions(rule.actions, bindings);
          if (inferredTriples.length > 0) {
            matches.push({
              ruleId: rule.id,
              bindings,
              inferredTriples,
            });
          }
        }
      }
    } else if (patternConditions.length === 2) {
      // Join two patterns
      const [pattern1, pattern2] = patternConditions;
      for (const t1 of triples) {
        const bindings1 = this.matchPattern(pattern1, t1);
        if (bindings1) {
          for (const t2 of triples) {
            const bindings2 = this.matchPattern(pattern2, t2);
            if (bindings2 && this.compatibleBindings(bindings1, bindings2)) {
              const merged = { ...bindings1, ...bindings2 };
              const inferredTriples = this.applyActions(rule.actions, merged);
              if (inferredTriples.length > 0) {
                matches.push({
                  ruleId: rule.id,
                  bindings: merged,
                  inferredTriples,
                });
              }
            }
          }
        }
      }
    }

    return matches;
  }

  /**
   * Match a pattern against a triple
   */
  private matchPattern(
    pattern: Extract<RuleCondition, { type: 'triple-pattern' }>,
    triple: Triple
  ): Bindings | null {
    const bindings: Bindings = {};

    // Match subject
    if (pattern.subject) {
      if (typeof pattern.subject === 'string') {
        if (pattern.subject !== triple.subject) return null;
      } else {
        bindings[pattern.subject.variable] = triple.subject;
      }
    }

    // Match predicate
    if (pattern.predicate) {
      if (typeof pattern.predicate === 'string') {
        if (pattern.predicate !== triple.predicate) return null;
      } else {
        bindings[pattern.predicate.variable] = triple.predicate;
      }
    }

    // Match object
    if (pattern.object) {
      if (typeof pattern.object === 'string') {
        if (pattern.object !== triple.object) return null;
      } else {
        bindings[pattern.object.variable] = triple.object;
      }
    }

    return bindings;
  }

  /**
   * Check if two binding sets are compatible
   */
  private compatibleBindings(b1: Bindings, b2: Bindings): boolean {
    for (const key of Object.keys(b1)) {
      if (key in b2 && b1[key] !== b2[key]) {
        return false;
      }
    }
    return true;
  }

  /**
   * Apply actions with bindings
   */
  private applyActions(actions: RuleAction[], bindings: Bindings): Triple[] {
    const result: Triple[] = [];

    for (const action of actions) {
      if (action.type === 'add-triple') {
        const subject = typeof action.subject === 'string'
          ? action.subject
          : bindings[action.subject.variable];
        const predicate = action.predicate;
        const object = typeof action.object === 'string'
          ? action.object
          : bindings[action.object.variable];

        if (subject && predicate && object) {
          result.push({ subject, predicate, object });
        }
      }
    }

    return result;
  }

  /**
   * Create unique key for triple
   */
  private tripleKey(triple: Triple): string {
    return `${triple.subject}|${triple.predicate}|${triple.object}`;
  }
}
