/**
 * Inference Explainer Tests
 *
 * @module learning/inference/__tests__/inference-explainer.test
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { InferenceExplainer } from '../inference-explainer.js';
import { NAMESPACES } from '../types.js';
import type { Triple, AppliedRule, InferenceResult, InferenceStats } from '../types.js';

describe('InferenceExplainer', () => {
  let explainer: InferenceExplainer;

  const createStats = (): InferenceStats => ({
    rulesApplied: 0,
    triplesInferred: 0,
    iterations: 0,
    timeMs: 0,
    fixedPointReached: false,
    inputTriples: 0,
    outputTriples: 0,
  });

  beforeEach(() => {
    explainer = new InferenceExplainer();
  });

  describe('constructor', () => {
    it('should create explainer instance', () => {
      expect(explainer).toBeInstanceOf(InferenceExplainer);
    });
  });

  describe('explain', () => {
    it('should explain a simple subclass inference', () => {
      const conclusion: Triple = {
        subject: 'http://example.org/Dog',
        predicate: `${NAMESPACES.RDF}type`,
        object: 'http://example.org/Animal',
      };

      const appliedRules: AppliedRule[] = [
        {
          ruleId: 'cax-sco',
          ruleName: 'SubClass Inference',
          bindings: {
            x: 'http://example.org/Dog',
            c1: 'http://example.org/Mammal',
            c2: 'http://example.org/Animal',
          },
          inferredTriples: [conclusion],
          appliedAt: Date.now(),
        },
      ];

      const explanation = explainer.explain(conclusion, appliedRules);

      expect(explanation).toBeDefined();
      expect(explanation.conclusion).toBe(conclusion);
      expect(explanation.humanReadable).toContain('サブクラス');
      expect(explanation.rule).toBe('cax-sco');
    });

    it('should explain a symmetric property inference', () => {
      const conclusion: Triple = {
        subject: 'http://example.org/bob',
        predicate: 'http://example.org/knows',
        object: 'http://example.org/alice',
      };

      const appliedRules: AppliedRule[] = [
        {
          ruleId: 'prp-symp',
          ruleName: 'Symmetric Property',
          bindings: {
            x: 'http://example.org/alice',
            y: 'http://example.org/bob',
            p: 'http://example.org/knows',
          },
          inferredTriples: [conclusion],
          appliedAt: Date.now(),
        },
      ];

      const explanation = explainer.explain(conclusion, appliedRules);

      expect(explanation).toBeDefined();
      expect(explanation.humanReadable).toContain('対称');
    });

    it('should return generic explanation for unknown rule', () => {
      const conclusion: Triple = {
        subject: 'http://example.org/x',
        predicate: 'http://example.org/p',
        object: 'http://example.org/y',
      };

      const explanation = explainer.explain(conclusion, []);

      expect(explanation).toBeDefined();
      expect(explanation.rule).toBe('unknown');
    });
  });

  describe('explainAll', () => {
    it('should explain all inferred triples', () => {
      const result: InferenceResult = {
        inferredTriples: [
          {
            subject: 'http://example.org/a',
            predicate: `${NAMESPACES.RDF}type`,
            object: 'http://example.org/B',
          },
          {
            subject: 'http://example.org/c',
            predicate: `${NAMESPACES.RDF}type`,
            object: 'http://example.org/D',
          },
        ],
        appliedRules: [
          {
            ruleId: 'cax-sco',
            ruleName: 'SubClass',
            bindings: {},
            inferredTriples: [
              {
                subject: 'http://example.org/a',
                predicate: `${NAMESPACES.RDF}type`,
                object: 'http://example.org/B',
              },
            ],
            appliedAt: Date.now(),
          },
          {
            ruleId: 'cax-sco',
            ruleName: 'SubClass',
            bindings: {},
            inferredTriples: [
              {
                subject: 'http://example.org/c',
                predicate: `${NAMESPACES.RDF}type`,
                object: 'http://example.org/D',
              },
            ],
            appliedAt: Date.now(),
          },
        ],
        stats: createStats(),
      };

      const explanations = explainer.explainAll(result);

      expect(explanations).toHaveLength(2);
      expect(explanations[0].conclusion.subject).toBe('http://example.org/a');
      expect(explanations[1].conclusion.subject).toBe('http://example.org/c');
    });

    it('should return empty array for empty result', () => {
      const result: InferenceResult = {
        inferredTriples: [],
        appliedRules: [],
        stats: createStats(),
      };

      const explanations = explainer.explainAll(result);

      expect(explanations).toHaveLength(0);
    });
  });

  describe('format', () => {
    const createExplanation = () => ({
      id: 'exp-1',
      conclusion: {
        subject: 'http://example.org/Dog',
        predicate: `${NAMESPACES.RDF}type`,
        object: 'http://example.org/Animal',
      },
      premises: [
        {
          subject: 'http://example.org/Dog',
          predicate: `${NAMESPACES.RDF}type`,
          object: 'http://example.org/Mammal',
        },
      ],
      rule: 'cax-sco',
      humanReadable: 'DogはMammalのインスタンスであり、MammalはAnimalのサブクラスなので、DogはAnimalのインスタンスでもある',
      depth: 1,
      dependsOn: [],
    });

    it('should format as text', () => {
      const explanation = createExplanation();
      const formatted = explainer.format(explanation, 'text');

      expect(formatted).toContain('【推論結果】');
      expect(formatted).toContain('【説明】');
      expect(formatted).toContain('【前提】');
      expect(formatted).toContain('【適用ルール】');
    });

    it('should format as markdown', () => {
      const explanation = createExplanation();
      const formatted = explainer.format(explanation, 'markdown');

      expect(formatted).toContain('### 推論結果');
      expect(formatted).toContain('**結論**');
      expect(formatted).toContain('### 説明');
      expect(formatted).toContain('> ');
    });

    it('should format as HTML', () => {
      const explanation = createExplanation();
      const formatted = explainer.format(explanation, 'html');

      expect(formatted).toContain('<div class="inference-explanation">');
      expect(formatted).toContain('<h4>推論結果</h4>');
      expect(formatted).toContain('<span class="subject">');
    });

    it('should escape HTML entities', () => {
      const explanation = {
        ...createExplanation(),
        humanReadable: 'Test <script>alert("xss")</script>',
      };

      const formatted = explainer.format(explanation, 'html');

      expect(formatted).not.toContain('<script>');
      expect(formatted).toContain('&lt;script&gt;');
    });
  });

  describe('URI shortening', () => {
    it('should shorten known namespace URIs', () => {
      const conclusion: Triple = {
        subject: 'http://example.org/x',
        predicate: `${NAMESPACES.RDF}type`,
        object: `${NAMESPACES.OWL}Class`,
      };

      const explanation = explainer.explain(conclusion, []);

      // The human-readable should use shortened forms
      expect(explanation.humanReadable).toBeDefined();
    });

    it('should extract local name from unknown URIs', () => {
      const conclusion: Triple = {
        subject: 'http://example.org/namespace#LocalName',
        predicate: 'http://example.org/pred',
        object: 'http://example.org/path/Object',
      };

      const explanation = explainer.explain(conclusion, []);

      expect(explanation.humanReadable).toBeDefined();
    });
  });

  describe('addTemplate', () => {
    it('should add custom template', () => {
      explainer.addTemplate(
        /custom-rule/,
        () => 'カスタムルールによる推論'
      );

      const conclusion: Triple = {
        subject: 'http://example.org/x',
        predicate: 'http://example.org/p',
        object: 'http://example.org/y',
      };

      const appliedRules: AppliedRule[] = [
        {
          ruleId: 'custom-rule',
          ruleName: 'Custom Rule',
          bindings: {},
          inferredTriples: [conclusion],
          appliedAt: Date.now(),
        },
      ];

      const explanation = explainer.explain(conclusion, appliedRules);

      expect(explanation.humanReadable).toBe('カスタムルールによる推論');
    });
  });

  describe('reset', () => {
    it('should reset explanation counter', () => {
      const conclusion: Triple = {
        subject: 'http://example.org/x',
        predicate: 'http://example.org/p',
        object: 'http://example.org/y',
      };

      // Generate some explanations
      explainer.explain(conclusion, []);
      explainer.explain(conclusion, []);

      explainer.reset();

      const explanation = explainer.explain(conclusion, []);

      // Counter should be reset to 1
      expect(explanation.id).toBe('exp-1');
    });
  });
});
