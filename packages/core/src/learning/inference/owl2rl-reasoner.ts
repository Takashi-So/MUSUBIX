/**
 * OWL 2 RL Reasoner
 *
 * @module learning/inference/owl2rl-reasoner
 * @description OWL 2 RLプロファイル推論エンジン
 * @requirements REQ-ONTO-010, REQ-ONTO-011
 */

import type {
  Triple,
  OWL2RLRule,
  OWL2RLRuleType,
  DatalogRule,
  DatalogAtom,
  DatalogTerm,
  Bindings,
  InferenceResult,
  AppliedRule,
  InferenceStats,
  InferenceProgress,
  ReasonerOptions,
  IReasoner,
} from './types.js';
import { NAMESPACES } from './types.js';

/**
 * OWL 2 RL組み込みルール
 */
export const OWL2RL_RULES: OWL2RLRule[] = [
  // ===== Class Expression Axioms =====
  {
    id: 'cls-thing',
    name: 'Everything is owl:Thing',
    description: 'Every individual is an instance of owl:Thing',
    antecedent: ['?x rdf:type ?c'],
    consequent: ['?x rdf:type owl:Thing'],
    priority: 100,
    enabled: true,
  },
  {
    id: 'cax-sco',
    name: 'SubClass Inheritance',
    description: 'If x is of type c1 and c1 subClassOf c2, then x is of type c2',
    antecedent: ['?x rdf:type ?c1', '?c1 rdfs:subClassOf ?c2'],
    consequent: ['?x rdf:type ?c2'],
    priority: 90,
    enabled: true,
  },
  {
    id: 'cax-eqc1',
    name: 'Equivalent Class 1',
    description: 'If c1 equivalentClass c2 and x type c1, then x type c2',
    antecedent: ['?c1 owl:equivalentClass ?c2', '?x rdf:type ?c1'],
    consequent: ['?x rdf:type ?c2'],
    priority: 85,
    enabled: true,
  },
  {
    id: 'cax-eqc2',
    name: 'Equivalent Class 2',
    description: 'If c1 equivalentClass c2 and x type c2, then x type c1',
    antecedent: ['?c1 owl:equivalentClass ?c2', '?x rdf:type ?c2'],
    consequent: ['?x rdf:type ?c1'],
    priority: 85,
    enabled: true,
  },

  // ===== Property Expression Axioms =====
  {
    id: 'prp-dom',
    name: 'Property Domain',
    description: 'If p has domain c and x p y, then x type c',
    antecedent: ['?p rdfs:domain ?c', '?x ?p ?y'],
    consequent: ['?x rdf:type ?c'],
    priority: 80,
    enabled: true,
  },
  {
    id: 'prp-rng',
    name: 'Property Range',
    description: 'If p has range c and x p y, then y type c',
    antecedent: ['?p rdfs:range ?c', '?x ?p ?y'],
    consequent: ['?y rdf:type ?c'],
    priority: 80,
    enabled: true,
  },
  {
    id: 'prp-symp',
    name: 'Symmetric Property',
    description: 'If p is symmetric and x p y, then y p x',
    antecedent: ['?p rdf:type owl:SymmetricProperty', '?x ?p ?y'],
    consequent: ['?y ?p ?x'],
    priority: 75,
    enabled: true,
  },
  {
    id: 'prp-trp',
    name: 'Transitive Property',
    description: 'If p is transitive and x p y and y p z, then x p z',
    antecedent: ['?p rdf:type owl:TransitiveProperty', '?x ?p ?y', '?y ?p ?z'],
    consequent: ['?x ?p ?z'],
    priority: 75,
    enabled: true,
  },
  {
    id: 'prp-inv1',
    name: 'Inverse Property 1',
    description: 'If p1 inverseOf p2 and x p1 y, then y p2 x',
    antecedent: ['?p1 owl:inverseOf ?p2', '?x ?p1 ?y'],
    consequent: ['?y ?p2 ?x'],
    priority: 75,
    enabled: true,
  },
  {
    id: 'prp-inv2',
    name: 'Inverse Property 2',
    description: 'If p1 inverseOf p2 and x p2 y, then y p1 x',
    antecedent: ['?p1 owl:inverseOf ?p2', '?x ?p2 ?y'],
    consequent: ['?y ?p1 ?x'],
    priority: 75,
    enabled: true,
  },
  {
    id: 'prp-spo1',
    name: 'SubProperty Inheritance',
    description: 'If p1 subPropertyOf p2 and x p1 y, then x p2 y',
    antecedent: ['?p1 rdfs:subPropertyOf ?p2', '?x ?p1 ?y'],
    consequent: ['?x ?p2 ?y'],
    priority: 85,
    enabled: true,
  },
  {
    id: 'prp-eqp1',
    name: 'Equivalent Property 1',
    description: 'If p1 equivalentProperty p2 and x p1 y, then x p2 y',
    antecedent: ['?p1 owl:equivalentProperty ?p2', '?x ?p1 ?y'],
    consequent: ['?x ?p2 ?y'],
    priority: 80,
    enabled: true,
  },
  {
    id: 'prp-eqp2',
    name: 'Equivalent Property 2',
    description: 'If p1 equivalentProperty p2 and x p2 y, then x p1 y',
    antecedent: ['?p1 owl:equivalentProperty ?p2', '?x ?p2 ?y'],
    consequent: ['?x ?p1 ?y'],
    priority: 80,
    enabled: true,
  },

  // ===== Equality Axioms =====
  {
    id: 'eq-ref',
    name: 'Reflexive sameAs',
    description: 'Everything is sameAs itself',
    antecedent: ['?x ?p ?y'],
    consequent: ['?x owl:sameAs ?x'],
    priority: 70,
    enabled: false, // 通常は無効（大量の推論を生成）
  },
  {
    id: 'eq-sym',
    name: 'Symmetric sameAs',
    description: 'If x sameAs y, then y sameAs x',
    antecedent: ['?x owl:sameAs ?y'],
    consequent: ['?y owl:sameAs ?x'],
    priority: 70,
    enabled: true,
  },
  {
    id: 'eq-trans',
    name: 'Transitive sameAs',
    description: 'If x sameAs y and y sameAs z, then x sameAs z',
    antecedent: ['?x owl:sameAs ?y', '?y owl:sameAs ?z'],
    consequent: ['?x owl:sameAs ?z'],
    priority: 70,
    enabled: true,
  },
  {
    id: 'eq-rep-s',
    name: 'Replace Subject',
    description: 'If s sameAs s2 and s p o, then s2 p o',
    antecedent: ['?s owl:sameAs ?s2', '?s ?p ?o'],
    consequent: ['?s2 ?p ?o'],
    priority: 65,
    enabled: true,
  },
  {
    id: 'eq-rep-o',
    name: 'Replace Object',
    description: 'If o sameAs o2 and s p o, then s p o2',
    antecedent: ['?o owl:sameAs ?o2', '?s ?p ?o'],
    consequent: ['?s ?p ?o2'],
    priority: 65,
    enabled: true,
  },

  // ===== Schema Vocabulary =====
  {
    id: 'scm-sco',
    name: 'SubClass Transitivity',
    description: 'If c1 subClassOf c2 and c2 subClassOf c3, then c1 subClassOf c3',
    antecedent: ['?c1 rdfs:subClassOf ?c2', '?c2 rdfs:subClassOf ?c3'],
    consequent: ['?c1 rdfs:subClassOf ?c3'],
    priority: 95,
    enabled: true,
  },
  {
    id: 'scm-spo',
    name: 'SubProperty Transitivity',
    description: 'If p1 subPropertyOf p2 and p2 subPropertyOf p3, then p1 subPropertyOf p3',
    antecedent: ['?p1 rdfs:subPropertyOf ?p2', '?p2 rdfs:subPropertyOf ?p3'],
    consequent: ['?p1 rdfs:subPropertyOf ?p3'],
    priority: 95,
    enabled: true,
  },
  {
    id: 'scm-eqc1',
    name: 'EquivalentClass to SubClass 1',
    description: 'If c1 equivalentClass c2, then c1 subClassOf c2',
    antecedent: ['?c1 owl:equivalentClass ?c2'],
    consequent: ['?c1 rdfs:subClassOf ?c2'],
    priority: 90,
    enabled: true,
  },
  {
    id: 'scm-eqc2',
    name: 'EquivalentClass to SubClass 2',
    description: 'If c1 equivalentClass c2, then c2 subClassOf c1',
    antecedent: ['?c1 owl:equivalentClass ?c2'],
    consequent: ['?c2 rdfs:subClassOf ?c1'],
    priority: 90,
    enabled: true,
  },
];

/**
 * OWL 2 RL Reasoner
 * REQ-ONTO-010: OWL 2 RLプロファイル推論
 * REQ-ONTO-011: 200ms以内の推論
 */
export class OWL2RLReasoner implements IReasoner {
  private rules: Map<string, OWL2RLRule> = new Map();
  private customRules: Map<string, DatalogRule> = new Map();
  private stats: InferenceStats;
  private prefixes: Map<string, string> = new Map();

  constructor() {
    this.stats = this.createEmptyStats();
    this.initializePrefixes();
    this.loadBuiltinRules();
  }

  /**
   * プレフィックスを初期化
   */
  private initializePrefixes(): void {
    this.prefixes.set('rdf', NAMESPACES.RDF);
    this.prefixes.set('rdfs', NAMESPACES.RDFS);
    this.prefixes.set('owl', NAMESPACES.OWL);
    this.prefixes.set('xsd', NAMESPACES.XSD);
    this.prefixes.set('musubix', NAMESPACES.MUSUBIX);
  }

  /**
   * 組み込みルールをロード
   */
  private loadBuiltinRules(): void {
    for (const rule of OWL2RL_RULES) {
      this.rules.set(rule.id, rule);
    }
  }

  /**
   * 空の統計を作成
   */
  private createEmptyStats(): InferenceStats {
    return {
      rulesApplied: 0,
      triplesInferred: 0,
      iterations: 0,
      timeMs: 0,
      fixedPointReached: false,
      inputTriples: 0,
      outputTriples: 0,
    };
  }

  /**
   * 推論を実行
   * REQ-ONTO-011: 200ms以内の推論
   */
  async infer(triples: Triple[], options: ReasonerOptions = {}): Promise<InferenceResult> {
    const startTime = Date.now();
    const maxIterations = options.maxIterations ?? 10;
    const timeout = options.timeout ?? 200; // デフォルト200ms (REQ-ONTO-011)

    // 統計を初期化
    this.stats = this.createEmptyStats();
    this.stats.inputTriples = triples.length;

    // 有効なルールをフィルタ
    const enabledRules = this.getEnabledRules(options);

    // トリプルセットを初期化（重複排除）
    const tripleSet = new Map<string, Triple>();
    for (const triple of triples) {
      const key = this.tripleKey(triple);
      tripleSet.set(key, triple);
    }

    const appliedRules: AppliedRule[] = [];
    let iteration = 0;
    let fixedPointReached = false;

    // 進捗レポート
    const reportProgress = (phase: InferenceProgress['phase'], message: string) => {
      if (options.onProgress) {
        const elapsed = Date.now() - startTime;
        options.onProgress({
          phase,
          totalTriples: triples.length,
          processedTriples: tripleSet.size,
          inferredTriples: this.stats.triplesInferred,
          elapsedMs: elapsed,
          estimatedRemainingMs: iteration > 0 ? (elapsed / iteration) * (maxIterations - iteration) : 0,
          message,
        });
      }
    };

    reportProgress('initializing', 'Starting OWL 2 RL reasoning...');

    // 固定点に達するまでまたは最大反復回数まで推論
    while (iteration < maxIterations) {
      const elapsed = Date.now() - startTime;

      // タイムアウトチェック
      if (elapsed > timeout) {
        reportProgress('reasoning', `Timeout reached at iteration ${iteration}`);
        break;
      }

      iteration++;
      this.stats.iterations = iteration;
      reportProgress('reasoning', `Iteration ${iteration}/${maxIterations}`);

      const newTriples: Triple[] = [];

      // 各ルールを適用
      for (const rule of enabledRules) {
        const ruleResults = this.applyRule(rule, Array.from(tripleSet.values()));

        for (const result of ruleResults) {
          const key = this.tripleKey(result.triple);
          if (!tripleSet.has(key)) {
            tripleSet.set(key, result.triple);
            newTriples.push(result.triple);

            appliedRules.push({
              ruleId: rule.id,
              ruleName: rule.name,
              bindings: result.bindings,
              inferredTriples: [result.triple],
              appliedAt: Date.now(),
            });

            this.stats.rulesApplied++;
          }
        }
      }

      // カスタムDatalogルールを適用
      for (const rule of this.customRules.values()) {
        if (rule.enabled) {
          const ruleResults = this.applyDatalogRule(rule, Array.from(tripleSet.values()));
          for (const result of ruleResults) {
            const key = this.tripleKey(result.triple);
            if (!tripleSet.has(key)) {
              tripleSet.set(key, result.triple);
              newTriples.push(result.triple);

              appliedRules.push({
                ruleId: rule.id,
                ruleName: rule.name,
                bindings: result.bindings,
                inferredTriples: [result.triple],
                appliedAt: Date.now(),
              });

              this.stats.rulesApplied++;
            }
          }
        }
      }

      this.stats.triplesInferred += newTriples.length;

      // 新しいトリプルがなければ固定点到達
      if (newTriples.length === 0) {
        fixedPointReached = true;
        break;
      }
    }

    // 統計を更新
    this.stats.timeMs = Date.now() - startTime;
    this.stats.fixedPointReached = fixedPointReached;
    this.stats.outputTriples = tripleSet.size;

    reportProgress('completed', `Reasoning completed: ${this.stats.triplesInferred} triples inferred`);

    return {
      inferredTriples: Array.from(tripleSet.values()).filter(
        (t) => !triples.some((orig) => this.tripleKey(orig) === this.tripleKey(t))
      ),
      appliedRules,
      stats: { ...this.stats },
    };
  }

  /**
   * 有効なルールを取得
   */
  private getEnabledRules(options: ReasonerOptions): OWL2RLRule[] {
    let rules = Array.from(this.rules.values()).filter((r) => r.enabled);

    if (options.enabledRules) {
      rules = rules.filter((r) => options.enabledRules!.includes(r.id));
    }

    if (options.disabledRules) {
      rules = rules.filter((r) => !options.disabledRules!.includes(r.id));
    }

    return rules.sort((a, b) => b.priority - a.priority);
  }

  /**
   * ルールを適用
   */
  private applyRule(
    rule: OWL2RLRule,
    triples: Triple[]
  ): Array<{ triple: Triple; bindings: Bindings }> {
    const results: Array<{ triple: Triple; bindings: Bindings }> = [];

    // 前提条件をパース
    const antecedentPatterns = rule.antecedent.map((a) => this.parsePattern(a));
    const consequentPatterns = rule.consequent.map((c) => this.parsePattern(c));

    // バインディングを検索
    const allBindings = this.findBindings(antecedentPatterns, triples);

    // 各バインディングに対して結論を生成
    for (const bindings of allBindings) {
      for (const pattern of consequentPatterns) {
        const triple = this.instantiatePattern(pattern, bindings);
        if (triple) {
          results.push({ triple, bindings });
        }
      }
    }

    return results;
  }

  /**
   * Datalogルールを適用
   */
  private applyDatalogRule(
    rule: DatalogRule,
    triples: Triple[]
  ): Array<{ triple: Triple; bindings: Bindings }> {
    const results: Array<{ triple: Triple; bindings: Bindings }> = [];

    // ボディをトリプルパターンに変換
    const bodyPatterns = rule.body.map((atom) => this.atomToPattern(atom));

    // バインディングを検索
    const allBindings = this.findBindings(bodyPatterns, triples);

    // 各バインディングに対してヘッドを具体化
    for (const bindings of allBindings) {
      const triple = this.instantiateAtom(rule.head, bindings);
      if (triple) {
        results.push({ triple, bindings });
      }
    }

    return results;
  }

  /**
   * パターンをパース
   */
  private parsePattern(pattern: string): { s: string; p: string; o: string } {
    const expanded = this.expandPrefixes(pattern.trim());
    const parts = expanded.split(/\s+/);
    return {
      s: parts[0] || '',
      p: parts[1] || '',
      o: parts[2] || '',
    };
  }

  /**
   * プレフィックスを展開
   */
  private expandPrefixes(str: string): string {
    let result = str;
    for (const [prefix, uri] of this.prefixes) {
      result = result.replace(new RegExp(`\\b${prefix}:`, 'g'), uri);
    }
    return result;
  }

  /**
   * バインディングを検索
   */
  private findBindings(
    patterns: Array<{ s: string; p: string; o: string }>,
    triples: Triple[]
  ): Bindings[] {
    if (patterns.length === 0) return [{}];

    let currentBindings: Bindings[] = [{}];

    for (const pattern of patterns) {
      const newBindings: Bindings[] = [];

      for (const bindings of currentBindings) {
        const matches = this.matchPattern(pattern, triples, bindings);
        newBindings.push(...matches);
      }

      currentBindings = newBindings;

      if (currentBindings.length === 0) break;
    }

    return currentBindings;
  }

  /**
   * パターンをマッチ
   */
  private matchPattern(
    pattern: { s: string; p: string; o: string },
    triples: Triple[],
    existingBindings: Bindings
  ): Bindings[] {
    const results: Bindings[] = [];

    for (const triple of triples) {
      const newBindings = this.tryMatch(pattern, triple, existingBindings);
      if (newBindings) {
        results.push(newBindings);
      }
    }

    return results;
  }

  /**
   * マッチを試行
   */
  private tryMatch(
    pattern: { s: string; p: string; o: string },
    triple: Triple,
    existingBindings: Bindings
  ): Bindings | null {
    const bindings = { ...existingBindings };

    // Subject
    if (!this.matchTerm(pattern.s, triple.subject, bindings)) return null;

    // Predicate
    if (!this.matchTerm(pattern.p, triple.predicate, bindings)) return null;

    // Object
    if (!this.matchTerm(pattern.o, triple.object, bindings)) return null;

    return bindings;
  }

  /**
   * 項をマッチ
   */
  private matchTerm(pattern: string, value: string, bindings: Bindings): boolean {
    if (pattern.startsWith('?')) {
      const varName = pattern.substring(1);
      if (varName in bindings) {
        return bindings[varName] === value;
      }
      bindings[varName] = value;
      return true;
    }
    return pattern === value;
  }

  /**
   * パターンを具体化
   */
  private instantiatePattern(
    pattern: { s: string; p: string; o: string },
    bindings: Bindings
  ): Triple | null {
    const s = this.resolve(pattern.s, bindings);
    const p = this.resolve(pattern.p, bindings);
    const o = this.resolve(pattern.o, bindings);

    if (!s || !p || !o) return null;

    return { subject: s, predicate: p, object: o };
  }

  /**
   * 変数を解決
   */
  private resolve(term: string, bindings: Bindings): string | null {
    if (term.startsWith('?')) {
      const varName = term.substring(1);
      return bindings[varName] ?? null;
    }
    return term;
  }

  /**
   * アトムをパターンに変換
   */
  private atomToPattern(atom: DatalogAtom): { s: string; p: string; o: string } {
    const args = atom.args.map((a) => this.termToString(a));
    return {
      s: args[0] || '',
      p: atom.predicate,
      o: args[1] || '',
    };
  }

  /**
   * 項を文字列に変換
   */
  private termToString(term: DatalogTerm): string {
    switch (term.type) {
      case 'variable':
        return `?${term.name}`;
      case 'constant':
        return term.value;
      case 'literal':
        return term.datatype ? `"${term.value}"^^${term.datatype}` : `"${term.value}"`;
    }
  }

  /**
   * アトムを具体化
   */
  private instantiateAtom(atom: DatalogAtom, bindings: Bindings): Triple | null {
    const args = atom.args.map((a) => {
      if (a.type === 'variable') {
        return bindings[a.name] ?? null;
      }
      return this.termToString(a);
    });

    if (args.some((a) => a === null)) return null;

    return {
      subject: args[0]!,
      predicate: atom.predicate,
      object: args[1]!,
    };
  }

  /**
   * トリプルのキーを生成
   */
  private tripleKey(triple: Triple): string {
    return `${triple.subject}|${triple.predicate}|${triple.object}`;
  }

  /**
   * ルールを追加
   */
  addRule(rule: DatalogRule): void {
    this.customRules.set(rule.id, rule);
  }

  /**
   * ルールを削除
   */
  removeRule(ruleId: string): boolean {
    return this.customRules.delete(ruleId);
  }

  /**
   * ルール一覧を取得
   */
  getRules(): DatalogRule[] {
    return Array.from(this.customRules.values());
  }

  /**
   * OWL 2 RLルール一覧を取得
   */
  getOWL2RLRules(): OWL2RLRule[] {
    return Array.from(this.rules.values());
  }

  /**
   * ルールを有効化
   */
  enableRule(ruleId: OWL2RLRuleType): void {
    const rule = this.rules.get(ruleId);
    if (rule) {
      rule.enabled = true;
    }
  }

  /**
   * ルールを無効化
   */
  disableRule(ruleId: OWL2RLRuleType): void {
    const rule = this.rules.get(ruleId);
    if (rule) {
      rule.enabled = false;
    }
  }

  /**
   * 統計をリセット
   */
  resetStats(): void {
    this.stats = this.createEmptyStats();
  }

  /**
   * 現在の統計を取得
   */
  getStats(): InferenceStats {
    return { ...this.stats };
  }
}
