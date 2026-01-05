/**
 * Datalog Engine
 *
 * @module learning/inference/datalog-engine
 * @description Datalogルール処理エンジン
 * @requirements REQ-ONTO-014
 */

import type {
  Triple,
  DatalogRule,
  DatalogAtom,
  DatalogTerm,
  Bindings,
  InferenceResult,
  AppliedRule,
  InferenceStats,
  InferenceProgress,
  ReasonerOptions,
} from './types.js';

/**
 * Datalogプログラム（ルールの集合）
 */
export interface DatalogProgram {
  /** プログラムID */
  id: string;
  /** プログラム名 */
  name: string;
  /** ルール一覧 */
  rules: DatalogRule[];
  /** 名前空間 */
  namespaces: Record<string, string>;
}

/**
 * ストラティファイド評価のための層
 */
interface Stratum {
  /** 層番号 */
  level: number;
  /** この層のルール */
  rules: DatalogRule[];
}

/**
 * Datalog Engine
 * REQ-ONTO-014: Datalogルール統合
 */
export class DatalogEngine {
  private rules: Map<string, DatalogRule> = new Map();
  private facts: Map<string, Triple> = new Map();
  private namespaces: Map<string, string> = new Map();
  private stats: InferenceStats;

  constructor() {
    this.stats = this.createEmptyStats();
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
   * ルールを追加
   */
  addRule(rule: DatalogRule): void {
    this.rules.set(rule.id, rule);
  }

  /**
   * 複数ルールを追加
   */
  addRules(rules: DatalogRule[]): void {
    for (const rule of rules) {
      this.addRule(rule);
    }
  }

  /**
   * ルールを削除
   */
  removeRule(ruleId: string): boolean {
    return this.rules.delete(ruleId);
  }

  /**
   * ルール一覧を取得
   */
  getRules(): DatalogRule[] {
    return Array.from(this.rules.values());
  }

  /**
   * ファクトを追加
   */
  addFact(triple: Triple): void {
    const key = this.tripleKey(triple);
    this.facts.set(key, triple);
  }

  /**
   * 複数ファクトを追加
   */
  addFacts(triples: Triple[]): void {
    for (const triple of triples) {
      this.addFact(triple);
    }
  }

  /**
   * ファクトをクリア
   */
  clearFacts(): void {
    this.facts.clear();
  }

  /**
   * 名前空間を設定
   */
  setNamespace(prefix: string, uri: string): void {
    this.namespaces.set(prefix, uri);
  }

  /**
   * プログラムをロード
   */
  loadProgram(program: DatalogProgram): void {
    // 名前空間をロード
    for (const [prefix, uri] of Object.entries(program.namespaces)) {
      this.setNamespace(prefix, uri);
    }

    // ルールをロード
    this.addRules(program.rules);
  }

  /**
   * Datalog形式の文字列からルールをパース
   */
  parseRule(ruleString: string): DatalogRule | null {
    // 形式: head :- body1, body2, ...
    const match = ruleString.match(/^(.+?)\s*:-\s*(.+)\.?\s*$/);
    if (!match) return null;

    const headStr = match[1].trim();
    const bodyStr = match[2].trim();

    const head = this.parseAtom(headStr);
    if (!head) return null;

    const bodyParts = this.splitAtoms(bodyStr);
    const body = bodyParts.map((b) => this.parseAtom(b)).filter((b): b is DatalogAtom => b !== null);

    if (body.length !== bodyParts.length) return null;

    return {
      id: `rule-${Date.now()}-${Math.random().toString(36).substring(7)}`,
      name: `Parsed Rule: ${headStr}`,
      head,
      body,
      priority: 50,
      enabled: true,
    };
  }

  /**
   * アトムをパース
   */
  private parseAtom(atomStr: string): DatalogAtom | null {
    // 形式: predicate(arg1, arg2, ...)
    const match = atomStr.match(/^(not\s+)?(\w+)\((.+)\)$/);
    if (!match) return null;

    const negated = !!match[1];
    const predicate = this.expandPrefix(match[2]);
    const argsStr = match[3];

    const args = argsStr.split(',').map((a) => this.parseTerm(a.trim()));

    return {
      predicate,
      args,
      negated,
    };
  }

  /**
   * 項をパース
   */
  private parseTerm(termStr: string): DatalogTerm {
    // 変数: ?name または Name (大文字始まり)
    if (termStr.startsWith('?') || /^[A-Z]/.test(termStr)) {
      return {
        type: 'variable',
        name: termStr.startsWith('?') ? termStr.substring(1) : termStr,
      };
    }

    // リテラル: "value" または "value"^^datatype
    const literalMatch = termStr.match(/^"(.+?)"(?:\^\^(.+))?$/);
    if (literalMatch) {
      return {
        type: 'literal',
        value: literalMatch[1],
        datatype: literalMatch[2],
      };
    }

    // 定数
    return {
      type: 'constant',
      value: this.expandPrefix(termStr),
    };
  }

  /**
   * プレフィックスを展開
   */
  private expandPrefix(term: string): string {
    const colonIndex = term.indexOf(':');
    if (colonIndex === -1) return term;

    const prefix = term.substring(0, colonIndex);
    const localPart = term.substring(colonIndex + 1);

    const uri = this.namespaces.get(prefix);
    if (uri) {
      return uri + localPart;
    }

    return term;
  }

  /**
   * アトム文字列を分割
   */
  private splitAtoms(str: string): string[] {
    const atoms: string[] = [];
    let current = '';
    let depth = 0;

    for (const char of str) {
      if (char === '(') depth++;
      if (char === ')') depth--;

      if (char === ',' && depth === 0) {
        atoms.push(current.trim());
        current = '';
      } else {
        current += char;
      }
    }

    if (current.trim()) {
      atoms.push(current.trim());
    }

    return atoms;
  }

  /**
   * 推論を実行
   */
  async evaluate(options: ReasonerOptions = {}): Promise<InferenceResult> {
    const startTime = Date.now();
    const maxIterations = options.maxIterations ?? 100;
    const timeout = options.timeout ?? 5000;

    // 統計を初期化
    this.stats = this.createEmptyStats();
    this.stats.inputTriples = this.facts.size;

    // ストラティファイド評価のための層を計算
    const strata = this.stratify();

    const appliedRules: AppliedRule[] = [];
    let totalInferred = 0;

    // 進捗レポート
    const reportProgress = (phase: InferenceProgress['phase'], message: string) => {
      if (options.onProgress) {
        const elapsed = Date.now() - startTime;
        options.onProgress({
          phase,
          totalTriples: this.facts.size,
          processedTriples: this.facts.size,
          inferredTriples: totalInferred,
          elapsedMs: elapsed,
          estimatedRemainingMs: this.stats.iterations > 0 
            ? (elapsed / this.stats.iterations) * (maxIterations - this.stats.iterations)
            : 0,
          message,
        });
      }
    };

    reportProgress('initializing', 'Starting Datalog evaluation...');

    // 各層を順番に評価
    for (const stratum of strata) {
      reportProgress('reasoning', `Evaluating stratum ${stratum.level}`);

      let stratumIteration = 0;
      let fixedPoint = false;

      while (!fixedPoint && stratumIteration < maxIterations) {
        const elapsed = Date.now() - startTime;
        if (elapsed > timeout) break;

        stratumIteration++;
        this.stats.iterations++;

        const newTriples: Triple[] = [];

        // この層の各ルールを適用
        for (const rule of stratum.rules) {
          if (!rule.enabled) continue;

          const ruleResults = this.applyRule(rule);

          for (const result of ruleResults) {
            const key = this.tripleKey(result.triple);
            if (!this.facts.has(key)) {
              this.facts.set(key, result.triple);
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

        totalInferred += newTriples.length;
        this.stats.triplesInferred = totalInferred;

        if (newTriples.length === 0) {
          fixedPoint = true;
        }
      }
    }

    // 統計を更新
    this.stats.timeMs = Date.now() - startTime;
    this.stats.fixedPointReached = true;
    this.stats.outputTriples = this.facts.size;

    reportProgress('completed', `Evaluation completed: ${totalInferred} triples inferred`);

    return {
      inferredTriples: Array.from(this.facts.values()),
      appliedRules,
      stats: { ...this.stats },
    };
  }

  /**
   * ルールをストラティファイ
   */
  private stratify(): Stratum[] {
    // 簡易実装: 否定のあるルールを後の層に配置
    const positive: DatalogRule[] = [];
    const negated: DatalogRule[] = [];

    for (const rule of this.rules.values()) {
      if (rule.body.some((atom) => atom.negated)) {
        negated.push(rule);
      } else {
        positive.push(rule);
      }
    }

    const strata: Stratum[] = [];

    if (positive.length > 0) {
      strata.push({
        level: 0,
        rules: positive.sort((a, b) => b.priority - a.priority),
      });
    }

    if (negated.length > 0) {
      strata.push({
        level: 1,
        rules: negated.sort((a, b) => b.priority - a.priority),
      });
    }

    return strata;
  }

  /**
   * ルールを適用
   */
  private applyRule(rule: DatalogRule): Array<{ triple: Triple; bindings: Bindings }> {
    const results: Array<{ triple: Triple; bindings: Bindings }> = [];
    const facts = Array.from(this.facts.values());

    // ボディのバインディングを検索
    const allBindings = this.findBindings(rule.body, facts);

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
   * バインディングを検索
   */
  private findBindings(body: DatalogAtom[], facts: Triple[]): Bindings[] {
    if (body.length === 0) return [{}];

    let currentBindings: Bindings[] = [{}];

    for (const atom of body) {
      if (atom.negated) {
        // 否定: バインディングがマッチしない場合のみ残す
        currentBindings = currentBindings.filter((bindings) => {
          const matches = this.matchAtom(atom, facts, bindings);
          return matches.length === 0;
        });
      } else {
        // 肯定: マッチするバインディングを拡張
        const newBindings: Bindings[] = [];
        for (const bindings of currentBindings) {
          const matches = this.matchAtom(atom, facts, bindings);
          newBindings.push(...matches);
        }
        currentBindings = newBindings;
      }

      if (currentBindings.length === 0) break;
    }

    return currentBindings;
  }

  /**
   * アトムをマッチ
   */
  private matchAtom(atom: DatalogAtom, facts: Triple[], existingBindings: Bindings): Bindings[] {
    const results: Bindings[] = [];

    for (const fact of facts) {
      // 述語をマッチ
      if (atom.predicate !== fact.predicate) continue;

      // 引数をマッチ
      const bindings = this.matchArgs(atom.args, fact, existingBindings);
      if (bindings) {
        results.push(bindings);
      }
    }

    return results;
  }

  /**
   * 引数をマッチ
   */
  private matchArgs(args: DatalogTerm[], fact: Triple, existingBindings: Bindings): Bindings | null {
    if (args.length < 2) return null;

    const bindings = { ...existingBindings };
    const values = [fact.subject, fact.object];

    for (let i = 0; i < Math.min(args.length, values.length); i++) {
      const arg = args[i];
      const value = values[i];

      switch (arg.type) {
        case 'variable':
          if (arg.name in bindings) {
            if (bindings[arg.name] !== value) return null;
          } else {
            bindings[arg.name] = value;
          }
          break;

        case 'constant':
          if (arg.value !== value) return null;
          break;

        case 'literal':
          if (arg.value !== value) return null;
          break;
      }
    }

    return bindings;
  }

  /**
   * アトムを具体化
   */
  private instantiateAtom(atom: DatalogAtom, bindings: Bindings): Triple | null {
    const args = atom.args.map((arg) => {
      switch (arg.type) {
        case 'variable':
          return bindings[arg.name] ?? null;
        case 'constant':
          return arg.value;
        case 'literal':
          return arg.value;
      }
    });

    if (args.some((a) => a === null) || args.length < 2) return null;

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

  /**
   * クエリを実行
   */
  query(atom: DatalogAtom): Bindings[] {
    const facts = Array.from(this.facts.values());
    return this.matchAtom({ ...atom, negated: false }, facts, {});
  }
}
