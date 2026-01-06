/**
 * Postcondition Verifier
 * 
 * 事後条件の形式検証を行うクラス
 */

import type { Z3Client, Z3Result } from '../z3/types.js';
import type {
  PostconditionInput,
  VerificationResult,
  VerificationStatus,
  VariableDeclaration,
  Condition,
} from './types.js';

/**
 * 事後条件検証器
 * 
 * Z3ソルバーを使用して、事前条件が成り立つときに
 * 事後条件が必ず成り立つかを検証します（Hoareトリプル）。
 * 
 * @example
 * ```typescript
 * const z3 = await Z3Adapter.create();
 * const verifier = new PostconditionVerifier(z3);
 * 
 * const result = await verifier.verify({
 *   precondition: { expression: 'balance >= amount', format: 'javascript' },
 *   postcondition: { expression: 'balance_new = balance - amount', format: 'javascript' },
 *   preVariables: [
 *     { name: 'balance', type: 'Int' },
 *     { name: 'amount', type: 'Int' },
 *   ],
 *   postVariables: [
 *     { name: 'balance_new', type: 'Int' },
 *   ],
 * });
 * ```
 */
export class PostconditionVerifier {
  private readonly z3: Z3Client;

  constructor(z3Client: Z3Client) {
    this.z3 = z3Client;
  }

  /**
   * 事後条件を検証
   * 
   * 事前条件 ∧ 遷移 → 事後条件 が常に成り立つかを検証
   * 
   * @param input - 検証入力
   * @returns 検証結果
   */
  async verify(input: PostconditionInput): Promise<VerificationResult> {
    const startTime = Date.now();

    try {
      // SMT-LIB2スクリプトを生成
      const smtScript = this.buildSmtScript(input);

      if (input.options?.verbose) {
        console.log('[PostconditionVerifier] SMT Script:', smtScript);
      }

      // Z3で検証
      // 「事前条件 ∧ 遷移 ∧ ¬事後条件」がunsatなら、事後条件は妥当
      const result = await this.z3.checkSat(smtScript);
      const duration = Date.now() - startTime;

      return this.buildResult(input, result, duration, smtScript);
    } catch (error) {
      const duration = Date.now() - startTime;
      return {
        status: 'error',
        condition: input.postcondition,
        duration,
        errorMessage: error instanceof Error ? error.message : String(error),
      };
    }
  }

  /**
   * 事後条件の部分的正当性をチェック
   * 
   * 事前条件が成り立つとき、プログラムが停止すれば事後条件が成り立つ
   */
  async checkPartialCorrectness(input: PostconditionInput): Promise<boolean> {
    const result = await this.verify(input);
    return result.status === 'valid';
  }

  /**
   * 最弱事前条件を計算
   * 
   * 事後条件が成り立つための最弱の事前条件を計算
   */
  async computeWeakestPrecondition(
    postcondition: Condition,
    transition: string,
    _variables: VariableDeclaration[]
  ): Promise<string | null> {
    // Note: 完全な最弱事前条件計算は複雑
    // 基本的な置換ベースの近似を提供

    try {
      const postSmt = this.conditionToSmt(postcondition);
      
      // 遷移関係で変数を置換
      // 例: balance_new → balance - amount
      let wp = postSmt;
      
      // 遷移式をパース
      const assignments = this.parseTransition(transition);
      
      // 後ろから置換
      for (const [varName, expr] of Object.entries(assignments)) {
        wp = wp.replace(new RegExp(`\\b${varName}\\b`, 'g'), `(${expr})`);
      }

      return wp;
    } catch {
      return null;
    }
  }

  /**
   * SMT-LIB2スクリプトを構築
   * 
   * 「事前条件 ∧ 遷移 ∧ ¬事後条件」の充足可能性をチェック
   * unsatなら事後条件は妥当
   */
  private buildSmtScript(input: PostconditionInput): string {
    const lines: string[] = [];

    lines.push('(set-logic ALL)');

    // 事前状態の変数宣言
    for (const variable of input.preVariables) {
      lines.push(this.declareVariable(variable));
    }

    // 事後状態の変数宣言
    for (const variable of input.postVariables) {
      // 重複を避ける
      const preVar = input.preVariables.find(v => v.name === variable.name);
      if (!preVar) {
        lines.push(this.declareVariable(variable));
      }
    }

    // 事前条件をアサート
    const preSmt = this.conditionToSmt(input.precondition);
    lines.push(`(assert ${preSmt})`);

    // 遷移関係をアサート（存在する場合）
    if (input.transition) {
      const transitionSmt = this.parseAndConvertTransition(input.transition);
      lines.push(`(assert ${transitionSmt})`);
    }

    // 事後条件の否定をアサート
    const postSmt = this.conditionToSmt(input.postcondition);
    lines.push(`(assert (not ${postSmt}))`);

    return lines.join('\n');
  }

  /**
   * 変数をSMT-LIB2形式で宣言
   */
  private declareVariable(variable: VariableDeclaration): string {
    const smtType = this.typeToSmt(variable);
    return `(declare-const ${variable.name} ${smtType})`;
  }

  /**
   * 型をSMT-LIB2形式に変換
   */
  private typeToSmt(variable: VariableDeclaration): string {
    switch (variable.type) {
      case 'Int':
        return 'Int';
      case 'Real':
        return 'Real';
      case 'Bool':
        return 'Bool';
      case 'String':
        return 'String';
      case 'Array':
        const elemType = variable.elementType
          ? this.typeToSmt({ name: '', type: variable.elementType })
          : 'Int';
        return `(Array Int ${elemType})`;
      case 'BitVec':
        return `(_ BitVec ${variable.bitWidth ?? 32})`;
      default:
        return 'Int';
    }
  }

  /**
   * 条件式をSMT-LIB2形式に変換
   */
  private conditionToSmt(condition: Condition): string {
    if (condition.format === 'smt') {
      return condition.expression;
    }
    return this.convertToSmt(condition.expression);
  }

  /**
   * JavaScript式をSMT-LIB2に変換
   */
  private convertToSmt(expr: string): string {
    let smt = expr;

    // 基本的な演算子変換
    smt = smt.replace(/&&/g, ' and ');
    smt = smt.replace(/\|\|/g, ' or ');
    smt = smt.replace(/!/g, ' not ');
    smt = smt.replace(/==/g, '=');
    smt = smt.replace(/!=/g, ' distinct ');

    // 中置記法を前置記法に変換
    smt = this.infixToPrefix(smt);

    return smt;
  }

  /**
   * 遷移関係をパースしてSMT形式に変換
   */
  private parseAndConvertTransition(transition: string): string {
    const assignments = this.parseTransition(transition);
    const conditions: string[] = [];

    for (const [varName, expr] of Object.entries(assignments)) {
      const exprSmt = this.infixToPrefix(expr);
      conditions.push(`(= ${varName} ${exprSmt})`);
    }

    if (conditions.length === 0) {
      return 'true';
    }
    if (conditions.length === 1) {
      return conditions[0];
    }
    return `(and ${conditions.join(' ')})`;
  }

  /**
   * 遷移式をパース
   * 例: "balance_new := balance - amount; count_new := count + 1"
   */
  private parseTransition(transition: string): Record<string, string> {
    const assignments: Record<string, string> = {};
    const parts = transition.split(/[;,]/);

    for (const part of parts) {
      // := または = で分割
      const match = part.match(/^\s*(\w+)\s*:?=\s*(.+)\s*$/);
      if (match) {
        const [, varName, expr] = match;
        assignments[varName] = expr.trim();
      }
    }

    return assignments;
  }

  /**
   * 中置記法を前置記法（S式）に変換
   */
  private infixToPrefix(expr: string): string {
    const trimmed = expr.trim();

    // すでにS式の場合はそのまま返す
    if (trimmed.startsWith('(') && this.isBalancedSExpr(trimmed)) {
      return trimmed;
    }

    // and/or/not の処理
    const andMatch = trimmed.match(/^(.+?)\s+and\s+(.+)$/i);
    if (andMatch) {
      return `(and ${this.infixToPrefix(andMatch[1])} ${this.infixToPrefix(andMatch[2])})`;
    }

    const orMatch = trimmed.match(/^(.+?)\s+or\s+(.+)$/i);
    if (orMatch) {
      return `(or ${this.infixToPrefix(orMatch[1])} ${this.infixToPrefix(orMatch[2])})`;
    }

    const notMatch = trimmed.match(/^\s*not\s+(.+)$/i);
    if (notMatch) {
      return `(not ${this.infixToPrefix(notMatch[1])})`;
    }

    // 比較演算子の処理
    const operators = ['>=', '<=', '>', '<', '=', 'distinct'];
    for (const op of operators) {
      const regex = new RegExp(`^(.+?)\\s*${op.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*(.+)$`);
      const match = trimmed.match(regex);
      if (match) {
        return `(${op} ${this.infixToPrefix(match[1])} ${this.infixToPrefix(match[2])})`;
      }
    }

    // 算術演算子の処理
    const arithmeticOps = ['+', '-', '*', '/'];
    for (const op of arithmeticOps) {
      const parts = trimmed.split(new RegExp(`\\s*\\${op}\\s*`));
      if (parts.length === 2) {
        return `(${op} ${this.infixToPrefix(parts[0])} ${this.infixToPrefix(parts[1])})`;
      }
    }

    return trimmed;
  }

  /**
   * S式がバランスしているかチェック
   */
  private isBalancedSExpr(expr: string): boolean {
    let depth = 0;
    for (const char of expr) {
      if (char === '(') depth++;
      if (char === ')') depth--;
      if (depth < 0) return false;
    }
    return depth === 0;
  }

  /**
   * 検証結果を構築
   */
  private buildResult(
    input: PostconditionInput,
    z3Result: Z3Result,
    duration: number,
    smtScript: string
  ): VerificationResult {
    // unsatなら事後条件は妥当（valid）
    // satなら反例が存在（invalid）
    const status = this.mapZ3ResultToStatus(z3Result);

    const result: VerificationResult = {
      status,
      condition: input.postcondition,
      duration,
      details: {
        smtScript,
        z3Result,
        precondition: input.precondition.expression,
        transition: input.transition,
      },
    };

    // 反例の取得（invalidの場合）
    if (status === 'invalid' && input.options?.generateCounterexample) {
      result.counterexample = {
        assignments: {},
        explanation: 'Found an input that satisfies precondition but violates postcondition',
      };
    }

    return result;
  }

  /**
   * Z3結果を検証ステータスにマッピング
   */
  private mapZ3ResultToStatus(z3Result: Z3Result): VerificationStatus {
    switch (z3Result) {
      case 'unsat':
        return 'valid'; // 事後条件は常に成り立つ
      case 'sat':
        return 'invalid'; // 反例が存在
      case 'unknown':
        return 'unknown';
      case 'error':
        return 'error';
      default:
        return 'unknown';
    }
  }
}
