/**
 * Precondition Verifier
 * 
 * 事前条件の形式検証を行うクラス
 */

import type { Z3Client, Z3Result } from '../z3/types.js';
import type {
  PreconditionInput,
  VerificationResult,
  VerificationStatus,
  VariableDeclaration,
  Condition,
} from './types.js';

/**
 * 事前条件検証器
 * 
 * Z3ソルバーを使用して事前条件の充足可能性と妥当性を検証します。
 * 
 * @example
 * ```typescript
 * const z3 = await Z3Adapter.create();
 * const verifier = new PreconditionVerifier(z3);
 * 
 * const result = await verifier.verify({
 *   condition: { expression: 'amount > 0', format: 'javascript' },
 *   variables: [{ name: 'amount', type: 'Int' }],
 * });
 * 
 * if (result.status === 'valid') {
 *   console.log('Precondition is satisfiable');
 * }
 * ```
 */
export class PreconditionVerifier {
  private readonly z3: Z3Client;

  constructor(z3Client: Z3Client) {
    this.z3 = z3Client;
  }

  /**
   * 事前条件を検証
   * 
   * @param input - 検証入力
   * @returns 検証結果
   */
  async verify(input: PreconditionInput): Promise<VerificationResult> {
    const startTime = Date.now();

    try {
      // SMT-LIB2スクリプトを生成
      const smtScript = this.buildSmtScript(input);

      if (input.options?.verbose) {
        console.log('[PreconditionVerifier] SMT Script:', smtScript);
      }

      // Z3で検証
      const result = await this.z3.checkSat(smtScript);
      const duration = Date.now() - startTime;

      return this.buildResult(input.condition, result, duration, input, smtScript);
    } catch (error) {
      const duration = Date.now() - startTime;
      return {
        status: 'error',
        condition: input.condition,
        duration,
        errorMessage: error instanceof Error ? error.message : String(error),
      };
    }
  }

  /**
   * 事前条件の充足可能性をチェック
   * 
   * 事前条件を満たす入力が存在するかを確認
   */
  async checkSatisfiability(input: PreconditionInput): Promise<boolean> {
    const result = await this.verify(input);
    return result.status === 'valid';
  }

  /**
   * 事前条件の妥当性をチェック
   * 
   * 事前条件が常に真であるかを確認（否定がunsatなら常に真）
   */
  async checkValidity(input: PreconditionInput): Promise<boolean> {
    try {
      // 否定を追加したスクリプトを生成
      const smtScript = this.buildValidityScript(input);

      if (input.options?.verbose) {
        console.log('[PreconditionVerifier] Validity Script:', smtScript);
      }

      const result = await this.z3.checkSat(smtScript);
      
      // unsatなら妥当（常に真）
      return result === 'unsat';
    } catch {
      return false;
    }
  }

  /**
   * SMT-LIB2スクリプトを構築
   */
  private buildSmtScript(input: PreconditionInput): string {
    const lines: string[] = [];

    // ロジック設定
    lines.push('(set-logic ALL)');

    // 変数宣言
    for (const variable of input.variables) {
      lines.push(this.declareVariable(variable));
    }

    // コンテキスト条件
    if (input.context) {
      for (const ctx of input.context) {
        const smtExpr = this.conditionToSmt(ctx);
        lines.push(`(assert ${smtExpr})`);
      }
    }

    // 事前条件
    const precondSmt = this.conditionToSmt(input.condition);
    lines.push(`(assert ${precondSmt})`);

    return lines.join('\n');
  }

  /**
   * 妥当性検証用のSMT-LIB2スクリプトを構築
   */
  private buildValidityScript(input: PreconditionInput): string {
    const lines: string[] = [];

    lines.push('(set-logic ALL)');

    for (const variable of input.variables) {
      lines.push(this.declareVariable(variable));
    }

    if (input.context) {
      for (const ctx of input.context) {
        const smtExpr = this.conditionToSmt(ctx);
        lines.push(`(assert ${smtExpr})`);
      }
    }

    // 事前条件の否定をアサート
    const precondSmt = this.conditionToSmt(input.condition);
    lines.push(`(assert (not ${precondSmt}))`);

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
        const elemType = variable.elementType ? this.typeToSmt({ name: '', type: variable.elementType }) : 'Int';
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

    // JavaScript/自然言語からSMTへの変換
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
    smt = smt.replace(/>=/g, '>=');
    smt = smt.replace(/<=/g, '<=');

    // 二項演算をS式に変換
    // 例: a > b → (> a b)
    smt = this.infixToPrefix(smt);

    return smt;
  }

  /**
   * 中置記法を前置記法（S式）に変換
   */
  private infixToPrefix(expr: string): string {
    const trimmed = expr.trim();

    // 括弧で囲まれている場合は中身を処理
    if (trimmed.startsWith('(') && trimmed.endsWith(')')) {
      // 対応する括弧かチェック
      let depth = 0;
      let isMatching = true;
      for (let i = 0; i < trimmed.length - 1; i++) {
        if (trimmed[i] === '(') depth++;
        if (trimmed[i] === ')') depth--;
        if (depth === 0) {
          isMatching = false;
          break;
        }
      }
      if (isMatching) {
        return trimmed; // すでにS式
      }
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
      const parts = trimmed.split(new RegExp(`\\s*${op.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*`));
      if (parts.length === 2) {
        return `(${op} ${parts[0].trim()} ${parts[1].trim()})`;
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
   * 検証結果を構築
   */
  private buildResult(
    condition: Condition,
    z3Result: Z3Result,
    duration: number,
    input: PreconditionInput,
    smtScript: string
  ): VerificationResult {
    const status = this.mapZ3ResultToStatus(z3Result);

    const result: VerificationResult = {
      status,
      condition,
      duration,
      details: {
        smtScript,
        z3Result,
      },
    };

    // 反例の取得（invalidの場合）
    if (status === 'invalid' && input.options?.generateCounterexample) {
      // Note: 実際の反例取得はgetModelを使用
      result.counterexample = {
        assignments: {},
        explanation: 'Counterexample generation requires sat result',
      };
    }

    return result;
  }

  /**
   * Z3結果を検証ステータスにマッピング
   */
  private mapZ3ResultToStatus(z3Result: Z3Result): VerificationStatus {
    switch (z3Result) {
      case 'sat':
        return 'valid'; // 事前条件は充足可能（妥当）
      case 'unsat':
        return 'invalid'; // 事前条件は充足不可能
      case 'unknown':
        return 'unknown';
      case 'error':
        return 'error';
      default:
        return 'unknown';
    }
  }
}
