/**
 * Type declarations for z3-solver module
 * This is an optional dependency - runtime import will catch if not available
 */

declare module 'z3-solver' {
  export interface Z3Instance {
    Context: (name?: string) => Z3Context;
    check_sat: () => string;
    model: () => Map<string, string>;
  }

  export interface Z3Context {
    Int: {
      const: (name: string) => Z3Expr;
      val: (value: number) => Z3Expr;
    };
    Real: {
      const: (name: string) => Z3Expr;
      val: (value: number) => Z3Expr;
    };
    Bool: {
      const: (name: string) => Z3Expr;
      val: (value: boolean) => Z3Expr;
    };
    And: (...args: Z3Expr[]) => Z3Expr;
    Or: (...args: Z3Expr[]) => Z3Expr;
    Not: (expr: Z3Expr) => Z3Expr;
    Implies: (a: Z3Expr, b: Z3Expr) => Z3Expr;
    Solver: () => Z3Solver;
  }

  export interface Z3Expr {
    eq: (other: Z3Expr) => Z3Expr;
    neq: (other: Z3Expr) => Z3Expr;
    lt: (other: Z3Expr) => Z3Expr;
    le: (other: Z3Expr) => Z3Expr;
    gt: (other: Z3Expr) => Z3Expr;
    ge: (other: Z3Expr) => Z3Expr;
    add: (other: Z3Expr) => Z3Expr;
    sub: (other: Z3Expr) => Z3Expr;
    mul: (other: Z3Expr) => Z3Expr;
    div: (other: Z3Expr) => Z3Expr;
    neg: () => Z3Expr;
  }

  export interface Z3Solver {
    add: (expr: Z3Expr) => void;
    check: () => Promise<'sat' | 'unsat' | 'unknown'>;
    model: () => Z3Model;
    reset: () => void;
  }

  export interface Z3Model {
    get: (expr: Z3Expr) => string;
    entries: () => Array<[string, string]>;
  }

  export function init(): Promise<Z3Instance>;
}
