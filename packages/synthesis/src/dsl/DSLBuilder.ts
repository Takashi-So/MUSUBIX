/**
 * DSL Builder
 * @module @nahisaho/musubix-synthesis
 * @description Declarative DSL definition builder
 * Traces to: REQ-SYN-001 (DSL Definition Framework)
 */

import type {
  Constant,
  DSLConfig,
  Operator,
  TypeDefinition,
} from '../types.js';

/**
 * DSL Builder implementation
 */
export class DSLBuilder {
  private readonly typeList: TypeDefinition[];
  private readonly operatorList: Operator[];
  private readonly constantList: Constant[];

  constructor() {
    this.typeList = [];
    this.operatorList = [];
    this.constantList = [];
  }

  /**
   * Add a type to the DSL
   */
  type(name: string, def: TypeDefinition): DSLBuilder {
    this.typeList.push({ ...def, name });
    return this;
  }

  /**
   * Add an operator to the DSL
   */
  operator(name: string, op: Operator): DSLBuilder {
    this.operatorList.push({ ...op, name });
    return this;
  }

  /**
   * Add a constant to the DSL
   */
  constant(name: string, c: Constant): DSLBuilder {
    this.constantList.push({ ...c, name });
    return this;
  }

  /**
   * Build the DSL config
   */
  build(): DSLConfig {
    return {
      types: [...this.typeList],
      operators: [...this.operatorList],
      constants: [...this.constantList],
    };
  }
}
