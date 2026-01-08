/**
 * ExplanationGenerator - Program Synthesis Explanation
 *
 * 合成されたプログラムの自然言語説明を生成する。
 *
 * @see TSK-SY-106 - ExplanationGenerator実装
 * @see REQ-SY-106 - 説明生成要件
 * @module @nahisaho/musubix-synthesis
 */

/**
 * 入出力例
 */
export interface Example {
  input: unknown;
  output: unknown;
}

/**
 * 合成されたプログラム
 */
export interface SynthesizedProgram {
  /** プログラムID */
  id: string;
  /** 合成されたコード */
  code: string;
  /** 対象ドメイン */
  domain: string;
  /** 入出力例 */
  examples: Example[];
  /** 合成信頼度 */
  confidence: number;
}

/**
 * 説明
 */
export interface Explanation {
  /** 説明文 */
  description: string;
  /** 対象ドメイン */
  domain: string;
  /** ステップ */
  steps: string[];
  /** 例のウォークスルー */
  exampleWalkthrough: ExampleWalkthrough[];
  /** 信頼度 */
  confidence: number;
}

/**
 * 例のウォークスルー
 */
export interface ExampleWalkthrough {
  input: string;
  output: string;
  trace: string;
}

/**
 * 詳細説明
 */
export interface DetailedExplanation extends Explanation {
  /** 根拠 */
  rationale: string;
  /** 制限事項 */
  limitations: string[];
  /** 入出力関係 */
  relationship: string;
}

/**
 * 説明生成器インターフェース
 */
export interface ExplanationGenerator {
  /**
   * プログラムの説明を生成
   */
  generate(program: SynthesizedProgram): Explanation;

  /**
   * 説明の信頼度を取得
   */
  getConfidence(program: SynthesizedProgram): number;

  /**
   * 詳細説明を生成
   */
  explain(program: SynthesizedProgram): DetailedExplanation;

  /**
   * 一行サマリーを生成
   */
  summarize(program: SynthesizedProgram): string;
}

/**
 * 操作パターンの定義
 */
const operationPatterns: Record<string, { pattern: RegExp; description: string }> = {
  toUpperCase: { pattern: /\.toUpperCase\(\)/, description: 'converts text to uppercase' },
  toLowerCase: { pattern: /\.toLowerCase\(\)/, description: 'converts text to lowercase' },
  trim: { pattern: /\.trim\(\)/, description: 'removes leading and trailing whitespace' },
  split: { pattern: /\.split\([^)]+\)/, description: 'splits text into parts' },
  join: { pattern: /\.join\([^)]+\)/, description: 'joins parts into text' },
  map: { pattern: /\.map\([^)]+\)/, description: 'transforms each element' },
  filter: { pattern: /\.filter\([^)]+\)/, description: 'filters elements based on condition' },
  reduce: { pattern: /\.reduce\([^)]+\)/, description: 'combines elements into a single value' },
  reverse: { pattern: /\.reverse\(\)/, description: 'reverses the order of elements' },
  length: { pattern: /\.length/, description: 'gets the length' },
  charAt: { pattern: /\.charAt\(\d+\)/, description: 'extracts a character at position' },
  repeat: { pattern: /\.repeat\(\d+\)/, description: 'repeats the input' },
  flat: { pattern: /\.flat\(\)/, description: 'flattens nested arrays' },
  multiply: { pattern: /\*\s*\d+/, description: 'multiplies by a number' },
  add: { pattern: /\+\s*\d+/, description: 'adds a number' },
  subtract: { pattern: /-\s*\d+/, description: 'subtracts a number' },
};

/**
 * デフォルト説明生成器
 */
class DefaultExplanationGenerator implements ExplanationGenerator {
  /**
   * プログラムの説明を生成
   */
  generate(program: SynthesizedProgram): Explanation {
    const steps = this.extractSteps(program.code);
    const description = this.generateDescription(program, steps);
    const exampleWalkthrough = this.generateWalkthrough(program);
    const confidence = this.calculateExplanationConfidence(program, steps);

    return {
      description,
      domain: program.domain,
      steps,
      exampleWalkthrough,
      confidence,
    };
  }

  /**
   * 説明の信頼度を取得
   */
  getConfidence(program: SynthesizedProgram): number {
    // 基礎信頼度
    let confidence = program.confidence;

    // コードの複雑さによる調整
    const complexity = this.measureComplexity(program.code);
    if (complexity > 3) {
      confidence *= 0.8;
    }

    // 例の数による調整
    const exampleBonus = Math.min(program.examples.length * 0.05, 0.2);
    confidence = Math.min(confidence + exampleBonus, 1.0);

    return Math.round(confidence * 100) / 100;
  }

  /**
   * 詳細説明を生成
   */
  explain(program: SynthesizedProgram): DetailedExplanation {
    const baseExplanation = this.generate(program);
    const relationship = this.identifyRelationship(program);
    const rationale = this.generateRationale(program);
    const limitations = this.identifyLimitations(program);

    return {
      ...baseExplanation,
      rationale,
      limitations,
      relationship,
    };
  }

  /**
   * 一行サマリーを生成
   */
  summarize(program: SynthesizedProgram): string {
    const steps = this.extractSteps(program.code);
    
    if (steps.length === 0) {
      return `Transforms ${program.domain} input to output`;
    }

    if (steps.length === 1) {
      return this.toHumanReadable(steps[0]);
    }

    // 複数ステップの場合は主要な操作を抽出
    const mainOps = steps.slice(0, 2);
    const summary = mainOps.map(s => this.toHumanReadable(s)).join(', then ');
    
    if (summary.length > 90) {
      return summary.substring(0, 87) + '...';
    }
    
    return summary;
  }

  /**
   * コードからステップを抽出
   */
  private extractSteps(code: string): string[] {
    const steps: string[] = [];

    for (const [name, { pattern }] of Object.entries(operationPatterns)) {
      if (pattern.test(code)) {
        steps.push(name);
      }
    }

    // チェーンの順序を維持するために正規化
    return steps;
  }

  /**
   * 説明文を生成
   */
  private generateDescription(program: SynthesizedProgram, steps: string[]): string {
    if (steps.length === 0) {
      return `This program transforms a ${program.domain} input according to the specified pattern.`;
    }

    const operations = steps.map(s => operationPatterns[s]?.description || s).join(', then ');
    return `This program ${operations}.`;
  }

  /**
   * 例のウォークスルーを生成
   */
  private generateWalkthrough(program: SynthesizedProgram): ExampleWalkthrough[] {
    return program.examples.map((ex) => ({
      input: JSON.stringify(ex.input),
      output: JSON.stringify(ex.output),
      trace: `Input ${JSON.stringify(ex.input)} → Apply transformation → Output ${JSON.stringify(ex.output)}`,
    }));
  }

  /**
   * 説明の信頼度を計算
   */
  private calculateExplanationConfidence(program: SynthesizedProgram, steps: string[]): number {
    let confidence = 0.5;

    // 認識されたステップが多いほど信頼度UP
    confidence += Math.min(steps.length * 0.1, 0.3);

    // 例が多いほど信頼度UP
    confidence += Math.min(program.examples.length * 0.05, 0.15);

    // プログラム自体の信頼度を反映
    confidence = confidence * 0.5 + program.confidence * 0.5;

    return Math.round(confidence * 100) / 100;
  }

  /**
   * コードの複雑さを計測
   */
  private measureComplexity(code: string): number {
    let complexity = 1;
    
    // メソッドチェーンの数
    const chainCount = (code.match(/\./g) || []).length;
    complexity += chainCount * 0.5;

    // コールバック関数の数
    const callbackCount = (code.match(/=>/g) || []).length;
    complexity += callbackCount * 0.8;

    // ネストの深さ（括弧の数）
    const parenDepth = Math.max((code.match(/\(/g) || []).length - 1, 0);
    complexity += parenDepth * 0.3;

    return complexity;
  }

  /**
   * 入出力関係を識別
   */
  private identifyRelationship(program: SynthesizedProgram): string {
    if (program.examples.length === 0) {
      return 'Unable to determine relationship without examples';
    }

    const { examples } = program;
    const inputType = typeof examples[0].input;
    const outputType = typeof examples[0].output;

    if (inputType === outputType) {
      return `Transforms ${inputType} to ${outputType} while preserving type`;
    }

    return `Converts ${inputType} to ${outputType}`;
  }

  /**
   * 根拠を生成
   */
  private generateRationale(program: SynthesizedProgram): string {
    const steps = this.extractSteps(program.code);
    
    if (steps.length === 0) {
      return 'The transformation pattern was inferred from the provided examples.';
    }

    return `The program uses ${steps.join(', ')} operations to achieve the transformation shown in the examples.`;
  }

  /**
   * 制限事項を識別
   */
  private identifyLimitations(program: SynthesizedProgram): string[] {
    const limitations: string[] = [];

    if (program.examples.length < 3) {
      limitations.push('Limited examples may not cover all edge cases');
    }

    if (program.confidence < 0.7) {
      limitations.push('Low confidence suggests uncertain generalization');
    }

    const complexity = this.measureComplexity(program.code);
    if (complexity > 4) {
      limitations.push('Complex transformation may have unexpected behavior');
    }

    return limitations;
  }

  /**
   * 操作名を人間可読な形式に変換
   */
  private toHumanReadable(step: string): string {
    const descriptions: Record<string, string> = {
      toUpperCase: 'Converts to uppercase',
      toLowerCase: 'Converts to lowercase',
      trim: 'Removes whitespace',
      split: 'Splits into parts',
      join: 'Joins parts together',
      map: 'Transforms each element',
      filter: 'Filters elements',
      reduce: 'Combines elements',
      reverse: 'Reverses order',
      length: 'Gets the length',
      charAt: 'Extracts a character',
      repeat: 'Repeats the input',
      flat: 'Flattens the array',
      multiply: 'Multiplies the value',
      add: 'Adds to the value',
      subtract: 'Subtracts from the value',
    };

    return descriptions[step] || `Applies ${step} operation`;
  }
}

/**
 * ExplanationGenerator を作成
 */
export function createExplanationGenerator(): ExplanationGenerator {
  return new DefaultExplanationGenerator();
}
