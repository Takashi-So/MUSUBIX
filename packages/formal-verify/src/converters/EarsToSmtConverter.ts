/**
 * EARS to SMT Converter
 * 
 * EARS形式の要件をSMT-LIB2形式に変換するコンバーター
 */

import type {
  EarsPattern,
  EarsPatternType,
  SmtFormula,
  SmtDeclaration,
  ConversionResult,
  ConversionOptions,
} from './types.js';

/**
 * EARS→SMTコンバーター
 * 
 * EARS形式の自然言語要件をSMT-LIB2形式の論理式に変換します。
 * 5つのEARSパターンをサポート:
 * - Ubiquitous: THE [system] SHALL [requirement]
 * - Event-driven: WHEN [event], THE [system] SHALL [response]
 * - State-driven: WHILE [state], THE [system] SHALL [response]
 * - Unwanted: THE [system] SHALL NOT [behavior]
 * - Optional: IF [condition], THEN THE [system] SHALL [response]
 * 
 * @example
 * ```typescript
 * const converter = new EarsToSmtConverter();
 * 
 * const result = converter.convert(
 *   'WHEN user clicks submit, THE system SHALL save the data within 100ms'
 * );
 * 
 * if (result.success) {
 *   console.log(result.formula.smtLib2);
 * }
 * ```
 */
export class EarsToSmtConverter {
  private readonly options: ConversionOptions;

  constructor(options: ConversionOptions = {}) {
    this.options = {
      strict: options.strict ?? false,
      inferTypes: options.inferTypes ?? true,
      typeMapping: options.typeMapping ?? {},
      debug: options.debug ?? false,
    };
  }

  /**
   * EARS形式の要件をSMT-LIB2に変換
   * 
   * @param earsRequirement - EARS形式の要件文
   * @returns 変換結果
   */
  convert(earsRequirement: string): ConversionResult {
    const startTime = Date.now();
    const warnings: string[] = [];

    try {
      // 1. EARSパターンを解析
      const pattern = this.parseEarsPattern(earsRequirement);
      
      if (!pattern) {
        return {
          success: false,
          error: 'Failed to parse EARS pattern. Ensure the requirement follows EARS format.',
          warnings,
          duration: Date.now() - startTime,
        };
      }

      if (this.options.debug) {
        console.log('[EarsToSmtConverter] Parsed pattern:', pattern);
      }

      // 2. 変数を抽出
      const variables = this.extractVariables(pattern);
      
      // 3. SMT宣言を生成
      const declarations = this.generateDeclarations(variables);

      // 4. SMTアサーションを生成
      const assertions = this.generateAssertions(pattern, warnings);

      // 5. SMT-LIB2スクリプトを組み立て
      const smtLib2 = this.buildSmtLib2(declarations, assertions);

      const formula: SmtFormula = {
        smtLib2,
        declarations,
        assertions,
        metadata: {
          earsPattern: pattern,
          transformationRules: this.getAppliedRules(pattern.type),
          warnings,
        },
      };

      return {
        success: true,
        formula,
        warnings,
        duration: Date.now() - startTime,
      };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : String(error),
        warnings,
        duration: Date.now() - startTime,
      };
    }
  }

  /**
   * 複数のEARS要件をまとめて変換
   */
  convertMultiple(earsRequirements: string[]): ConversionResult[] {
    return earsRequirements.map(req => this.convert(req));
  }

  /**
   * EARSパターンを解析
   */
  parseEarsPattern(requirement: string): EarsPattern | null {
    const normalized = requirement.trim();

    // Pattern 1: Event-driven - WHEN [event], THE [system] SHALL [response]
    const eventDrivenMatch = normalized.match(
      /^WHEN\s+(.+?),?\s+THE\s+(.+?)\s+SHALL\s+(.+)$/i
    );
    if (eventDrivenMatch) {
      return {
        type: 'event-driven',
        original: normalized,
        event: eventDrivenMatch[1].trim(),
        system: eventDrivenMatch[2].trim(),
        requirement: eventDrivenMatch[3].trim(),
      };
    }

    // Pattern 2: State-driven - WHILE [state], THE [system] SHALL [response]
    const stateDrivenMatch = normalized.match(
      /^WHILE\s+(.+?),?\s+THE\s+(.+?)\s+SHALL\s+(.+)$/i
    );
    if (stateDrivenMatch) {
      return {
        type: 'state-driven',
        original: normalized,
        state: stateDrivenMatch[1].trim(),
        system: stateDrivenMatch[2].trim(),
        requirement: stateDrivenMatch[3].trim(),
      };
    }

    // Pattern 3: Optional - IF [condition], THEN THE [system] SHALL [response]
    const optionalMatch = normalized.match(
      /^IF\s+(.+?),?\s+THEN\s+THE\s+(.+?)\s+SHALL\s+(.+)$/i
    );
    if (optionalMatch) {
      return {
        type: 'optional',
        original: normalized,
        condition: optionalMatch[1].trim(),
        system: optionalMatch[2].trim(),
        requirement: optionalMatch[3].trim(),
      };
    }

    // Pattern 4: Unwanted - THE [system] SHALL NOT [behavior]
    const unwantedMatch = normalized.match(
      /^THE\s+(.+?)\s+SHALL\s+NOT\s+(.+)$/i
    );
    if (unwantedMatch) {
      return {
        type: 'unwanted',
        original: normalized,
        system: unwantedMatch[1].trim(),
        requirement: unwantedMatch[2].trim(),
        negated: true,
      };
    }

    // Pattern 5: Ubiquitous - THE [system] SHALL [requirement]
    const ubiquitousMatch = normalized.match(
      /^THE\s+(.+?)\s+SHALL\s+(.+)$/i
    );
    if (ubiquitousMatch) {
      return {
        type: 'ubiquitous',
        original: normalized,
        system: ubiquitousMatch[1].trim(),
        requirement: ubiquitousMatch[2].trim(),
      };
    }

    return null;
  }

  /**
   * パターンから変数を抽出
   */
  private extractVariables(pattern: EarsPattern): Map<string, string> {
    const variables = new Map<string, string>();
    const allText = [
      pattern.requirement,
      pattern.event,
      pattern.state,
      pattern.condition,
    ].filter(Boolean).join(' ');

    // 数値を含む変数パターンを検出
    // 例: "within 100ms" → response_time
    const timeMatch = allText.match(/within\s+(\d+)\s*(ms|s|seconds?|milliseconds?)/i);
    if (timeMatch) {
      variables.set('response_time', 'Int');
      variables.set('time_limit', 'Int');
    }

    // 比較演算子を含む変数を検出
    // 例: "amount > 0" → amount: Int
    const comparisonMatches = allText.matchAll(/(\w+)\s*([<>=]+)\s*(\d+)/g);
    for (const match of comparisonMatches) {
      const varName = this.toSmtIdentifier(match[1]);
      variables.set(varName, 'Int');
    }

    // システム状態変数
    variables.set(this.toSmtIdentifier(pattern.system) + '_active', 'Bool');

    // イベント/状態/条件に基づく変数
    if (pattern.event) {
      variables.set(this.toSmtIdentifier(pattern.event) + '_occurred', 'Bool');
    }
    if (pattern.state) {
      variables.set(this.toSmtIdentifier(pattern.state) + '_active', 'Bool');
    }
    if (pattern.condition) {
      variables.set(this.toSmtIdentifier(pattern.condition) + '_holds', 'Bool');
    }

    return variables;
  }

  /**
   * SMT宣言を生成
   */
  private generateDeclarations(variables: Map<string, string>): SmtDeclaration[] {
    const declarations: SmtDeclaration[] = [];

    for (const [name, type] of variables) {
      // カスタム型マッピングを適用
      const smtType = this.options.typeMapping?.[name] ?? type;
      declarations.push({
        name,
        type: smtType,
        description: `Variable derived from EARS requirement`,
      });
    }

    return declarations;
  }

  /**
   * SMTアサーションを生成
   */
  private generateAssertions(pattern: EarsPattern, warnings: string[]): string[] {
    const assertions: string[] = [];

    switch (pattern.type) {
      case 'ubiquitous':
        // 常に成り立つ: ∀ state. requirement
        assertions.push(this.generateUbiquitousAssertion(pattern));
        break;

      case 'event-driven':
        // イベント発生時に成り立つ: event → requirement
        assertions.push(this.generateEventDrivenAssertion(pattern));
        break;

      case 'state-driven':
        // 状態が有効な間成り立つ: state → requirement
        assertions.push(this.generateStateDrivenAssertion(pattern));
        break;

      case 'unwanted':
        // 禁止動作: ¬behavior
        assertions.push(this.generateUnwantedAssertion(pattern));
        break;

      case 'optional':
        // 条件付き: condition → requirement
        assertions.push(this.generateOptionalAssertion(pattern));
        break;

      default:
        warnings.push(`Unknown pattern type: ${pattern.type}`);
    }

    return assertions;
  }

  /**
   * Ubiquitousパターンのアサーション生成
   */
  private generateUbiquitousAssertion(pattern: EarsPattern): string {
    const systemVar = this.toSmtIdentifier(pattern.system) + '_active';
    const reqVar = this.toSmtIdentifier(pattern.requirement);
    
    // システムがアクティブなら要件が成り立つ
    return `(=> ${systemVar} ${reqVar})`;
  }

  /**
   * Event-drivenパターンのアサーション生成
   */
  private generateEventDrivenAssertion(pattern: EarsPattern): string {
    const eventVar = this.toSmtIdentifier(pattern.event!) + '_occurred';
    const reqVar = this.toSmtIdentifier(pattern.requirement);
    
    // イベントが発生したら要件が成り立つ
    return `(=> ${eventVar} ${reqVar})`;
  }

  /**
   * State-drivenパターンのアサーション生成
   */
  private generateStateDrivenAssertion(pattern: EarsPattern): string {
    const stateVar = this.toSmtIdentifier(pattern.state!) + '_active';
    const reqVar = this.toSmtIdentifier(pattern.requirement);
    
    // 状態が有効なら要件が成り立つ
    return `(=> ${stateVar} ${reqVar})`;
  }

  /**
   * Unwantedパターンのアサーション生成
   */
  private generateUnwantedAssertion(pattern: EarsPattern): string {
    const behaviorVar = this.toSmtIdentifier(pattern.requirement);
    
    // 禁止動作は発生しない
    return `(not ${behaviorVar})`;
  }

  /**
   * Optionalパターンのアサーション生成
   */
  private generateOptionalAssertion(pattern: EarsPattern): string {
    const conditionVar = this.toSmtIdentifier(pattern.condition!) + '_holds';
    const reqVar = this.toSmtIdentifier(pattern.requirement);
    
    // 条件が成り立つなら要件が成り立つ
    return `(=> ${conditionVar} ${reqVar})`;
  }

  /**
   * SMT-LIB2スクリプトを組み立て
   */
  private buildSmtLib2(
    declarations: SmtDeclaration[],
    assertions: string[]
  ): string {
    const lines: string[] = [];

    // ヘッダー
    lines.push('; Generated by MUSUBIX EarsToSmtConverter');
    lines.push('; EARS to SMT-LIB2 conversion');
    lines.push('');
    lines.push('(set-logic ALL)');
    lines.push('');

    // 宣言
    lines.push('; Variable declarations');
    for (const decl of declarations) {
      if (decl.description) {
        lines.push(`; ${decl.description}`);
      }
      lines.push(`(declare-const ${decl.name} ${decl.type})`);
    }
    lines.push('');

    // アサーション
    lines.push('; Assertions');
    for (const assertion of assertions) {
      lines.push(`(assert ${assertion})`);
    }
    lines.push('');

    // チェック
    lines.push('; Check satisfiability');
    lines.push('(check-sat)');

    return lines.join('\n');
  }

  /**
   * 文字列をSMT識別子に変換
   */
  private toSmtIdentifier(text: string): string {
    return text
      .toLowerCase()
      .replace(/[^a-z0-9_]/g, '_')
      .replace(/_+/g, '_')
      .replace(/^_|_$/g, '')
      .substring(0, 50); // 長すぎる識別子を切り詰め
  }

  /**
   * 適用されたルールを取得
   */
  private getAppliedRules(patternType: EarsPatternType): string[] {
    const rules: Record<EarsPatternType, string[]> = {
      'ubiquitous': ['system-active-implies-requirement'],
      'event-driven': ['event-triggers-response'],
      'state-driven': ['state-maintains-requirement'],
      'unwanted': ['behavior-negation'],
      'optional': ['condition-implies-requirement'],
    };

    return rules[patternType] ?? [];
  }

  /**
   * サポートされているパターンタイプを取得
   */
  getSupportedPatterns(): EarsPatternType[] {
    return ['ubiquitous', 'event-driven', 'state-driven', 'unwanted', 'optional'];
  }

  /**
   * パターンのサンプルを取得
   */
  getPatternExamples(): Record<EarsPatternType, string> {
    return {
      'ubiquitous': 'THE system SHALL validate all user inputs',
      'event-driven': 'WHEN user clicks submit, THE system SHALL save the data',
      'state-driven': 'WHILE user is logged in, THE system SHALL display the dashboard',
      'unwanted': 'THE system SHALL NOT expose sensitive data in logs',
      'optional': 'IF payment amount exceeds 10000, THEN THE system SHALL require additional verification',
    };
  }
}
