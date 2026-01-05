/**
 * Inference Explainer
 *
 * @module learning/inference/inference-explainer
 * @description 推論過程の説明生成
 * @requirements REQ-ONTO-013
 */

import type {
  Triple,
  AppliedRule,
  InferenceExplanation,
  InferenceResult,
  IExplainer,
} from './types.js';
import { NAMESPACES } from './types.js';

/**
 * 説明テンプレート
 */
interface ExplanationTemplate {
  /** ルールパターン */
  rulePattern: RegExp;
  /** テンプレート関数 */
  template: (premises: Triple[], conclusion: Triple, bindings: Record<string, string>) => string;
}

/**
 * 推論説明生成器
 * REQ-ONTO-013: 人間可読な推論説明生成
 */
export class InferenceExplainer implements IExplainer {
  private templates: ExplanationTemplate[] = [];
  private prefixMap: Map<string, string> = new Map();
  private explanationCounter = 0;

  constructor() {
    this.initializePrefixes();
    this.loadDefaultTemplates();
  }

  /**
   * プレフィックスマップを初期化
   */
  private initializePrefixes(): void {
    // URIからプレフィックスへのマッピング（逆引き用）
    this.prefixMap.set(NAMESPACES.RDF, 'rdf');
    this.prefixMap.set(NAMESPACES.RDFS, 'rdfs');
    this.prefixMap.set(NAMESPACES.OWL, 'owl');
    this.prefixMap.set(NAMESPACES.XSD, 'xsd');
    this.prefixMap.set(NAMESPACES.MUSUBIX, 'musubix');
  }

  /**
   * デフォルトテンプレートをロード
   */
  private loadDefaultTemplates(): void {
    // SubClass推論
    this.templates.push({
      rulePattern: /cax-sco|SubClass/i,
      template: (premises, conclusion, bindings) => {
        const instance = this.shorten(bindings['x'] || conclusion.subject);
        const subClass = this.shorten(bindings['c1'] || premises[0]?.object || '');
        const superClass = this.shorten(bindings['c2'] || conclusion.object);
        return `${instance} は ${subClass} のインスタンスであり、${subClass} は ${superClass} のサブクラスなので、${instance} は ${superClass} のインスタンスでもある`;
      },
    });

    // EquivalentClass推論
    this.templates.push({
      rulePattern: /cax-eqc|EquivalentClass/i,
      template: (_premises, conclusion, bindings) => {
        const instance = this.shorten(bindings['x'] || conclusion.subject);
        const class1 = this.shorten(bindings['c1'] || '');
        const class2 = this.shorten(bindings['c2'] || conclusion.object);
        return `${class1} と ${class2} は同値クラスなので、${instance} が ${class1} のインスタンスであれば ${class2} のインスタンスでもある`;
      },
    });

    // Property Domain推論
    this.templates.push({
      rulePattern: /prp-dom|Domain/i,
      template: (premises, conclusion, bindings) => {
        const subject = this.shorten(bindings['x'] || conclusion.subject);
        const property = this.shorten(bindings['p'] || premises[1]?.predicate || '');
        const domain = this.shorten(bindings['c'] || conclusion.object);
        return `${property} プロパティの定義域は ${domain} なので、${subject} が ${property} の主語であれば ${domain} のインスタンスである`;
      },
    });

    // Property Range推論
    this.templates.push({
      rulePattern: /prp-rng|Range/i,
      template: (premises, conclusion, bindings) => {
        const object = this.shorten(bindings['y'] || conclusion.subject);
        const property = this.shorten(bindings['p'] || premises[1]?.predicate || '');
        const range = this.shorten(bindings['c'] || conclusion.object);
        return `${property} プロパティの値域は ${range} なので、${object} が ${property} の目的語であれば ${range} のインスタンスである`;
      },
    });

    // Symmetric Property推論
    this.templates.push({
      rulePattern: /prp-symp|Symmetric/i,
      template: (premises, conclusion, bindings) => {
        const x = this.shorten(bindings['x'] || premises[1]?.subject || '');
        const y = this.shorten(bindings['y'] || premises[1]?.object || '');
        const property = this.shorten(bindings['p'] || conclusion.predicate);
        return `${property} は対称プロパティなので、${x} ${property} ${y} であれば ${y} ${property} ${x} も成り立つ`;
      },
    });

    // Transitive Property推論
    this.templates.push({
      rulePattern: /prp-trp|Transitive/i,
      template: (_premises, conclusion, bindings) => {
        const x = this.shorten(bindings['x'] || conclusion.subject);
        const y = this.shorten(bindings['y'] || '');
        const z = this.shorten(bindings['z'] || conclusion.object);
        const property = this.shorten(bindings['p'] || conclusion.predicate);
        return `${property} は推移プロパティなので、${x} ${property} ${y} かつ ${y} ${property} ${z} であれば ${x} ${property} ${z} も成り立つ`;
      },
    });

    // Inverse Property推論
    this.templates.push({
      rulePattern: /prp-inv|Inverse/i,
      template: (_premises, conclusion, bindings) => {
        const x = this.shorten(bindings['x'] || '');
        const y = this.shorten(bindings['y'] || '');
        const p1 = this.shorten(bindings['p1'] || '');
        const p2 = this.shorten(bindings['p2'] || conclusion.predicate);
        return `${p1} と ${p2} は逆プロパティなので、${x} ${p1} ${y} であれば ${y} ${p2} ${x} も成り立つ`;
      },
    });

    // SubProperty推論
    this.templates.push({
      rulePattern: /prp-spo|SubProperty/i,
      template: (_premises, conclusion, bindings) => {
        const x = this.shorten(bindings['x'] || conclusion.subject);
        const y = this.shorten(bindings['y'] || conclusion.object);
        const subProp = this.shorten(bindings['p1'] || '');
        const superProp = this.shorten(bindings['p2'] || conclusion.predicate);
        return `${subProp} は ${superProp} のサブプロパティなので、${x} ${subProp} ${y} であれば ${x} ${superProp} ${y} も成り立つ`;
      },
    });

    // sameAs推論
    this.templates.push({
      rulePattern: /eq-|sameAs/i,
      template: (_premises, conclusion, bindings) => {
        const x = this.shorten(bindings['x'] || bindings['s'] || conclusion.subject);
        const y = this.shorten(bindings['y'] || bindings['s2'] || conclusion.object);
        return `${x} と ${y} は同一個体（owl:sameAs）なので、一方について成り立つ命題は他方についても成り立つ`;
      },
    });

    // デフォルトテンプレート
    this.templates.push({
      rulePattern: /.*/,
      template: (premises, conclusion, _bindings) => {
        const premiseStr = premises
          .map((p) => `(${this.shorten(p.subject)} ${this.shorten(p.predicate)} ${this.shorten(p.object)})`)
          .join(' かつ ');
        const conclusionStr = `(${this.shorten(conclusion.subject)} ${this.shorten(conclusion.predicate)} ${this.shorten(conclusion.object)})`;
        return `${premiseStr} から ${conclusionStr} が推論される`;
      },
    });
  }

  /**
   * URIを短縮形に変換
   */
  private shorten(uri: string): string {
    if (!uri) return '?';

    for (const [namespace, prefix] of this.prefixMap) {
      if (uri.startsWith(namespace)) {
        return `${prefix}:${uri.substring(namespace.length)}`;
      }
    }

    // ハッシュやスラッシュの後のローカル名を抽出
    const hashIndex = uri.lastIndexOf('#');
    if (hashIndex !== -1) {
      return uri.substring(hashIndex + 1);
    }

    const slashIndex = uri.lastIndexOf('/');
    if (slashIndex !== -1) {
      return uri.substring(slashIndex + 1);
    }

    return uri;
  }

  /**
   * 単一の説明を生成
   */
  explain(conclusion: Triple, appliedRules: AppliedRule[]): InferenceExplanation {
    // この結論に直接関連するルールを見つける
    const relevantRule = appliedRules.find((rule) =>
      rule.inferredTriples.some(
        (t) =>
          t.subject === conclusion.subject &&
          t.predicate === conclusion.predicate &&
          t.object === conclusion.object
      )
    );

    if (!relevantRule) {
      return this.createBaseExplanation(conclusion, [], 'unknown', 0);
    }

    // 前提となるトリプルを収集（簡易実装）
    const premises = this.findPremises(conclusion, relevantRule, appliedRules);

    return this.createExplanation(conclusion, premises, relevantRule);
  }

  /**
   * 前提トリプルを検索
   */
  private findPremises(
    conclusion: Triple,
    rule: AppliedRule,
    allRules: AppliedRule[]
  ): Triple[] {
    const premises: Triple[] = [];
    const bindings = rule.bindings;

    // バインディングから前提を推測
    for (const [_varName, value] of Object.entries(bindings)) {
      // 関連するトリプルを検索
      for (const otherRule of allRules) {
        for (const triple of otherRule.inferredTriples) {
          if (
            triple.subject === value ||
            triple.object === value ||
            triple.predicate === value
          ) {
            if (
              triple.subject !== conclusion.subject ||
              triple.predicate !== conclusion.predicate ||
              triple.object !== conclusion.object
            ) {
              premises.push(triple);
            }
          }
        }
      }
    }

    // 重複を除去
    const uniquePremises = new Map<string, Triple>();
    for (const p of premises) {
      const key = `${p.subject}|${p.predicate}|${p.object}`;
      uniquePremises.set(key, p);
    }

    return Array.from(uniquePremises.values()).slice(0, 5); // 最大5件
  }

  /**
   * 説明を生成
   */
  private createExplanation(
    conclusion: Triple,
    premises: Triple[],
    rule: AppliedRule
  ): InferenceExplanation {
    // 適切なテンプレートを選択
    const template = this.templates.find((t) => t.rulePattern.test(rule.ruleId));

    let humanReadable: string;
    if (template) {
      humanReadable = template.template(premises, conclusion, rule.bindings);
    } else {
      humanReadable = `ルール「${rule.ruleName}」により推論された`;
    }

    return this.createBaseExplanation(conclusion, premises, rule.ruleId, 1, humanReadable);
  }

  /**
   * 基本説明を作成
   */
  private createBaseExplanation(
    conclusion: Triple,
    premises: Triple[],
    ruleId: string,
    depth: number,
    humanReadable?: string
  ): InferenceExplanation {
    this.explanationCounter++;

    return {
      id: `exp-${this.explanationCounter}`,
      conclusion,
      premises,
      rule: ruleId,
      humanReadable:
        humanReadable ||
        `${this.shorten(conclusion.subject)} は ${this.shorten(conclusion.predicate)} の関係で ${this.shorten(conclusion.object)} と関連している`,
      depth,
      dependsOn: [],
    };
  }

  /**
   * 全ての説明を生成
   */
  explainAll(result: InferenceResult): InferenceExplanation[] {
    const explanations: InferenceExplanation[] = [];

    for (const triple of result.inferredTriples) {
      const explanation = this.explain(triple, result.appliedRules);
      explanations.push(explanation);
    }

    return explanations;
  }

  /**
   * 説明をフォーマット
   */
  format(explanation: InferenceExplanation, format: 'text' | 'html' | 'markdown'): string {
    switch (format) {
      case 'text':
        return this.formatAsText(explanation);
      case 'html':
        return this.formatAsHtml(explanation);
      case 'markdown':
        return this.formatAsMarkdown(explanation);
      default:
        return this.formatAsText(explanation);
    }
  }

  /**
   * テキスト形式でフォーマット
   */
  private formatAsText(explanation: InferenceExplanation): string {
    const lines: string[] = [];

    lines.push(`【推論結果】`);
    lines.push(
      `  結論: ${this.shorten(explanation.conclusion.subject)} ${this.shorten(explanation.conclusion.predicate)} ${this.shorten(explanation.conclusion.object)}`
    );
    lines.push(``);
    lines.push(`【説明】`);
    lines.push(`  ${explanation.humanReadable}`);
    lines.push(``);

    if (explanation.premises.length > 0) {
      lines.push(`【前提】`);
      for (const premise of explanation.premises) {
        lines.push(
          `  - ${this.shorten(premise.subject)} ${this.shorten(premise.predicate)} ${this.shorten(premise.object)}`
        );
      }
      lines.push(``);
    }

    lines.push(`【適用ルール】 ${explanation.rule}`);

    return lines.join('\n');
  }

  /**
   * HTML形式でフォーマット
   */
  private formatAsHtml(explanation: InferenceExplanation): string {
    const conclusionHtml = `<span class="subject">${this.escapeHtml(this.shorten(explanation.conclusion.subject))}</span> 
      <span class="predicate">${this.escapeHtml(this.shorten(explanation.conclusion.predicate))}</span> 
      <span class="object">${this.escapeHtml(this.shorten(explanation.conclusion.object))}</span>`;

    const premisesHtml =
      explanation.premises.length > 0
        ? `<ul class="premises">
        ${explanation.premises
          .map(
            (p) =>
              `<li><span class="subject">${this.escapeHtml(this.shorten(p.subject))}</span> 
              <span class="predicate">${this.escapeHtml(this.shorten(p.predicate))}</span> 
              <span class="object">${this.escapeHtml(this.shorten(p.object))}</span></li>`
          )
          .join('')}
      </ul>`
        : '';

    return `
      <div class="inference-explanation">
        <h4>推論結果</h4>
        <p class="conclusion">${conclusionHtml}</p>
        <h4>説明</h4>
        <p class="human-readable">${this.escapeHtml(explanation.humanReadable)}</p>
        ${premisesHtml ? `<h4>前提</h4>${premisesHtml}` : ''}
        <p class="rule">適用ルール: <code>${this.escapeHtml(explanation.rule)}</code></p>
      </div>
    `;
  }

  /**
   * Markdown形式でフォーマット
   */
  private formatAsMarkdown(explanation: InferenceExplanation): string {
    const lines: string[] = [];

    lines.push(`### 推論結果`);
    lines.push(``);
    lines.push(
      `**結論**: \`${this.shorten(explanation.conclusion.subject)}\` → \`${this.shorten(explanation.conclusion.predicate)}\` → \`${this.shorten(explanation.conclusion.object)}\``
    );
    lines.push(``);
    lines.push(`### 説明`);
    lines.push(``);
    lines.push(`> ${explanation.humanReadable}`);
    lines.push(``);

    if (explanation.premises.length > 0) {
      lines.push(`### 前提`);
      lines.push(``);
      for (const premise of explanation.premises) {
        lines.push(
          `- \`${this.shorten(premise.subject)}\` → \`${this.shorten(premise.predicate)}\` → \`${this.shorten(premise.object)}\``
        );
      }
      lines.push(``);
    }

    lines.push(`**適用ルール**: \`${explanation.rule}\``);

    return lines.join('\n');
  }

  /**
   * HTMLエスケープ
   */
  private escapeHtml(str: string): string {
    return str
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#039;');
  }

  /**
   * カスタムテンプレートを追加
   */
  addTemplate(pattern: RegExp, template: ExplanationTemplate['template']): void {
    // デフォルトテンプレートの前に挿入
    this.templates.splice(this.templates.length - 1, 0, {
      rulePattern: pattern,
      template,
    });
  }

  /**
   * カウンターをリセット
   */
  reset(): void {
    this.explanationCounter = 0;
  }
}
