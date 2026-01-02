/**
 * Explanation Generator
 * 
 * Generates human-readable explanations from reasoning chains
 * 
 * @packageDocumentation
 * @module explanation/explanation-generator
 * 
 * @see REQ-EXP-002 - Explanation Generation
 * @see Article VIII - Transparency Standards
 */

import {
  ReasoningChain,
  ReasoningStep,
  ReasoningStepType,
  Evidence,
  Alternative,
  ConfidenceLevel,
} from './reasoning-chain.js';

/**
 * Explanation detail level
 */
export type ExplanationLevel = 'minimal' | 'summary' | 'detailed' | 'comprehensive';

/**
 * Explanation format
 */
export type ExplanationFormat = 'text' | 'markdown' | 'html' | 'json';

/**
 * Audience type
 */
export type AudienceType = 'expert' | 'technical' | 'business' | 'general';

/**
 * Explanation section
 */
export interface ExplanationSection {
  /** Section title */
  title: string;
  /** Section content */
  content: string;
  /** Section level (1-4) */
  level: number;
  /** Subsections */
  subsections?: ExplanationSection[];
}

/**
 * Generated explanation
 */
export interface Explanation {
  /** Explanation ID */
  id: string;
  /** Chain ID */
  chainId: string;
  /** Title */
  title: string;
  /** Executive summary */
  summary: string;
  /** Sections */
  sections: ExplanationSection[];
  /** Key insights */
  keyInsights: string[];
  /** Confidence assessment */
  confidenceAssessment: string;
  /** Uncertainties and limitations */
  uncertainties: string[];
  /** Format */
  format: ExplanationFormat;
  /** Level */
  level: ExplanationLevel;
  /** Audience */
  audience: AudienceType;
  /** Generated at */
  generatedAt: Date;
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Explanation generator options
 */
export interface ExplanationGeneratorOptions {
  /** Detail level */
  level: ExplanationLevel;
  /** Output format */
  format: ExplanationFormat;
  /** Target audience */
  audience: AudienceType;
  /** Include evidence */
  includeEvidence: boolean;
  /** Include alternatives */
  includeAlternatives: boolean;
  /** Include confidence scores */
  includeConfidenceScores: boolean;
  /** Include timestamps */
  includeTimestamps: boolean;
  /** Maximum sections */
  maxSections: number;
  /** Language */
  language: 'en' | 'ja';
}

/**
 * Default options
 */
export const DEFAULT_GENERATOR_OPTIONS: ExplanationGeneratorOptions = {
  level: 'detailed',
  format: 'markdown',
  audience: 'technical',
  includeEvidence: true,
  includeAlternatives: true,
  includeConfidenceScores: true,
  includeTimestamps: false,
  maxSections: 10,
  language: 'en',
};

/**
 * Localized strings
 */
const LOCALE_STRINGS = {
  en: {
    processOverview: 'Process Overview',
    reasoningProcess: 'Reasoning Process',
    keyDecisions: 'Key Decisions',
    evidenceUsed: 'Evidence Used',
    alternativesConsidered: 'Alternatives Considered',
    conclusion: 'Conclusion',
    confidenceAssessment: 'Confidence Assessment',
    uncertainties: 'Uncertainties and Limitations',
    stepTypes: {
      input: 'Input',
      analysis: 'Analysis',
      inference: 'Inference',
      decision: 'Decision',
      action: 'Action',
      validation: 'Validation',
      output: 'Output',
      error: 'Error',
      fallback: 'Fallback',
    } as Record<ReasoningStepType, string>,
    confidenceLevels: {
      high: 'High confidence',
      medium: 'Medium confidence',
      low: 'Low confidence',
      uncertain: 'Uncertain',
    } as Record<ConfidenceLevel, string>,
  },
  ja: {
    processOverview: 'プロセス概要',
    reasoningProcess: '推論プロセス',
    keyDecisions: '主要な決定事項',
    evidenceUsed: '使用した証拠',
    alternativesConsidered: '検討した代替案',
    conclusion: '結論',
    confidenceAssessment: '信頼度評価',
    uncertainties: '不確実性と制限事項',
    stepTypes: {
      input: '入力',
      analysis: '分析',
      inference: '推論',
      decision: '決定',
      action: 'アクション',
      validation: '検証',
      output: '出力',
      error: 'エラー',
      fallback: 'フォールバック',
    } as Record<ReasoningStepType, string>,
    confidenceLevels: {
      high: '高信頼度',
      medium: '中信頼度',
      low: '低信頼度',
      uncertain: '不確実',
    } as Record<ConfidenceLevel, string>,
  },
};

/**
 * Explanation Generator
 */
export class ExplanationGenerator {
  private options: ExplanationGeneratorOptions;
  private explanationCounter = 0;

  constructor(options?: Partial<ExplanationGeneratorOptions>) {
    this.options = { ...DEFAULT_GENERATOR_OPTIONS, ...options };
  }

  /**
   * Generate explanation from reasoning chain
   */
  generate(chain: ReasoningChain, options?: Partial<ExplanationGeneratorOptions>): Explanation {
    const opts = { ...this.options, ...options };
    const locale = LOCALE_STRINGS[opts.language];
    
    const sections = this.generateSections(chain, opts, locale);
    const keyInsights = this.extractKeyInsights(chain, locale);
    const confidenceAssessment = this.generateConfidenceAssessment(chain, locale);
    const uncertainties = this.extractUncertainties(chain);

    const explanation: Explanation = {
      id: this.generateId(),
      chainId: chain.id,
      title: this.generateTitle(chain),
      summary: this.generateSummary(chain, opts),
      sections: sections.slice(0, opts.maxSections),
      keyInsights,
      confidenceAssessment,
      uncertainties,
      format: opts.format,
      level: opts.level,
      audience: opts.audience,
      generatedAt: new Date(),
    };

    return explanation;
  }

  /**
   * Format explanation to string
   */
  format(explanation: Explanation): string {
    switch (explanation.format) {
      case 'text':
        return this.formatAsText(explanation);
      case 'markdown':
        return this.formatAsMarkdown(explanation);
      case 'html':
        return this.formatAsHtml(explanation);
      case 'json':
        return JSON.stringify(explanation, null, 2);
      default:
        return this.formatAsMarkdown(explanation);
    }
  }

  /**
   * Generate explanation and format in one step
   */
  explain(chain: ReasoningChain, options?: Partial<ExplanationGeneratorOptions>): string {
    const explanation = this.generate(chain, options);
    return this.format(explanation);
  }

  /**
   * Generate sections based on reasoning chain
   */
  private generateSections(
    chain: ReasoningChain,
    opts: ExplanationGeneratorOptions,
    locale: typeof LOCALE_STRINGS.en
  ): ExplanationSection[] {
    const sections: ExplanationSection[] = [];

    // Process Overview
    if (opts.level !== 'minimal') {
      sections.push({
        title: locale.processOverview,
        content: this.generateProcessOverview(chain, opts),
        level: 1,
      });
    }

    // Reasoning Process
    const reasoningSection = this.generateReasoningSection(chain, opts, locale);
    if (reasoningSection.subsections?.length || reasoningSection.content) {
      sections.push(reasoningSection);
    }

    // Key Decisions
    const decisions = chain.steps.filter((s: ReasoningStep) => s.type === 'decision');
    if (decisions.length > 0 && opts.level !== 'minimal') {
      sections.push({
        title: locale.keyDecisions,
        content: this.formatDecisions(decisions, opts, locale),
        level: 1,
      });
    }

    // Evidence Used
    if (opts.includeEvidence && opts.level === 'comprehensive') {
      const allEvidence = chain.steps.flatMap((s: ReasoningStep) => s.evidence ?? []);
      if (allEvidence.length > 0) {
        sections.push({
          title: locale.evidenceUsed,
          content: this.formatEvidence(allEvidence),
          level: 1,
        });
      }
    }

    // Alternatives Considered
    if (opts.includeAlternatives && opts.level === 'comprehensive') {
      const allAlternatives = chain.steps.flatMap((s: ReasoningStep) => s.alternatives ?? []);
      if (allAlternatives.length > 0) {
        sections.push({
          title: locale.alternativesConsidered,
          content: this.formatAlternatives(allAlternatives),
          level: 1,
        });
      }
    }

    // Conclusion
    if (chain.outcome) {
      sections.push({
        title: locale.conclusion,
        content: this.formatConclusion(chain),
        level: 1,
      });
    }

    return sections;
  }

  /**
   * Generate process overview
   */
  private generateProcessOverview(
    chain: ReasoningChain,
    opts: ExplanationGeneratorOptions
  ): string {
    const stepCount = chain.steps.length;
    const duration = chain.endTime
      ? chain.endTime.getTime() - chain.startTime.getTime()
      : Date.now() - chain.startTime.getTime();

    let overview = `Task: ${chain.task}\n`;
    overview += `Steps: ${stepCount}\n`;
    overview += `Duration: ${this.formatDuration(duration)}\n`;
    overview += `Status: ${chain.status}\n`;
    
    if (opts.includeConfidenceScores) {
      overview += `Overall Confidence: ${(chain.overallConfidence * 100).toFixed(1)}%\n`;
    }

    return overview;
  }

  /**
   * Generate reasoning section
   */
  private generateReasoningSection(
    chain: ReasoningChain,
    opts: ExplanationGeneratorOptions,
    locale: typeof LOCALE_STRINGS.en
  ): ExplanationSection {
    const subsections: ExplanationSection[] = [];

    // Group steps by type for summary and detailed levels
    if (opts.level === 'summary' || opts.level === 'detailed') {
      const stepsByType = this.groupStepsByType(chain.steps);
      
      for (const [type, steps] of Object.entries(stepsByType)) {
        if (steps.length > 0) {
          subsections.push({
            title: locale.stepTypes[type as ReasoningStepType],
            content: this.formatStepGroup(steps, opts, locale),
            level: 2,
          });
        }
      }
    }

    // Include all steps for comprehensive level
    if (opts.level === 'comprehensive') {
      for (const step of chain.steps) {
        subsections.push({
          title: `${locale.stepTypes[step.type]}: ${step.description}`,
          content: this.formatStepDetail(step, opts, locale),
          level: 2,
        });
      }
    }

    return {
      title: locale.reasoningProcess,
      content: opts.level === 'minimal' 
        ? this.formatMinimalReasoning(chain.steps, locale) 
        : '',
      level: 1,
      subsections: opts.level !== 'minimal' ? subsections : undefined,
    };
  }

  /**
   * Group steps by type
   */
  private groupStepsByType(steps: ReasoningStep[]): Record<ReasoningStepType, ReasoningStep[]> {
    const grouped: Record<ReasoningStepType, ReasoningStep[]> = {
      input: [],
      analysis: [],
      inference: [],
      decision: [],
      action: [],
      validation: [],
      output: [],
      error: [],
      fallback: [],
    };

    for (const step of steps) {
      grouped[step.type].push(step);
    }

    return grouped;
  }

  /**
   * Format step group
   */
  private formatStepGroup(
    steps: ReasoningStep[],
    opts: ExplanationGeneratorOptions,
    locale: typeof LOCALE_STRINGS.en
  ): string {
    return steps
      .map((step) => {
        let line = `- ${step.description}`;
        if (opts.includeConfidenceScores) {
          line += ` (${locale.confidenceLevels[step.confidence]})`;
        }
        return line;
      })
      .join('\n');
  }

  /**
   * Format step detail
   */
  private formatStepDetail(
    step: ReasoningStep,
    opts: ExplanationGeneratorOptions,
    locale: typeof LOCALE_STRINGS.en
  ): string {
    let detail = '';
    
    if (opts.includeTimestamps) {
      detail += `Time: ${step.timestamp.toISOString()}\n`;
    }
    
    if (step.duration) {
      detail += `Duration: ${this.formatDuration(step.duration)}\n`;
    }
    
    if (opts.includeConfidenceScores) {
      detail += `Confidence: ${locale.confidenceLevels[step.confidence]} (${(step.confidenceScore * 100).toFixed(1)}%)\n`;
    }
    
    if (step.input !== undefined) {
      detail += `Input: ${this.formatValue(step.input)}\n`;
    }
    
    if (step.output !== undefined) {
      detail += `Output: ${this.formatValue(step.output)}\n`;
    }
    
    if (step.evidence?.length) {
      detail += `Evidence: ${step.evidence.length} item(s)\n`;
    }
    
    if (step.alternatives?.length) {
      detail += `Alternatives considered: ${step.alternatives.length}\n`;
    }

    return detail;
  }

  /**
   * Format minimal reasoning
   */
  private formatMinimalReasoning(steps: ReasoningStep[], locale: typeof LOCALE_STRINGS.en): string {
    const keySteps = steps.filter(
      (s) => s.type === 'decision' || s.type === 'inference' || s.type === 'output'
    );
    
    return keySteps
      .map((step) => `${locale.stepTypes[step.type]}: ${step.description}`)
      .join('\n');
  }

  /**
   * Format decisions
   */
  private formatDecisions(
    decisions: ReasoningStep[],
    opts: ExplanationGeneratorOptions,
    locale: typeof LOCALE_STRINGS.en
  ): string {
    return decisions
      .map((d: ReasoningStep, i: number) => {
        let text = `${i + 1}. ${d.description}`;
        if (opts.includeConfidenceScores) {
          text += ` [${locale.confidenceLevels[d.confidence]}]`;
        }
        if (d.alternatives?.length && opts.includeAlternatives) {
          text += `\n   Alternatives: ${d.alternatives.map((a: Alternative) => a.description).join(', ')}`;
        }
        return text;
      })
      .join('\n');
  }

  /**
   * Format evidence
   */
  private formatEvidence(evidence: Evidence[]): string {
    return evidence
      .map((e) => `- [${e.type}] ${e.source}: ${e.content} (relevance: ${(e.relevance * 100).toFixed(0)}%)`)
      .join('\n');
  }

  /**
   * Format alternatives
   */
  private formatAlternatives(alternatives: Alternative[]): string {
    return alternatives
      .map((a) => `- ${a.description}\n  Rejected: ${a.rejectionReason}`)
      .join('\n');
  }

  /**
   * Format conclusion
   */
  private formatConclusion(chain: ReasoningChain): string {
    if (!chain.outcome) return '';
    
    let conclusion = chain.outcome.summary + '\n';
    
    if (chain.outcome.keyDecisions.length > 0) {
      conclusion += '\nKey decisions:\n';
      conclusion += chain.outcome.keyDecisions.map((d) => `- ${d}`).join('\n');
    }
    
    return conclusion;
  }

  /**
   * Generate summary
   */
  private generateSummary(chain: ReasoningChain, _opts: ExplanationGeneratorOptions): string {
    if (chain.outcome) {
      return chain.outcome.summary;
    }
    
    const lastOutput = [...chain.steps].reverse().find((s) => s.type === 'output');
    if (lastOutput) {
      return lastOutput.description;
    }
    
    return `Reasoning chain for: ${chain.task}`;
  }

  /**
   * Generate title
   */
  private generateTitle(chain: ReasoningChain): string {
    const maxLength = 80;
    if (chain.task.length <= maxLength) {
      return chain.task;
    }
    return chain.task.substring(0, maxLength - 3) + '...';
  }

  /**
   * Extract key insights
   */
  private extractKeyInsights(chain: ReasoningChain, _locale: typeof LOCALE_STRINGS.en): string[] {
    const insights: string[] = [];
    
    // High confidence decisions
    const highConfDecisions = chain.steps.filter(
      (s: ReasoningStep) => s.type === 'decision' && s.confidence === 'high'
    );
    for (const d of highConfDecisions.slice(0, 3)) {
      insights.push(`Decision: ${d.description}`);
    }
    
    // Key inferences
    const inferences = chain.steps.filter((s: ReasoningStep) => s.type === 'inference');
    for (const i of inferences.slice(0, 2)) {
      insights.push(`Inference: ${i.description}`);
    }
    
    // Outcome key decisions
    if (chain.outcome?.keyDecisions) {
      for (const kd of chain.outcome.keyDecisions.slice(0, 2)) {
        if (!insights.includes(`Decision: ${kd}`)) {
          insights.push(kd);
        }
      }
    }
    
    return insights.slice(0, 5);
  }

  /**
   * Generate confidence assessment
   */
  private generateConfidenceAssessment(chain: ReasoningChain, locale: typeof LOCALE_STRINGS.en): string {
    const overall = chain.overallConfidence;
    const level = this.scoreToLevel(overall);
    
    const lowConfSteps = chain.steps.filter((s: ReasoningStep) => s.confidence === 'low' || s.confidence === 'uncertain');
    
    let assessment = `${locale.confidenceLevels[level]} (${(overall * 100).toFixed(1)}%)`;
    
    if (lowConfSteps.length > 0) {
      assessment += `\n${lowConfSteps.length} step(s) with low confidence.`;
    }
    
    return assessment;
  }

  /**
   * Extract uncertainties
   */
  private extractUncertainties(chain: ReasoningChain): string[] {
    const uncertainties: string[] = [];
    
    // Low confidence steps
    const lowConfSteps = chain.steps.filter((s: ReasoningStep) => s.confidence === 'low' || s.confidence === 'uncertain');
    for (const step of lowConfSteps) {
      uncertainties.push(`Uncertain ${step.type}: ${step.description}`);
    }
    
    // Outcome uncertainties
    if (chain.outcome?.uncertainties) {
      uncertainties.push(...chain.outcome.uncertainties);
    }
    
    // Errors
    if (chain.error) {
      uncertainties.push(`Error: ${chain.error}`);
    }
    
    return uncertainties;
  }

  /**
   * Format as text
   */
  private formatAsText(explanation: Explanation): string {
    let text = `${explanation.title}\n${'='.repeat(explanation.title.length)}\n\n`;
    text += `${explanation.summary}\n\n`;
    
    for (const section of explanation.sections) {
      text += this.formatSectionAsText(section);
    }
    
    if (explanation.keyInsights.length > 0) {
      text += `Key Insights:\n${explanation.keyInsights.map((i) => `  - ${i}`).join('\n')}\n\n`;
    }
    
    if (explanation.uncertainties.length > 0) {
      text += `Uncertainties:\n${explanation.uncertainties.map((u) => `  - ${u}`).join('\n')}\n\n`;
    }
    
    text += `Confidence: ${explanation.confidenceAssessment}\n`;
    
    return text;
  }

  /**
   * Format section as text
   */
  private formatSectionAsText(section: ExplanationSection, indent = ''): string {
    let text = `${indent}${section.title}\n`;
    text += `${indent}${'-'.repeat(section.title.length)}\n`;
    
    if (section.content) {
      text += `${section.content.split('\n').map((l) => `${indent}${l}`).join('\n')}\n`;
    }
    
    if (section.subsections) {
      for (const sub of section.subsections) {
        text += this.formatSectionAsText(sub, indent + '  ');
      }
    }
    
    text += '\n';
    return text;
  }

  /**
   * Format as markdown
   */
  private formatAsMarkdown(explanation: Explanation): string {
    let md = `# ${explanation.title}\n\n`;
    md += `${explanation.summary}\n\n`;
    
    for (const section of explanation.sections) {
      md += this.formatSectionAsMarkdown(section);
    }
    
    if (explanation.keyInsights.length > 0) {
      md += `## Key Insights\n\n`;
      md += explanation.keyInsights.map((i) => `- ${i}`).join('\n') + '\n\n';
    }
    
    if (explanation.uncertainties.length > 0) {
      md += `## Uncertainties\n\n`;
      md += explanation.uncertainties.map((u) => `- ${u}`).join('\n') + '\n\n';
    }
    
    md += `---\n\n*Confidence: ${explanation.confidenceAssessment}*\n`;
    
    return md;
  }

  /**
   * Format section as markdown
   */
  private formatSectionAsMarkdown(section: ExplanationSection): string {
    const heading = '#'.repeat(section.level + 1);
    let md = `${heading} ${section.title}\n\n`;
    
    if (section.content) {
      md += `${section.content}\n\n`;
    }
    
    if (section.subsections) {
      for (const sub of section.subsections) {
        md += this.formatSectionAsMarkdown(sub);
      }
    }
    
    return md;
  }

  /**
   * Format as HTML
   */
  private formatAsHtml(explanation: Explanation): string {
    let html = `<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <title>${this.escapeHtml(explanation.title)}</title>
  <style>
    body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; max-width: 800px; margin: 0 auto; padding: 20px; }
    h1, h2, h3, h4 { color: #333; }
    .summary { font-size: 1.1em; color: #666; margin-bottom: 20px; }
    .section { margin-bottom: 20px; }
    .insights { background: #f0f7ff; padding: 15px; border-radius: 5px; }
    .uncertainties { background: #fff5f0; padding: 15px; border-radius: 5px; }
    .confidence { font-style: italic; color: #888; margin-top: 20px; }
    ul { margin: 10px 0; }
  </style>
</head>
<body>
  <h1>${this.escapeHtml(explanation.title)}</h1>
  <p class="summary">${this.escapeHtml(explanation.summary)}</p>
`;
    
    for (const section of explanation.sections) {
      html += this.formatSectionAsHtml(section);
    }
    
    if (explanation.keyInsights.length > 0) {
      html += `  <div class="insights">
    <h2>Key Insights</h2>
    <ul>
      ${explanation.keyInsights.map((i) => `<li>${this.escapeHtml(i)}</li>`).join('\n      ')}
    </ul>
  </div>
`;
    }
    
    if (explanation.uncertainties.length > 0) {
      html += `  <div class="uncertainties">
    <h2>Uncertainties</h2>
    <ul>
      ${explanation.uncertainties.map((u) => `<li>${this.escapeHtml(u)}</li>`).join('\n      ')}
    </ul>
  </div>
`;
    }
    
    html += `  <p class="confidence">Confidence: ${this.escapeHtml(explanation.confidenceAssessment)}</p>
</body>
</html>`;
    
    return html;
  }

  /**
   * Format section as HTML
   */
  private formatSectionAsHtml(section: ExplanationSection): string {
    const tag = `h${Math.min(section.level + 1, 6)}`;
    let html = `  <div class="section">
    <${tag}>${this.escapeHtml(section.title)}</${tag}>
`;
    
    if (section.content) {
      html += `    <p>${this.escapeHtml(section.content).replace(/\n/g, '<br>')}</p>\n`;
    }
    
    if (section.subsections) {
      for (const sub of section.subsections) {
        html += this.formatSectionAsHtml(sub);
      }
    }
    
    html += `  </div>\n`;
    return html;
  }

  /**
   * Escape HTML
   */
  private escapeHtml(text: string): string {
    return text
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#039;');
  }

  /**
   * Format value
   */
  private formatValue(value: unknown): string {
    if (value === null) return 'null';
    if (value === undefined) return 'undefined';
    if (typeof value === 'string') return value;
    if (typeof value === 'number' || typeof value === 'boolean') return String(value);
    try {
      const json = JSON.stringify(value);
      return json.length > 100 ? json.substring(0, 97) + '...' : json;
    } catch {
      return String(value);
    }
  }

  /**
   * Format duration
   */
  private formatDuration(ms: number): string {
    if (ms < 1000) return `${ms}ms`;
    if (ms < 60000) return `${(ms / 1000).toFixed(2)}s`;
    return `${(ms / 60000).toFixed(2)}min`;
  }

  /**
   * Score to level
   */
  private scoreToLevel(score: number): ConfidenceLevel {
    if (score >= 0.8) return 'high';
    if (score >= 0.5) return 'medium';
    if (score >= 0.2) return 'low';
    return 'uncertain';
  }

  /**
   * Generate ID
   */
  private generateId(): string {
    this.explanationCounter++;
    return `exp-${Date.now()}-${this.explanationCounter}`;
  }
}

/**
 * Create explanation generator instance
 */
export function createExplanationGenerator(
  options?: Partial<ExplanationGeneratorOptions>
): ExplanationGenerator {
  return new ExplanationGenerator(options);
}
