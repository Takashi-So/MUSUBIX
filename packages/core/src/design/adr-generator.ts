/**
 * ADR (Architecture Decision Record) Generator
 * 
 * Generates ADRs from design decisions
 * 
 * @packageDocumentation
 * @module design/adr-generator
 * 
 * @see REQ-DES-005 - ADR Generation
 * @see Article IV - Design-Implementation Consistency
 */

/**
 * ADR status
 */
export type ADRStatus = 'proposed' | 'accepted' | 'deprecated' | 'superseded';

/**
 * Decision driver
 */
export interface DecisionDriver {
  /** Driver ID */
  id: string;
  /** Description */
  description: string;
  /** Priority */
  priority: 'high' | 'medium' | 'low';
  /** Category */
  category?: string;
}

/**
 * Considered option
 */
export interface ConsideredOption {
  /** Option ID */
  id: string;
  /** Option name */
  name: string;
  /** Description */
  description: string;
  /** Pros */
  pros: string[];
  /** Cons */
  cons: string[];
  /** Chosen */
  chosen: boolean;
}

/**
 * ADR (Architecture Decision Record)
 */
export interface ADR {
  /** ADR ID */
  id: string;
  /** ADR number */
  number: number;
  /** Title */
  title: string;
  /** Status */
  status: ADRStatus;
  /** Date */
  date: Date;
  /** Context */
  context: string;
  /** Decision drivers */
  drivers: DecisionDriver[];
  /** Considered options */
  options: ConsideredOption[];
  /** Decision outcome */
  decision: string;
  /** Rationale */
  rationale: string;
  /** Consequences */
  consequences: {
    positive: string[];
    negative: string[];
    neutral: string[];
  };
  /** Related ADRs */
  relatedAdrs?: string[];
  /** Supersedes */
  supersedes?: string;
  /** Superseded by */
  supersededBy?: string;
  /** Links */
  links?: Array<{
    title: string;
    url: string;
  }>;
  /** Authors */
  authors?: string[];
  /** Tags */
  tags?: string[];
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * ADR input
 */
export interface ADRInput {
  /** Title */
  title: string;
  /** Context description */
  context: string;
  /** Decision drivers */
  drivers?: Array<{
    description: string;
    priority?: 'high' | 'medium' | 'low';
    category?: string;
  }>;
  /** Options considered */
  options: Array<{
    name: string;
    description: string;
    pros?: string[];
    cons?: string[];
    chosen?: boolean;
  }>;
  /** Decision */
  decision?: string;
  /** Rationale */
  rationale?: string;
  /** Positive consequences */
  positiveConsequences?: string[];
  /** Negative consequences */
  negativeConsequences?: string[];
  /** Related ADRs */
  relatedAdrs?: string[];
  /** Authors */
  authors?: string[];
  /** Tags */
  tags?: string[];
}

/**
 * ADR template
 */
export type ADRTemplate = 'madr' | 'nygard' | 'alexandrian' | 'simple';

/**
 * ADR generator config
 */
export interface ADRGeneratorConfig {
  /** Template to use */
  template: ADRTemplate;
  /** Output format */
  outputFormat: 'markdown' | 'json' | 'yaml';
  /** Include table of contents */
  includeToc: boolean;
  /** Number prefix */
  numberPrefix: string;
  /** Number padding */
  numberPadding: number;
  /** Date format */
  dateFormat: 'iso' | 'long' | 'short';
  /** Auto-generate rationale */
  autoRationale: boolean;
}

/**
 * Default configuration
 */
export const DEFAULT_ADR_CONFIG: ADRGeneratorConfig = {
  template: 'madr',
  outputFormat: 'markdown',
  includeToc: true,
  numberPrefix: 'ADR-',
  numberPadding: 4,
  dateFormat: 'iso',
  autoRationale: true,
};

/**
 * ADR Generator
 */
export class ADRGenerator {
  private config: ADRGeneratorConfig;
  private adrCounter = 0;
  private driverCounter = 0;
  private optionCounter = 0;

  constructor(config?: Partial<ADRGeneratorConfig>) {
    this.config = { ...DEFAULT_ADR_CONFIG, ...config };
  }

  /**
   * Generate ADR from input
   */
  generate(input: ADRInput, number?: number): ADR {
    const adrNumber = number ?? ++this.adrCounter;
    
    // Process drivers
    const drivers: DecisionDriver[] = (input.drivers ?? []).map((d) => ({
      id: `driver-${++this.driverCounter}`,
      description: d.description,
      priority: d.priority ?? 'medium',
      category: d.category,
    }));

    // Process options
    const options: ConsideredOption[] = input.options.map((o) => ({
      id: `option-${++this.optionCounter}`,
      name: o.name,
      description: o.description,
      pros: o.pros ?? [],
      cons: o.cons ?? [],
      chosen: o.chosen ?? false,
    }));

    // Find chosen option
    const chosenOption = options.find((o) => o.chosen);

    // Generate decision text if not provided
    const decision = input.decision ??
      (chosenOption ? `We will use ${chosenOption.name}.` : 'Decision pending.');

    // Generate rationale if not provided and autoRationale is enabled
    const rationale = input.rationale ??
      (this.config.autoRationale && chosenOption
        ? this.generateRationale(chosenOption, options, drivers)
        : '');

    // Analyze consequences
    const consequences = {
      positive: input.positiveConsequences ??
        (chosenOption ? this.analyzePositiveConsequences(chosenOption) : []),
      negative: input.negativeConsequences ??
        (chosenOption ? this.analyzeNegativeConsequences(chosenOption) : []),
      neutral: this.analyzeNeutralConsequences(options),
    };

    return {
      id: `adr-${Date.now()}-${adrNumber}`,
      number: adrNumber,
      title: input.title,
      status: 'proposed',
      date: new Date(),
      context: input.context,
      drivers,
      options,
      decision,
      rationale,
      consequences,
      relatedAdrs: input.relatedAdrs,
      authors: input.authors,
      tags: input.tags,
    };
  }

  /**
   * Export ADR to formatted output
   */
  export(adr: ADR, format?: ADRGeneratorConfig['outputFormat']): string {
    const fmt = format ?? this.config.outputFormat;
    
    switch (fmt) {
      case 'markdown':
        return this.toMarkdown(adr);
      case 'json':
        return JSON.stringify(adr, null, 2);
      case 'yaml':
        return this.toYaml(adr);
      default:
        return this.toMarkdown(adr);
    }
  }

  /**
   * Update ADR status
   */
  updateStatus(adr: ADR, status: ADRStatus, supersededBy?: string): ADR {
    return {
      ...adr,
      status,
      supersededBy,
    };
  }

  /**
   * Create superseding ADR
   */
  supersede(original: ADR, newInput: ADRInput): { original: ADR; newAdr: ADR } {
    const newAdr = this.generate(newInput);
    newAdr.supersedes = `${this.config.numberPrefix}${original.number.toString().padStart(this.config.numberPadding, '0')}`;
    
    const updatedOriginal = this.updateStatus(
      original,
      'superseded',
      `${this.config.numberPrefix}${newAdr.number.toString().padStart(this.config.numberPadding, '0')}`
    );

    return { original: updatedOriginal, newAdr };
  }

  /**
   * Generate ADR number string
   */
  getAdrNumber(adr: ADR): string {
    return `${this.config.numberPrefix}${adr.number.toString().padStart(this.config.numberPadding, '0')}`;
  }

  /**
   * Generate rationale from chosen option
   */
  private generateRationale(
    chosen: ConsideredOption,
    options: ConsideredOption[],
    drivers: DecisionDriver[]
  ): string {
    const lines: string[] = [];

    lines.push(`${chosen.name} was chosen because:`);
    lines.push('');

    // Based on pros
    if (chosen.pros.length > 0) {
      lines.push('**Key advantages:**');
      for (const pro of chosen.pros) {
        lines.push(`- ${pro}`);
      }
      lines.push('');
    }

    // Address high-priority drivers
    const highPriority = drivers.filter((d) => d.priority === 'high');
    if (highPriority.length > 0) {
      lines.push('**Addresses critical requirements:**');
      for (const driver of highPriority) {
        lines.push(`- ${driver.description}`);
      }
      lines.push('');
    }

    // Compare with rejected options
    const rejected = options.filter((o) => !o.chosen && o.cons.length > 0);
    if (rejected.length > 0) {
      lines.push('**Compared to alternatives:**');
      for (const opt of rejected.slice(0, 2)) {
        lines.push(`- ${opt.name}: rejected due to ${opt.cons[0]?.toLowerCase() ?? 'various concerns'}`);
      }
    }

    return lines.join('\n');
  }

  /**
   * Analyze positive consequences
   */
  private analyzePositiveConsequences(chosen: ConsideredOption): string[] {
    return chosen.pros.map((pro) => `Good, because ${pro.toLowerCase()}`);
  }

  /**
   * Analyze negative consequences
   */
  private analyzeNegativeConsequences(chosen: ConsideredOption): string[] {
    return chosen.cons.map((con) => `Bad, because ${con.toLowerCase()}`);
  }

  /**
   * Analyze neutral consequences
   */
  private analyzeNeutralConsequences(options: ConsideredOption[]): string[] {
    const rejected = options.filter((o) => !o.chosen);
    return rejected.slice(0, 2).map((o) => `${o.name} was not chosen and may be reconsidered later`);
  }

  /**
   * Export to Markdown (MADR format)
   */
  private toMarkdown(adr: ADR): string {
    const lines: string[] = [];
    const number = this.getAdrNumber(adr);

    // Title
    lines.push(`# ${number}: ${adr.title}`);
    lines.push('');

    // Metadata table
    lines.push('| Metadata | Value |');
    lines.push('|----------|-------|');
    lines.push(`| Status | ${this.formatStatus(adr.status)} |`);
    lines.push(`| Date | ${this.formatDate(adr.date)} |`);
    if (adr.authors?.length) {
      lines.push(`| Authors | ${adr.authors.join(', ')} |`);
    }
    if (adr.tags?.length) {
      lines.push(`| Tags | ${adr.tags.join(', ')} |`);
    }
    if (adr.supersedes) {
      lines.push(`| Supersedes | ${adr.supersedes} |`);
    }
    if (adr.supersededBy) {
      lines.push(`| Superseded by | ${adr.supersededBy} |`);
    }
    lines.push('');

    // Table of contents
    if (this.config.includeToc) {
      lines.push('## Table of Contents');
      lines.push('');
      lines.push('- [Context](#context)');
      if (adr.drivers.length > 0) {
        lines.push('- [Decision Drivers](#decision-drivers)');
      }
      lines.push('- [Considered Options](#considered-options)');
      lines.push('- [Decision Outcome](#decision-outcome)');
      lines.push('- [Consequences](#consequences)');
      if (adr.relatedAdrs?.length) {
        lines.push('- [Related ADRs](#related-adrs)');
      }
      lines.push('');
    }

    // Context
    lines.push('## Context');
    lines.push('');
    lines.push(adr.context);
    lines.push('');

    // Decision Drivers
    if (adr.drivers.length > 0) {
      lines.push('## Decision Drivers');
      lines.push('');
      for (const driver of adr.drivers) {
        const priority = driver.priority === 'high' ? ' 🔴' : driver.priority === 'medium' ? ' 🟡' : '';
        lines.push(`- ${driver.description}${priority}`);
      }
      lines.push('');
    }

    // Considered Options
    lines.push('## Considered Options');
    lines.push('');
    for (const option of adr.options) {
      const chosen = option.chosen ? ' ✅' : '';
      lines.push(`- **${option.name}**${chosen}`);
    }
    lines.push('');

    // Options details
    for (const option of adr.options) {
      lines.push(`### ${option.name}`);
      lines.push('');
      lines.push(option.description);
      lines.push('');
      
      if (option.pros.length > 0) {
        lines.push('**Pros:**');
        for (const pro of option.pros) {
          lines.push(`- ✅ ${pro}`);
        }
        lines.push('');
      }
      
      if (option.cons.length > 0) {
        lines.push('**Cons:**');
        for (const con of option.cons) {
          lines.push(`- ❌ ${con}`);
        }
        lines.push('');
      }
    }

    // Decision Outcome
    lines.push('## Decision Outcome');
    lines.push('');
    lines.push(`**Decision:** ${adr.decision}`);
    lines.push('');
    
    if (adr.rationale) {
      lines.push('### Rationale');
      lines.push('');
      lines.push(adr.rationale);
      lines.push('');
    }

    // Consequences
    lines.push('## Consequences');
    lines.push('');
    
    if (adr.consequences.positive.length > 0) {
      lines.push('### Positive');
      lines.push('');
      for (const c of adr.consequences.positive) {
        lines.push(`- ${c}`);
      }
      lines.push('');
    }
    
    if (adr.consequences.negative.length > 0) {
      lines.push('### Negative');
      lines.push('');
      for (const c of adr.consequences.negative) {
        lines.push(`- ${c}`);
      }
      lines.push('');
    }
    
    if (adr.consequences.neutral.length > 0) {
      lines.push('### Neutral');
      lines.push('');
      for (const c of adr.consequences.neutral) {
        lines.push(`- ${c}`);
      }
      lines.push('');
    }

    // Related ADRs
    if (adr.relatedAdrs?.length) {
      lines.push('## Related ADRs');
      lines.push('');
      for (const related of adr.relatedAdrs) {
        lines.push(`- ${related}`);
      }
      lines.push('');
    }

    // Links
    if (adr.links?.length) {
      lines.push('## Links');
      lines.push('');
      for (const link of adr.links) {
        lines.push(`- [${link.title}](${link.url})`);
      }
      lines.push('');
    }

    return lines.join('\n');
  }

  /**
   * Export to YAML
   */
  private toYaml(adr: ADR): string {
    const lines: string[] = [];
    
    lines.push(`id: ${this.getAdrNumber(adr)}`);
    lines.push(`title: "${adr.title}"`);
    lines.push(`status: ${adr.status}`);
    lines.push(`date: ${this.formatDate(adr.date)}`);
    lines.push('');
    
    lines.push('context: |');
    for (const line of adr.context.split('\n')) {
      lines.push(`  ${line}`);
    }
    lines.push('');
    
    if (adr.drivers.length > 0) {
      lines.push('drivers:');
      for (const driver of adr.drivers) {
        lines.push(`  - description: "${driver.description}"`);
        lines.push(`    priority: ${driver.priority}`);
      }
      lines.push('');
    }
    
    lines.push('options:');
    for (const option of adr.options) {
      lines.push(`  - name: "${option.name}"`);
      lines.push(`    description: "${option.description}"`);
      lines.push(`    chosen: ${option.chosen}`);
      if (option.pros.length > 0) {
        lines.push('    pros:');
        for (const pro of option.pros) {
          lines.push(`      - "${pro}"`);
        }
      }
      if (option.cons.length > 0) {
        lines.push('    cons:');
        for (const con of option.cons) {
          lines.push(`      - "${con}"`);
        }
      }
    }
    lines.push('');
    
    lines.push(`decision: "${adr.decision}"`);
    lines.push('');
    
    lines.push('consequences:');
    lines.push('  positive:');
    for (const c of adr.consequences.positive) {
      lines.push(`    - "${c}"`);
    }
    lines.push('  negative:');
    for (const c of adr.consequences.negative) {
      lines.push(`    - "${c}"`);
    }
    
    return lines.join('\n');
  }

  /**
   * Format status with emoji
   */
  private formatStatus(status: ADRStatus): string {
    switch (status) {
      case 'proposed': return '🟡 Proposed';
      case 'accepted': return '✅ Accepted';
      case 'deprecated': return '⚠️ Deprecated';
      case 'superseded': return '🔄 Superseded';
      default: return status;
    }
  }

  /**
   * Format date
   */
  private formatDate(date: Date): string {
    switch (this.config.dateFormat) {
      case 'iso':
        return date.toISOString().split('T')[0];
      case 'long':
        return date.toLocaleDateString('en-US', {
          year: 'numeric',
          month: 'long',
          day: 'numeric',
        });
      case 'short':
        return date.toLocaleDateString('en-US');
      default:
        return date.toISOString().split('T')[0];
    }
  }
}

/**
 * Create ADR generator instance
 */
export function createADRGenerator(config?: Partial<ADRGeneratorConfig>): ADRGenerator {
  return new ADRGenerator(config);
}
