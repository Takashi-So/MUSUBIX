// Report Generator - Markdown/JSON Report Generation
// TSK-DR-005
// REQ: REQ-DR-CORE-005

import type {
  ResearchReport,
  Finding,
  TechnicalOption,
  Recommendation,
  Reference,
  IterationLog,
} from '../types/index.js';
import { KnowledgeBase } from '../knowledge/knowledge-base.js';

/**
 * Research Metadata for Report Generation
 */
export interface ResearchMetadata {
  totalTokens: number;
  durationMs: number;
  iterations: number;
}

/**
 * Report Generator - Builder Pattern
 * 
 * REQ: REQ-DR-CORE-005 - Generate research reports with citations
 */
export class ReportGenerator {
  /**
   * Generate research report
   */
  async generate(
    query: string,
    knowledge: KnowledgeBase,
    _trajectory: IterationLog[],
    metadata: ResearchMetadata
  ): Promise<ResearchReport> {
    const summary = this.generateSummary(query, knowledge);
    const findings = this.extractFindings(knowledge);
    const options = this.extractTechnicalOptions(knowledge);
    const recommendations = this.generateRecommendations(knowledge);
    const references = this.collectReferences(knowledge);
    
    return {
      query,
      summary,
      findings,
      options,
      recommendations,
      references,
      metadata: {
        iterations: metadata.iterations,
        tokensUsed: metadata.totalTokens,
        duration: metadata.durationMs,
        confidence: this.calculateOverallConfidence(findings),
      },
    };
  }
  
  /**
   * Convert report to Markdown format
   */
  toMarkdown(report: ResearchReport): string {
    const lines: string[] = [];
    
    lines.push(`# Research Report: ${report.query}`);
    lines.push('');
    lines.push(`**Generated**: ${new Date().toISOString()}`);
    lines.push(`**Iterations**: ${report.metadata.iterations}`);
    lines.push(`**Tokens Used**: ${report.metadata.tokensUsed}`);
    lines.push(`**Duration**: ${(report.metadata.duration / 1000).toFixed(2)}s`);
    lines.push(`**Confidence**: ${(report.metadata.confidence * 100).toFixed(1)}%`);
    lines.push('');
    lines.push('---');
    lines.push('');
    
    // Summary
    lines.push('## Executive Summary');
    lines.push('');
    lines.push(report.summary);
    lines.push('');
    
    // Findings
    if (report.findings.length > 0) {
      lines.push('## Key Findings');
      lines.push('');
      for (let i = 0; i < report.findings.length; i++) {
        const finding = report.findings[i];
        lines.push(`### ${i + 1}. ${finding.statement}`);
        lines.push('');
        lines.push(`**Confidence**: ${(finding.confidence * 100).toFixed(1)}%`);
        lines.push('');
        if (finding.citations.length > 0) {
          lines.push('**Sources**:');
          for (const citation of finding.citations) {
            lines.push(`- ${citation}`);
          }
          lines.push('');
        }
      }
    }
    
    // Technical Options
    if (report.options.length > 0) {
      lines.push('## Technical Options');
      lines.push('');
      for (const option of report.options) {
        lines.push(`### ${option.name}`);
        lines.push('');
        lines.push(option.description);
        lines.push('');
        if (option.pros.length > 0) {
          lines.push('**Pros**:');
          for (const pro of option.pros) {
            lines.push(`- ✅ ${pro}`);
          }
          lines.push('');
        }
        if (option.cons.length > 0) {
          lines.push('**Cons**:');
          for (const con of option.cons) {
            lines.push(`- ⚠️ ${con}`);
          }
          lines.push('');
        }
        if (option.useCases.length > 0) {
          lines.push('**Use Cases**:');
          for (const useCase of option.useCases) {
            lines.push(`- ${useCase}`);
          }
          lines.push('');
        }
      }
    }
    
    // Recommendations
    if (report.recommendations.length > 0) {
      lines.push('## Recommendations');
      lines.push('');
      const sortedRecs = [...report.recommendations].sort((a, b) => b.priority - a.priority);
      for (const rec of sortedRecs) {
        lines.push(`### Priority ${rec.priority}: ${rec.recommendation}`);
        lines.push('');
        lines.push(rec.rationale);
        lines.push('');
      }
    }
    
    // References
    if (report.references.length > 0) {
      lines.push('## References');
      lines.push('');
      for (const ref of report.references) {
        lines.push(`[${ref.id}] ${ref.title}`);
        lines.push(`- URL: ${ref.url}`);
        lines.push(`- Accessed: ${ref.accessDate}`);
        lines.push('');
      }
    }
    
    return lines.join('\n');
  }
  
  /**
   * Convert report to JSON format
   */
  toJSON(report: ResearchReport): string {
    return JSON.stringify(report, null, 2);
  }
  
  /**
   * Generate executive summary
   */
  private generateSummary(query: string, knowledge: KnowledgeBase): string {
    const facts = knowledge.getAll().filter(item => item.type === 'fact');
    
    if (facts.length === 0) {
      return `Research on "${query}" found no conclusive facts. Additional investigation may be needed.`;
    }
    
    const topFacts = facts
      .sort((a, b) => b.relevance - a.relevance)
      .slice(0, 3)
      .map(f => f.content)
      .join(' ');
    
    return `Research on "${query}" identified ${facts.length} key facts. ${topFacts}`;
  }
  
  /**
   * Extract findings from knowledge base
   */
  private extractFindings(knowledge: KnowledgeBase): Finding[] {
    return knowledge
      .getFindings()
      .slice(0, 10) // Top 10 findings
      .map(item => ({
        statement: item.content,
        citations: item.sources,
        confidence: item.relevance,
      }));
  }
  
  /**
   * Extract technical options (placeholder - requires LM reasoning)
   */
  private extractTechnicalOptions(_knowledge: KnowledgeBase): TechnicalOption[] {
    // TODO: Implement with LM reasoning in TSK-DR-010
    return [];
  }
  
  /**
   * Generate recommendations (placeholder - requires LM reasoning)
   */
  private generateRecommendations(_knowledge: KnowledgeBase): Recommendation[] {
    // TODO: Implement with LM reasoning in TSK-DR-010
    return [];
  }
  
  /**
   * Collect references/citations
   */
  private collectReferences(knowledge: KnowledgeBase): Reference[] {
    const urlSet = new Set<string>();
    const references: Reference[] = [];
    
    for (const item of knowledge.getAll()) {
      for (const source of item.sources) {
        if (!urlSet.has(source)) {
          urlSet.add(source);
          references.push({
            id: `ref-${references.length + 1}`,
            url: source,
            title: this.extractTitleFromUrl(source),
            accessDate: new Date().toISOString().split('T')[0],
          });
        }
      }
    }
    
    return references;
  }
  
  /**
   * Calculate overall confidence
   */
  private calculateOverallConfidence(findings: Finding[]): number {
    if (findings.length === 0) {
      return 0;
    }
    
    const sum = findings.reduce((acc, f) => acc + f.confidence, 0);
    return sum / findings.length;
  }
  
  /**
   * Extract title from URL
   */
  private extractTitleFromUrl(url: string): string {
    try {
      const urlObj = new URL(url);
      return urlObj.hostname;
    } catch {
      return url;
    }
  }
}
