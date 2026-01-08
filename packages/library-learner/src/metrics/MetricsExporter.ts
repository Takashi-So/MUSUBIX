/**
 * MetricsExporter
 * 
 * Pattern library metrics export in JSON/Markdown format
 * 
 * @packageDocumentation
 * @module library-learner/metrics
 * 
 * @see TSK-LL-108 - MetricsExporter実装
 * @see REQ-LL-108 - メトリクスエクスポート要件
 */

/**
 * Pattern usage information
 */
export interface PatternUsageInfo {
  count: number;
  lastUsed: Date;
}

/**
 * Library metrics data
 */
export interface LibraryMetrics {
  totalPatterns: number;
  activePatterns: number;
  patternUsage: Record<string, PatternUsageInfo>;
  compressionRate: number;
  searchReductionRate: number;
  hierarchyDepth: number;
  abstractionLevels: string[];
  lastUpdated: Date;
}

/**
 * Formatted metrics with human-readable values
 */
export interface FormattedMetrics {
  compressionRateFormatted: string;
  searchReductionRateFormatted: string;
  utilizationRate: string;
  topPatterns: Array<{ id: string; count: number; lastUsed: Date }>;
}

/**
 * Metrics summary with health status
 */
export interface MetricsSummary {
  totalPatterns: number;
  activePatterns: number;
  compressionRate: number;
  searchReductionRate: number;
  health: 'good' | 'warning' | 'poor';
}

/**
 * Library state for metrics collection
 */
export interface LibraryState {
  patterns: Array<{ id: string; usageCount: number }>;
  compressionHistory: number[];
  searchStats: { totalPruned: number; totalExplored: number };
}

/**
 * Export format type
 */
export type ExportFormat = 'json' | 'markdown';

/**
 * MetricsExporter interface
 */
export interface MetricsExporter {
  /**
   * Export metrics in specified format
   */
  export(metrics: LibraryMetrics, format: ExportFormat): string;

  /**
   * Collect metrics from library state
   */
  collectMetrics(state: LibraryState): LibraryMetrics;

  /**
   * Format metrics with human-readable values
   */
  formatMetrics(metrics: LibraryMetrics): FormattedMetrics;

  /**
   * Get summary with health status
   */
  getSummary(metrics: LibraryMetrics): MetricsSummary;
}

/**
 * Default MetricsExporter implementation
 */
class DefaultMetricsExporter implements MetricsExporter {
  /**
   * Export metrics in specified format
   */
  export(metrics: LibraryMetrics, format: ExportFormat): string {
    if (format !== 'json' && format !== 'markdown') {
      throw new Error(`Invalid export format: ${format}. Use 'json' or 'markdown'.`);
    }

    if (format === 'json') {
      return this.exportJson(metrics);
    }
    return this.exportMarkdown(metrics);
  }

  /**
   * Export as JSON
   */
  private exportJson(metrics: LibraryMetrics): string {
    return JSON.stringify(metrics, (_key, value) => {
      if (value instanceof Date) {
        return value.toISOString();
      }
      return value;
    }, 2);
  }

  /**
   * Export as Markdown
   */
  private exportMarkdown(metrics: LibraryMetrics): string {
    const formatted = this.formatMetrics(metrics);
    const summary = this.getSummary(metrics);
    
    const lines: string[] = [
      '# Pattern Library Metrics',
      '',
      `> Generated: ${metrics.lastUpdated.toISOString()}`,
      '',
      '## Summary',
      '',
      '| Metric | Value |',
      '|--------|-------|',
      `| Total Patterns | ${metrics.totalPatterns} |`,
      `| Active Patterns | ${metrics.activePatterns} |`,
      `| Utilization Rate | ${formatted.utilizationRate} |`,
      `| Compression Rate | ${formatted.compressionRateFormatted} |`,
      `| Search Reduction | ${formatted.searchReductionRateFormatted} |`,
      `| Hierarchy Depth | ${metrics.hierarchyDepth} |`,
      `| Health Status | ${summary.health} |`,
      '',
      '## Top Patterns by Usage',
      '',
      '| Pattern ID | Usage Count | Last Used |',
      '|------------|-------------|-----------|',
    ];

    for (const pattern of formatted.topPatterns.slice(0, 10)) {
      lines.push(`| ${pattern.id} | ${pattern.count} | ${pattern.lastUsed.toISOString().split('T')[0]} |`);
    }

    lines.push('');
    lines.push('## Hierarchy Levels');
    lines.push('');
    for (let i = 0; i < metrics.abstractionLevels.length; i++) {
      lines.push(`${i + 1}. ${metrics.abstractionLevels[i]}`);
    }

    return lines.join('\n');
  }

  /**
   * Collect metrics from library state
   */
  collectMetrics(state: LibraryState): LibraryMetrics {
    const patternUsage: Record<string, PatternUsageInfo> = {};
    let activeCount = 0;

    for (const pattern of state.patterns) {
      patternUsage[pattern.id] = {
        count: pattern.usageCount,
        lastUsed: new Date(),
      };
      if (pattern.usageCount > 0) {
        activeCount++;
      }
    }

    const compressionRate = state.compressionHistory.length > 0
      ? state.compressionHistory[state.compressionHistory.length - 1]
      : 0;

    const searchReductionRate = state.searchStats.totalExplored > 0
      ? state.searchStats.totalPruned / state.searchStats.totalExplored
      : 0;

    return {
      totalPatterns: state.patterns.length,
      activePatterns: activeCount,
      patternUsage,
      compressionRate,
      searchReductionRate,
      hierarchyDepth: 1,
      abstractionLevels: ['concrete'],
      lastUpdated: new Date(),
    };
  }

  /**
   * Format metrics with human-readable values
   */
  formatMetrics(metrics: LibraryMetrics): FormattedMetrics {
    const utilizationRate = metrics.totalPatterns > 0
      ? (metrics.activePatterns / metrics.totalPatterns) * 100
      : 0;

    const topPatterns = Object.entries(metrics.patternUsage)
      .map(([id, info]) => ({ id, count: info.count, lastUsed: info.lastUsed }))
      .sort((a, b) => b.count - a.count);

    return {
      compressionRateFormatted: `${(metrics.compressionRate * 100).toFixed(1)}%`,
      searchReductionRateFormatted: `${(metrics.searchReductionRate * 100).toFixed(1)}%`,
      utilizationRate: `${utilizationRate.toFixed(1)}%`,
      topPatterns,
    };
  }

  /**
   * Get summary with health status
   */
  getSummary(metrics: LibraryMetrics): MetricsSummary {
    let health: 'good' | 'warning' | 'poor';

    if (metrics.compressionRate >= 0.2 && metrics.searchReductionRate >= 0.7) {
      health = 'good';
    } else if (metrics.compressionRate >= 0.1 && metrics.searchReductionRate >= 0.5) {
      health = 'warning';
    } else {
      health = 'poor';
    }

    return {
      totalPatterns: metrics.totalPatterns,
      activePatterns: metrics.activePatterns,
      compressionRate: metrics.compressionRate,
      searchReductionRate: metrics.searchReductionRate,
      health,
    };
  }
}

/**
 * Create MetricsExporter instance
 */
export function createMetricsExporter(): MetricsExporter {
  return new DefaultMetricsExporter();
}

export { DefaultMetricsExporter };
