/**
 * MetricsExporter Tests
 * 
 * @see TSK-LL-108 - MetricsExporter実装
 * @see REQ-LL-108 - メトリクスエクスポート要件
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  MetricsExporter,
  createMetricsExporter,
  type LibraryMetrics,
  type ExportFormat,
} from '../../src/metrics/MetricsExporter.js';

describe('MetricsExporter', () => {
  let exporter: MetricsExporter;
  let sampleMetrics: LibraryMetrics;

  beforeEach(() => {
    exporter = createMetricsExporter();
    sampleMetrics = {
      totalPatterns: 150,
      activePatterns: 120,
      patternUsage: {
        'PAT-001': { count: 45, lastUsed: new Date('2026-01-08') },
        'PAT-002': { count: 30, lastUsed: new Date('2026-01-07') },
        'PAT-003': { count: 15, lastUsed: new Date('2026-01-06') },
      },
      compressionRate: 0.35,
      searchReductionRate: 0.92,
      hierarchyDepth: 4,
      abstractionLevels: ['concrete', 'generic', 'abstract', 'meta'],
      lastUpdated: new Date('2026-01-08T12:00:00Z'),
    };
  });

  describe('Interface Definition', () => {
    it('should have export method', () => {
      expect(typeof exporter.export).toBe('function');
    });

    it('should have collectMetrics method', () => {
      expect(typeof exporter.collectMetrics).toBe('function');
    });

    it('should have formatMetrics method', () => {
      expect(typeof exporter.formatMetrics).toBe('function');
    });

    it('should have getSummary method', () => {
      expect(typeof exporter.getSummary).toBe('function');
    });
  });

  describe('JSON Export', () => {
    it('should export metrics as JSON string', () => {
      const result = exporter.export(sampleMetrics, 'json');
      
      expect(typeof result).toBe('string');
      const parsed = JSON.parse(result);
      expect(parsed.totalPatterns).toBe(150);
      expect(parsed.compressionRate).toBe(0.35);
    });

    it('should include all metric fields in JSON', () => {
      const result = exporter.export(sampleMetrics, 'json');
      const parsed = JSON.parse(result);
      
      expect(parsed).toHaveProperty('totalPatterns');
      expect(parsed).toHaveProperty('activePatterns');
      expect(parsed).toHaveProperty('patternUsage');
      expect(parsed).toHaveProperty('compressionRate');
      expect(parsed).toHaveProperty('searchReductionRate');
      expect(parsed).toHaveProperty('hierarchyDepth');
    });

    it('should format JSON with indentation', () => {
      const result = exporter.export(sampleMetrics, 'json');
      
      expect(result).toContain('\n');
      expect(result).toContain('  ');
    });

    it('should handle empty metrics', () => {
      const emptyMetrics: LibraryMetrics = {
        totalPatterns: 0,
        activePatterns: 0,
        patternUsage: {},
        compressionRate: 0,
        searchReductionRate: 0,
        hierarchyDepth: 0,
        abstractionLevels: [],
        lastUpdated: new Date(),
      };
      
      const result = exporter.export(emptyMetrics, 'json');
      const parsed = JSON.parse(result);
      expect(parsed.totalPatterns).toBe(0);
    });
  });

  describe('Markdown Export', () => {
    it('should export metrics as Markdown string', () => {
      const result = exporter.export(sampleMetrics, 'markdown');
      
      expect(typeof result).toBe('string');
      expect(result).toContain('#');
      expect(result).toContain('Pattern Library Metrics');
    });

    it('should include summary section', () => {
      const result = exporter.export(sampleMetrics, 'markdown');
      
      expect(result).toContain('## Summary');
      expect(result).toContain('150');
      expect(result).toContain('120');
    });

    it('should include compression rate as percentage', () => {
      const result = exporter.export(sampleMetrics, 'markdown');
      
      expect(result).toContain('35.0%');
    });

    it('should include search reduction rate', () => {
      const result = exporter.export(sampleMetrics, 'markdown');
      
      expect(result).toContain('92.0%');
    });

    it('should include pattern usage table', () => {
      const result = exporter.export(sampleMetrics, 'markdown');
      
      expect(result).toContain('PAT-001');
      expect(result).toContain('45');
      expect(result).toContain('|');
    });

    it('should include hierarchy information', () => {
      const result = exporter.export(sampleMetrics, 'markdown');
      
      expect(result).toContain('Hierarchy');
      expect(result).toContain('4');
    });
  });

  describe('Format Metrics', () => {
    it('should format compression rate as percentage', () => {
      const formatted = exporter.formatMetrics(sampleMetrics);
      
      expect(formatted.compressionRateFormatted).toBe('35.0%');
    });

    it('should format search reduction rate as percentage', () => {
      const formatted = exporter.formatMetrics(sampleMetrics);
      
      expect(formatted.searchReductionRateFormatted).toBe('92.0%');
    });

    it('should calculate pattern utilization rate', () => {
      const formatted = exporter.formatMetrics(sampleMetrics);
      
      expect(formatted.utilizationRate).toBe('80.0%');
    });

    it('should sort patterns by usage count', () => {
      const formatted = exporter.formatMetrics(sampleMetrics);
      
      expect(formatted.topPatterns[0].id).toBe('PAT-001');
      expect(formatted.topPatterns[0].count).toBe(45);
    });
  });

  describe('Get Summary', () => {
    it('should return summary object', () => {
      const summary = exporter.getSummary(sampleMetrics);
      
      expect(summary).toHaveProperty('totalPatterns');
      expect(summary).toHaveProperty('activePatterns');
      expect(summary).toHaveProperty('compressionRate');
      expect(summary).toHaveProperty('searchReductionRate');
    });

    it('should include health status', () => {
      const summary = exporter.getSummary(sampleMetrics);
      
      expect(summary.health).toBe('good');
    });

    it('should detect poor health when compression rate is low', () => {
      const poorMetrics: LibraryMetrics = {
        ...sampleMetrics,
        compressionRate: 0.05,
        searchReductionRate: 0.3,
      };
      
      const summary = exporter.getSummary(poorMetrics);
      expect(summary.health).toBe('poor');
    });

    it('should detect warning health state', () => {
      const warningMetrics: LibraryMetrics = {
        ...sampleMetrics,
        compressionRate: 0.15,
        searchReductionRate: 0.6,
      };
      
      const summary = exporter.getSummary(warningMetrics);
      expect(summary.health).toBe('warning');
    });
  });

  describe('Collect Metrics', () => {
    it('should collect metrics from library state', () => {
      const libraryState = {
        patterns: [
          { id: 'PAT-001', usageCount: 10 },
          { id: 'PAT-002', usageCount: 5 },
        ],
        compressionHistory: [0.2, 0.25, 0.3],
        searchStats: { totalPruned: 900, totalExplored: 1000 },
      };
      
      const metrics = exporter.collectMetrics(libraryState);
      
      expect(metrics.totalPatterns).toBe(2);
      expect(metrics.compressionRate).toBe(0.3);
      expect(metrics.searchReductionRate).toBe(0.9);
    });
  });

  describe('Export Format Validation', () => {
    it('should accept json format', () => {
      expect(() => exporter.export(sampleMetrics, 'json')).not.toThrow();
    });

    it('should accept markdown format', () => {
      expect(() => exporter.export(sampleMetrics, 'markdown')).not.toThrow();
    });

    it('should throw for invalid format', () => {
      expect(() => exporter.export(sampleMetrics, 'invalid' as ExportFormat)).toThrow();
    });
  });
});
