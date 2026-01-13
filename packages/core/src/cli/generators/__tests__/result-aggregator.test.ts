/**
 * Result Aggregator Tests
 *
 * @traceability REQ-SCF-006
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { ResultAggregator, createResultAggregator } from '../result-aggregator.js';
import type { GeneratedFile } from '../value-object-generator.js';

describe('ResultAggregator', () => {
  let aggregator: ResultAggregator;
  const testConfig = {
    domain: 'TEST',
    outputDir: '/tmp/test-project',
  };

  beforeEach(() => {
    aggregator = createResultAggregator(testConfig);
  });

  describe('addValueObjectFiles', () => {
    it('should separate VO files and test files', () => {
      const files: GeneratedFile[] = [
        { path: '/tmp/test-project/src/value-objects/price.ts', content: '...', type: 'value-object' },
        { path: '/tmp/test-project/__tests__/price.test.ts', content: '...', type: 'test' },
      ];

      aggregator.addValueObjectFiles(files);
      const result = aggregator.getResult();

      expect(result.byType.valueObjects).toHaveLength(1);
      expect(result.byType.tests).toHaveLength(1);
    });
  });

  describe('addStatusMachineFiles', () => {
    it('should separate SM files and test files', () => {
      const files: GeneratedFile[] = [
        { path: '/tmp/test-project/src/statuses/order-status.ts', content: '...', type: 'status-machine' as 'value-object' },
        { path: '/tmp/test-project/__tests__/order-status.test.ts', content: '...', type: 'test' },
      ];

      aggregator.addStatusMachineFiles(files);
      const result = aggregator.getResult();

      expect(result.byType.statusMachines).toHaveLength(1);
      expect(result.byType.tests).toHaveLength(1);
    });
  });

  describe('getResult', () => {
    it('should return aggregated result with correct totals', () => {
      const voFiles: GeneratedFile[] = [
        { path: '/tmp/test-project/src/value-objects/price.ts', content: '...', type: 'value-object' },
        { path: '/tmp/test-project/__tests__/price.test.ts', content: '...', type: 'test' },
      ];
      const smFiles: GeneratedFile[] = [
        { path: '/tmp/test-project/src/statuses/order-status.ts', content: '...', type: 'value-object' },
        { path: '/tmp/test-project/__tests__/order-status.test.ts', content: '...', type: 'test' },
      ];

      aggregator.addValueObjectFiles(voFiles);
      aggregator.addStatusMachineFiles(smFiles);
      const result = aggregator.getResult();

      expect(result.totalFiles).toBe(4);
      expect(result.domain).toBe('TEST');
      expect(result.outputDir).toBe('/tmp/test-project');
      expect(result.success).toBe(true);
    });

    it('should mark success as false when errors exist', () => {
      aggregator.addError('Test error');
      const result = aggregator.getResult();

      expect(result.success).toBe(false);
      expect(result.errors).toContain('Test error');
    });

    it('should include warnings in result', () => {
      aggregator.addWarning('Test warning');
      const result = aggregator.getResult();

      expect(result.success).toBe(true);
      expect(result.warnings).toContain('Test warning');
    });
  });

  describe('generateSummary', () => {
    beforeEach(() => {
      const files: GeneratedFile[] = [
        { path: '/tmp/test-project/src/value-objects/price.ts', content: '...', type: 'value-object' },
        { path: '/tmp/test-project/__tests__/price.test.ts', content: '...', type: 'test' },
      ];
      aggregator.addValueObjectFiles(files);
    });

    it('should generate JSON summary', () => {
      const summary = aggregator.generateSummary('json');
      const parsed = JSON.parse(summary);

      expect(parsed.domain).toBe('TEST');
      expect(parsed.totalFiles).toBe(2);
      expect(parsed.byType.valueObjects).toHaveLength(1);
    });

    it('should generate Markdown summary', () => {
      const summary = aggregator.generateSummary('markdown');

      expect(summary).toContain('# Scaffold Generation Summary');
      expect(summary).toContain('**Domain**: TEST');
      expect(summary).toContain('Value Objects');
      expect(summary).toContain('| Value Objects | 1 |');
    });

    it('should generate console summary', () => {
      const summary = aggregator.generateSummary('console');

      expect(summary).toContain('Scaffold Generation');
      expect(summary).toContain('Domain:      TEST');
      expect(summary).toContain('Value Objects:   1');
    });

    it('should default to console format', () => {
      const summary = aggregator.generateSummary();

      expect(summary).toContain('Scaffold Generation');
    });
  });

  describe('getAllFilePaths', () => {
    it('should return relative file paths', () => {
      const files: GeneratedFile[] = [
        { path: '/tmp/test-project/src/value-objects/price.ts', content: '...', type: 'value-object' },
        { path: '/tmp/test-project/__tests__/price.test.ts', content: '...', type: 'test' },
      ];
      aggregator.addValueObjectFiles(files);

      const paths = aggregator.getAllFilePaths();

      expect(paths).toContain('src/value-objects/price.ts');
      expect(paths).toContain('__tests__/price.test.ts');
    });
  });

  describe('addOtherFiles', () => {
    it('should add other files to result', () => {
      const files: GeneratedFile[] = [
        { path: '/tmp/test-project/src/index.ts', content: '...', type: 'index' as 'value-object' },
      ];
      aggregator.addOtherFiles(files);

      const result = aggregator.getResult();
      expect(result.byType.other).toHaveLength(1);
    });
  });

  describe('error and warning handling', () => {
    it('should collect multiple errors', () => {
      aggregator.addError('Error 1');
      aggregator.addError('Error 2');

      const result = aggregator.getResult();
      expect(result.errors).toHaveLength(2);
      expect(result.success).toBe(false);
    });

    it('should collect multiple warnings', () => {
      aggregator.addWarning('Warning 1');
      aggregator.addWarning('Warning 2');

      const result = aggregator.getResult();
      expect(result.warnings).toHaveLength(2);
      expect(result.success).toBe(true);
    });

    it('should include errors in markdown summary', () => {
      aggregator.addError('Test error');
      const summary = aggregator.generateSummary('markdown');

      expect(summary).toContain('## Errors');
      expect(summary).toContain('Test error');
    });

    it('should include warnings in markdown summary', () => {
      aggregator.addWarning('Test warning');
      const summary = aggregator.generateSummary('markdown');

      expect(summary).toContain('## Warnings');
      expect(summary).toContain('Test warning');
    });
  });
});
