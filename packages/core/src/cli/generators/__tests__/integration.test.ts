/**
 * v3.3.0 Integration Tests
 *
 * Non-functional requirements tests for scaffold enhancement features
 *
 * @traceability REQ-NFR-001, REQ-NFR-002, REQ-NFR-003
 * @see TSK-NFR-001 - Performance Test
 * @see TSK-NFR-002 - Backward Compatibility
 * @see TSK-NFR-003 - E2E Integration
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { mkdir, rm } from 'fs/promises';
import { join } from 'path';
import { tmpdir } from 'os';
import {
  ValueObjectGenerator,
  StatusMachineGenerator,
  ResultAggregator,
  PatternAutoExtractor,
  PatternMerger,
  PatternLearningService,
  ExpertIntegration,
  createValueObjectGenerator,
  createStatusMachineGenerator,
  createResultAggregator,
  createPatternExtractor,
  createPatternMerger,
  createPatternLearningService,
  createExpertIntegration,
  type GeneratedFile,
} from '../index.js';

describe('v3.3.0 Non-Functional Requirements', () => {
  describe('TSK-NFR-001: Performance', () => {
    it('should generate 10 value objects in under 100ms', async () => {
      const generator = createValueObjectGenerator({
        domain: 'PERF',
        outputDir: tmpdir(),
        generateTests: false,
      });

      const specs = Array.from({ length: 10 }, (_, i) => ({
        name: `ValueObject${i}`,
      }));

      const startTime = performance.now();
      const files = await generator.generate(specs);
      const endTime = performance.now();

      const duration = endTime - startTime;
      expect(files).toHaveLength(10);
      expect(duration).toBeLessThan(100);
    });

    it('should generate 10 status machines in under 100ms', async () => {
      const generator = createStatusMachineGenerator({
        domain: 'PERF',
        outputDir: tmpdir(),
        generateTests: false,
      });

      const specs = Array.from({ length: 10 }, (_, i) => ({
        entityName: `Entity${i}`,
        initialStatus: 'draft',
      }));

      const startTime = performance.now();
      const files = await generator.generate(specs);
      const endTime = performance.now();

      const duration = endTime - startTime;
      expect(files).toHaveLength(10);
      expect(duration).toBeLessThan(100);
    });

    it('should extract patterns from 10 files in under 100ms', async () => {
      const extractor = createPatternExtractor({ minConfidence: 0.5 });

      const codeFiles = Array.from({ length: 10 }, (_, i) => ({
        content: `
          export interface Entity${i} {
            id: string;
            name: string;
          }
          
          export function createEntity${i}(name: string): Entity${i} {
            return { id: 'id', name };
          }
        `,
        path: `/test/entity${i}.ts`,
        domain: 'PERF',
      }));

      const startTime = performance.now();
      for (const file of codeFiles) {
        extractor.extractFromCode(file.content, file.path, file.domain);
      }
      const endTime = performance.now();

      const duration = endTime - startTime;
      expect(duration).toBeLessThan(100);
    });

    it('should merge 100 patterns in under 200ms', async () => {
      const merger = createPatternMerger();

      const patterns = Array.from({ length: 100 }, (_, i) => ({
        id: `pattern-${i}`,
        name: `Pattern${i}`,
        category: 'entity' as const,
        template: `interface Pattern${i} {}`,
        metadata: {
          sourceFile: `file${i}.ts`,
          extractedAt: new Date().toISOString(),
          domain: 'PERF',
          confidence: 0.8 + Math.random() * 0.2,
        },
        variables: [],
        examples: [],
      }));

      const startTime = performance.now();
      const result = merger.merge(patterns);
      const endTime = performance.now();

      const duration = endTime - startTime;
      expect(result).toBeDefined();
      expect(result.patterns).toBeDefined();
      expect(result.patterns.length).toBeGreaterThanOrEqual(0);
      expect(duration).toBeLessThan(200);
    });

    it('should learn from 50 files in under 500ms', async () => {
      const service = createPatternLearningService({ minConfidence: 0.5 });

      const files = Array.from({ length: 50 }, (_, i) => ({
        path: `/test/file${i}.ts`,
        content: `export interface Model${i} { id: string; }`,
        type: 'value-object' as const,
      }));

      const startTime = performance.now();
      const result = await service.learnFromGeneration(files);
      const endTime = performance.now();

      const duration = endTime - startTime;
      expect(result.executionTime).toBeGreaterThanOrEqual(0);
      expect(duration).toBeLessThan(500);
    });
  });

  describe('TSK-NFR-002: Backward Compatibility', () => {
    it('should support v3.2.0 CLI option format for value objects', async () => {
      // v3.2.0 format: -v "Price,Email" (comma-separated)
      const valueObjectsOption = 'Price,Email,Address';
      const parsed = valueObjectsOption.split(',').map((v) => v.trim());

      expect(parsed).toHaveLength(3);
      expect(parsed).toContain('Price');
      expect(parsed).toContain('Email');
      expect(parsed).toContain('Address');
    });

    it('should support ADR-v3.3.0-001 status option syntax', async () => {
      // ADR-v3.3.0-001: Support "Entity" or "Entity=status1,status2"
      const parsed1 = StatusMachineGenerator.parseStatusOption('Order');
      expect(parsed1.get('Order')).toBe(''); // No initial status = empty string

      const parsed2 = StatusMachineGenerator.parseStatusOption('Order=pending');
      expect(parsed2.get('Order')).toBe('pending');

      // Multiple entities
      const parsed3 = StatusMachineGenerator.parseStatusOption('Order,Payment=processing');
      expect(parsed3.has('Order')).toBe(true);
      expect(parsed3.get('Payment')).toBe('processing');
    });

    it('should maintain GeneratedFile interface compatibility', async () => {
      const generator = createValueObjectGenerator({
        domain: 'TEST',
        outputDir: '/test',
        generateTests: false,
      });

      const files = await generator.generate([{ name: 'Price' }]);

      // v3.2.0 compatible interface
      for (const file of files) {
        expect(file).toHaveProperty('path');
        expect(file).toHaveProperty('content');
        expect(file).toHaveProperty('type');
        expect(typeof file.path).toBe('string');
        expect(typeof file.content).toBe('string');
      }
    });

    it('should export all v3.2.0 types', async () => {
      // Verify exports are available
      expect(ValueObjectGenerator).toBeDefined();
      expect(StatusMachineGenerator).toBeDefined();
      expect(ResultAggregator).toBeDefined();
      expect(PatternAutoExtractor).toBeDefined();
      expect(PatternMerger).toBeDefined();
      expect(PatternLearningService).toBeDefined();
      expect(ExpertIntegration).toBeDefined();

      // Factory functions
      expect(createValueObjectGenerator).toBeDefined();
      expect(createStatusMachineGenerator).toBeDefined();
      expect(createResultAggregator).toBeDefined();
      expect(createPatternExtractor).toBeDefined();
      expect(createPatternMerger).toBeDefined();
      expect(createPatternLearningService).toBeDefined();
      expect(createExpertIntegration).toBeDefined();
    });
  });

  describe('TSK-NFR-003: End-to-End Integration', () => {
    const testDir = join(tmpdir(), `musubix-e2e-${Date.now()}`);

    beforeEach(async () => {
      try {
        await rm(testDir, { recursive: true, force: true });
      } catch {
        // Ignore cleanup errors
      }
      await mkdir(testDir, { recursive: true });
    });

    it('should complete Scaffold → Pattern → Expert workflow', async () => {
      // 1. Generate scaffold files
      const voGenerator = createValueObjectGenerator({
        domain: 'E2E',
        outputDir: testDir,
        generateTests: true,
      });

      const smGenerator = createStatusMachineGenerator({
        domain: 'E2E',
        outputDir: testDir,
        generateTests: true,
      });

      const voFiles = await voGenerator.generate([{ name: 'Price' }, { name: 'Email' }]);
      const smFiles = await smGenerator.generate([{ entityName: 'Order', initialStatus: 'draft' }]);

      // 2. Aggregate results
      const aggregator = createResultAggregator({ domain: 'E2E', outputDir: testDir });
      aggregator.addValueObjectFiles(voFiles);
      aggregator.addStatusMachineFiles(smFiles);

      const aggregated = aggregator.getResult();
      expect(aggregated.totalFiles).toBe(voFiles.length + smFiles.length);

      // 3. Extract patterns
      const extractor = createPatternExtractor({ minConfidence: 0.5 });
      const allFiles: GeneratedFile[] = [...voFiles, ...smFiles] as GeneratedFile[];

      for (const file of allFiles) {
        extractor.extractFromCode(file.content, file.path, 'E2E');
      }

      extractor.getResult();
      // May or may not extract patterns depending on code structure

      // 4. Learn from generation
      const learningService = createPatternLearningService({ minConfidence: 0.5 });
      const learnResult = await learningService.learnFromGeneration(allFiles as GeneratedFile[]);
      expect(learnResult.executionTime).toBeGreaterThanOrEqual(0);

      // 5. Consult expert (may fallback if not available)
      const expert = createExpertIntegration({ enabled: true });
      const recommendations = await expert.generateRecommendations(
        allFiles as GeneratedFile[],
        'E2E',
        'e2e-test-project'
      );
      expect(Array.isArray(recommendations)).toBe(true);

      // 6. Generate summary report
      const summary = aggregator.generateSummary('markdown');
      expect(summary).toContain('Generation');
    });

    it('should write and read generated files correctly', async () => {
      const generator = createValueObjectGenerator({
        domain: 'E2E',
        outputDir: testDir,
        generateTests: false,
      });

      const files = await generator.generate([{ name: 'Price' }]);
      await generator.writeFiles(files);

      // Verify file was written
      const { readFile: readFileSync } = await import('fs/promises');
      const priceContent = await readFileSync(files[0].path, 'utf-8');
      expect(priceContent).toContain('Price');
    });

    it('should maintain data integrity through pattern lifecycle', async () => {
      const learningService = createPatternLearningService({ enabled: true });

      // 1. Import initial patterns
      const initialData = {
        version: '1.0.0',
        exportedAt: new Date().toISOString(),
        patterns: [
          {
            id: 'test-pattern-1',
            pattern: {
              id: 'test-pattern-1',
              name: 'TestPattern',
              category: 'entity',
              template: 'interface {{name}} {}',
              metadata: {
                sourceFile: 'test.ts',
                extractedAt: new Date().toISOString(),
                domain: 'E2E',
                confidence: 0.9,
              },
              variables: [],
              examples: [],
            },
            usageCount: 3,
            lastUsed: new Date().toISOString(),
            successRate: 0.85,
            feedback: [],
          },
        ],
      };

      const importResult = learningService.importLibrary(JSON.stringify(initialData));
      expect(importResult.imported).toBe(1);

      // 2. Export and verify integrity
      const exported = learningService.exportLibrary();
      const parsedExport = JSON.parse(exported);

      expect(parsedExport.patterns).toHaveLength(1);
      expect(parsedExport.patterns[0].id).toBe('test-pattern-1');

      // 3. Clear and re-import
      learningService.clearLibrary();
      expect(learningService.getAllPatterns()).toHaveLength(0);

      const reimportResult = learningService.importLibrary(exported);
      expect(reimportResult.imported).toBe(1);
    });

    it('should handle error conditions gracefully', async () => {
      // Invalid extractor input
      const extractor = createPatternExtractor();
      const patterns = extractor.extractFromCode('', '', '');
      expect(patterns).toHaveLength(0);

      // Empty merger input - should return empty result
      const merger = createPatternMerger();
      const mergeResult = merger.merge([]);
      expect(mergeResult).toBeDefined();
      expect(mergeResult.patterns).toHaveLength(0);

      // Invalid learning service input
      const service = createPatternLearningService();
      const learnResult = await service.learnFromGeneration([]);
      expect(learnResult.extractedPatterns).toHaveLength(0);

      // Invalid JSON import
      const importResult = service.importLibrary('not valid json');
      expect(importResult.imported).toBe(0);
    });
  });
});
