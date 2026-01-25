/**
 * Codemap Tests
 *
 * @see REQ-CM-001〜004
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createCodemapManager,
  formatCodemapResultMarkdown,
  type CodemapConfig,
  type CodemapGenerationResult,
  DEFAULT_CODEMAP_CONFIG,
} from '../codemap/index.js';

describe('CodemapManager', () => {
  let manager: ReturnType<typeof createCodemapManager>;

  beforeEach(() => {
    manager = createCodemapManager();
  });

  describe('createCodemapManager', () => {
    it('should create manager with default config', () => {
      expect(manager).toBeDefined();
      const config = manager.getConfig();
      expect(config.projectRoot).toBe(DEFAULT_CODEMAP_CONFIG.projectRoot);
      expect(config.outputDir).toBe(DEFAULT_CODEMAP_CONFIG.outputDir);
    });

    it('should create manager with custom config', () => {
      const customConfig: Partial<CodemapConfig> = {
        projectRoot: '/custom/root',
        outputDir: '/custom/output',
      };
      const customManager = createCodemapManager(customConfig);
      const config = customManager.getConfig();
      expect(config.projectRoot).toBe('/custom/root');
      expect(config.outputDir).toBe('/custom/output');
    });
  });

  describe('analyzeRepository', () => {
    it('should analyze repository structure', async () => {
      const structure = await manager.analyzeRepository();

      expect(structure.directories).toBeDefined();
      expect(structure.entryPoints).toBeDefined();
    });
  });

  describe('analyzeModule', () => {
    it('should analyze module', async () => {
      const analysis = await manager.analyzeModule('src/index.ts');

      expect(analysis.path).toBe('src/index.ts');
      expect(analysis.exports).toBeDefined();
      expect(analysis.imports).toBeDefined();
    });
  });

  describe('generateCodemap', () => {
    it('should generate codemap document', async () => {
      const result = await manager.generateCodemap();

      expect(result.documents).toBeDefined();
      expect(result.diffs).toBeDefined();
    });
  });

  describe('calculateDiff', () => {
    it('should calculate diff between contents', () => {
      const diff = manager.calculateDiff('new content', 'old content');

      expect(diff.diffPercent).toBeDefined();
      expect(diff.additions).toBeDefined();
      expect(diff.deletions).toBeDefined();
    });
  });

  describe('saveCodemap', () => {
    it('should save codemap documents', async () => {
      const result: CodemapGenerationResult = {
        documents: [
          {
            name: 'CODEMAP.md',
            path: 'docs/CODEMAPS/CODEMAP.md',
            content: '# Codemap',
            generatedAt: new Date(),
          },
        ],
        diffs: [],
        totalDiffPercent: 0,
        generatedAt: new Date(),
      };

      const savedPaths = await manager.saveCodemap(result);

      expect(savedPaths).toBeInstanceOf(Array);
    });
  });
});

describe('Format functions', () => {
  it('should format codemap result as markdown', () => {
    const result: CodemapGenerationResult = {
      documents: [
        {
          name: 'CODEMAP.md',
          path: 'docs/CODEMAPS/CODEMAP.md',
          content: '# Codemap',
          generatedAt: new Date(),
        },
      ],
      diffs: [],
      totalDiffPercent: 0,
      generatedAt: new Date(),
    };

    const markdown = formatCodemapResultMarkdown(result);
    expect(markdown).toContain('Codemap');
  });
});
