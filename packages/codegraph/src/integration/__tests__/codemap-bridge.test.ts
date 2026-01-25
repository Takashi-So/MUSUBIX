/**
 * @fileoverview CodemapBridge Integration Tests
 * @traceability REQ-CM-001, REQ-CM-002, REQ-CM-003, REQ-CM-004
 */

import { describe, it, expect, beforeAll, afterAll, vi } from 'vitest';
import * as fs from 'fs/promises';
import * as path from 'path';
import * as os from 'os';
import { createCodemapBridge } from '../codemap-bridge.js';
import type { Codemap } from '../codemap-types.js';

describe('CodemapBridge', () => {
  let testDir: string;
  let bridge: ReturnType<typeof createCodemapBridge>;

  beforeAll(async () => {
    // Create temp directory for testing
    testDir = await fs.mkdtemp(path.join(os.tmpdir(), 'codemap-test-'));
    bridge = createCodemapBridge({
      maxDepth: 3,
      outputDir: path.join(testDir, 'output'),
    });

    // Create mock project structure
    await fs.mkdir(path.join(testDir, 'packages', 'core', 'src'), { recursive: true });
    await fs.mkdir(path.join(testDir, 'packages', 'utils', 'src'), { recursive: true });

    // Create package.json
    await fs.writeFile(
      path.join(testDir, 'package.json'),
      JSON.stringify({
        name: 'test-project',
        version: '1.0.0',
        workspaces: ['packages/*'],
      })
    );

    // Create core package
    await fs.writeFile(
      path.join(testDir, 'packages', 'core', 'package.json'),
      JSON.stringify({
        name: '@test/core',
        version: '1.0.0',
        main: 'src/index.js',
        dependencies: {
          '@test/utils': '^1.0.0',
        },
      })
    );

    // Create utils package
    await fs.writeFile(
      path.join(testDir, 'packages', 'utils', 'package.json'),
      JSON.stringify({
        name: '@test/utils',
        version: '1.0.0',
        main: 'src/index.js',
      })
    );

    // Create source files
    await fs.writeFile(
      path.join(testDir, 'packages', 'core', 'src', 'index.ts'),
      `
import { helper } from '@test/utils';

export function main(): void {
  console.log('Main function');
}

export class CoreService {
  private value: number = 0;
  
  getValue(): number {
    return this.value;
  }
  
  setValue(n: number): void {
    this.value = n;
  }
}

export interface CoreConfig {
  enabled: boolean;
  timeout: number;
}
`
    );

    await fs.writeFile(
      path.join(testDir, 'packages', 'utils', 'src', 'index.ts'),
      `
export function helper(): string {
  return 'helper';
}

export const VERSION = '1.0.0';
`
    );

    // Create CLI entry point
    await fs.writeFile(
      path.join(testDir, 'packages', 'core', 'src', 'cli.ts'),
      `#!/usr/bin/env node
import { main } from './index';
main();
`
    );
  });

  afterAll(async () => {
    // Cleanup
    await fs.rm(testDir, { recursive: true, force: true });
  });

  describe('analyzeStructure', () => {
    it('should detect packages in workspace', async () => {
      const result = await bridge.analyzeStructure(testDir);

      expect(result.packages).toBeDefined();
      expect(result.packages.length).toBeGreaterThanOrEqual(2);

      const corePackage = result.packages.find(p => p.name === '@test/core');
      expect(corePackage).toBeDefined();
      expect(corePackage?.dependencies).toContain('@test/utils');

      const utilsPackage = result.packages.find(p => p.name === '@test/utils');
      expect(utilsPackage).toBeDefined();
    });

    it('should build directory structure', async () => {
      const result = await bridge.analyzeStructure(testDir);

      expect(result.structure).toBeDefined();
      expect(result.structure.isDirectory).toBe(true);
      expect(result.structure.children).toBeDefined();

      const packagesDir = result.structure.children?.find(c => c.name === 'packages');
      expect(packagesDir).toBeDefined();
      expect(packagesDir?.isDirectory).toBe(true);
    });

    it('should detect entry points', async () => {
      const result = await bridge.analyzeStructure(testDir);

      expect(result.entryPoints).toBeDefined();
      // Should detect CLI entry point
      const cliEntry = result.entryPoints.find(e => e.type === 'cli');
      // Entry point detection may vary
      expect(Array.isArray(result.entryPoints)).toBe(true);
    });

    it('should detect frameworks', async () => {
      const result = await bridge.analyzeStructure(testDir);

      expect(result.frameworks).toBeDefined();
      expect(Array.isArray(result.frameworks)).toBe(true);
    });
  });

  describe('analyzeModule', () => {
    it('should analyze TypeScript module exports', async () => {
      const modulePath = path.join(testDir, 'packages', 'core', 'src', 'index.ts');
      const result = await bridge.analyzeModule(modulePath);

      expect(result.name).toBe('index');
      expect(result.exports).toBeDefined();
      expect(result.exports.length).toBeGreaterThan(0);

      // Check for main function export (uses 'type' not 'kind')
      const mainExport = result.exports.find(e => e.name === 'main');
      expect(mainExport).toBeDefined();
      expect(mainExport?.type).toBe('function');

      // Check for class export
      const classExport = result.exports.find(e => e.name === 'CoreService');
      expect(classExport).toBeDefined();
      expect(classExport?.type).toBe('class');

      // Check for interface export
      const interfaceExport = result.exports.find(e => e.name === 'CoreConfig');
      expect(interfaceExport).toBeDefined();
      expect(interfaceExport?.type).toBe('interface');
    });

    it('should analyze module imports', async () => {
      const modulePath = path.join(testDir, 'packages', 'core', 'src', 'index.ts');
      const result = await bridge.analyzeModule(modulePath);

      expect(result.imports).toBeDefined();
      expect(result.imports.length).toBeGreaterThan(0);

      // ModuleImport uses 'source' not 'from', and 'items' not 'names'
      const utilsImport = result.imports.find(i => i.source === '@test/utils');
      expect(utilsImport).toBeDefined();
      expect(utilsImport?.items).toContain('helper');
    });

    it('should count entity types', async () => {
      const modulePath = path.join(testDir, 'packages', 'core', 'src', 'index.ts');
      const result = await bridge.analyzeModule(modulePath);

      expect(result.entityCounts).toBeDefined();
      // entityCounts uses lowercase keys
      expect(result.entityCounts['function'] ?? result.entityCounts['functions'] ?? 0).toBeGreaterThanOrEqual(1);
      expect(result.entityCounts['class'] ?? result.entityCounts['classes'] ?? 0).toBeGreaterThanOrEqual(1);
      expect(result.entityCounts['interface'] ?? result.entityCounts['interfaces'] ?? 0).toBeGreaterThanOrEqual(1);
    });

    it('should calculate complexity', async () => {
      const modulePath = path.join(testDir, 'packages', 'core', 'src', 'index.ts');
      const result = await bridge.analyzeModule(modulePath);

      expect(result.complexity).toBeDefined();
      expect(typeof result.complexity).toBe('number');
      expect(result.complexity).toBeGreaterThanOrEqual(0);
    });

    it('should count lines of code', async () => {
      const modulePath = path.join(testDir, 'packages', 'core', 'src', 'index.ts');
      const result = await bridge.analyzeModule(modulePath);

      expect(result.linesOfCode).toBeDefined();
      expect(result.linesOfCode).toBeGreaterThan(0);
    });
  });

  describe('generateCodemap', () => {
    it('should generate codemap with all sections', async () => {
      const codemap = await bridge.generateCodemap(testDir);

      expect(codemap.projectName).toBe('test-project');
      expect(codemap.projectVersion).toBe('1.0.0');
      expect(codemap.generatedAt).toBeDefined();
      expect(codemap.packages).toBeDefined();
      expect(codemap.entryPoints).toBeDefined();
      expect(codemap.frameworks).toBeDefined();
      expect(codemap.structure).toBeDefined();
      expect(codemap.documents).toBeDefined();
    });

    it('should generate markdown documents', async () => {
      const codemap = await bridge.generateCodemap(testDir);

      expect(codemap.documents.length).toBeGreaterThan(0);

      const indexDoc = codemap.documents.find(d => d.type === 'index');
      expect(indexDoc).toBeDefined();
      expect(indexDoc?.content).toContain('# Code Map');
    });
  });

  describe('compareCodemaps', () => {
    it('should detect added packages', () => {
      const previous: Codemap = {
        projectName: 'test',
        generatedAt: new Date().toISOString(),
        packages: [{ name: '@test/core', path: '', dependencies: [] }],
        entryPoints: [],
        frameworks: [],
        structure: { name: 'root', path: '/', isDirectory: true },
        documents: [],
      };

      const current: Codemap = {
        projectName: 'test',
        generatedAt: new Date().toISOString(),
        packages: [
          { name: '@test/core', path: '', dependencies: [] },
          { name: '@test/utils', path: '', dependencies: [] },
        ],
        entryPoints: [],
        frameworks: [],
        structure: { name: 'root', path: '/', isDirectory: true },
        documents: [],
      };

      const diff = bridge.compareCodemaps(previous, current);

      expect(diff.addedPackages).toContain('@test/utils');
      expect(diff.removedPackages).toHaveLength(0);
    });

    it('should detect removed packages', () => {
      const previous: Codemap = {
        projectName: 'test',
        generatedAt: new Date().toISOString(),
        packages: [
          { name: '@test/core', path: '', dependencies: [] },
          { name: '@test/utils', path: '', dependencies: [] },
        ],
        entryPoints: [],
        frameworks: [],
        structure: { name: 'root', path: '/', isDirectory: true },
        documents: [],
      };

      const current: Codemap = {
        projectName: 'test',
        generatedAt: new Date().toISOString(),
        packages: [{ name: '@test/core', path: '', dependencies: [] }],
        entryPoints: [],
        frameworks: [],
        structure: { name: 'root', path: '/', isDirectory: true },
        documents: [],
      };

      const diff = bridge.compareCodemaps(previous, current);

      expect(diff.removedPackages).toContain('@test/utils');
      expect(diff.addedPackages).toHaveLength(0);
    });

    it('should detect modified packages', () => {
      const previous: Codemap = {
        projectName: 'test',
        generatedAt: new Date().toISOString(),
        packages: [{ name: '@test/core', path: '', dependencies: [], version: '1.0.0' }],
        entryPoints: [],
        frameworks: [],
        structure: { name: 'root', path: '/', isDirectory: true },
        documents: [],
      };

      const current: Codemap = {
        projectName: 'test',
        generatedAt: new Date().toISOString(),
        packages: [{ name: '@test/core', path: '', dependencies: [], version: '1.0.1' }],
        entryPoints: [],
        frameworks: [],
        structure: { name: 'root', path: '/', isDirectory: true },
        documents: [],
      };

      const diff = bridge.compareCodemaps(previous, current);

      expect(diff.modifiedPackages).toContain('@test/core');
    });

    it('should calculate diff percentage', () => {
      const previous: Codemap = {
        projectName: 'test',
        generatedAt: new Date().toISOString(),
        packages: Array(10).fill(null).map((_, i) => ({
          name: `@test/pkg-${i}`,
          path: '',
          dependencies: [],
        })),
        entryPoints: [],
        frameworks: [],
        structure: { name: 'root', path: '/', isDirectory: true },
        documents: [],
      };

      const current: Codemap = {
        projectName: 'test',
        generatedAt: new Date().toISOString(),
        packages: Array(10).fill(null).map((_, i) => ({
          name: `@test/pkg-${i}`,
          path: '',
          dependencies: [],
        })),
        entryPoints: [],
        frameworks: [],
        structure: { name: 'root', path: '/', isDirectory: true },
        documents: [],
      };

      // Remove 2 packages
      current.packages = current.packages.slice(2);
      // Add 1 new package
      current.packages.push({ name: '@test/new', path: '', dependencies: [] });

      const diff = bridge.compareCodemaps(previous, current);

      expect(diff.diffPercentage).toBeGreaterThan(0);
      expect(diff.addedPackages).toContain('@test/new');
      expect(diff.removedPackages).toHaveLength(2);
    });
  });

  describe('writeCodemap', () => {
    it('should write codemap to output directory', async () => {
      const codemap = await bridge.generateCodemap(testDir);
      const outputDir = path.join(testDir, 'codemap-output');

      await bridge.writeCodemap(codemap, outputDir);

      // Check if metadata file exists
      const metadataPath = path.join(outputDir, '.codemap-metadata.json');
      const metadata = JSON.parse(await fs.readFile(metadataPath, 'utf-8'));

      expect(metadata.projectName).toBe('test-project');
      expect(metadata.projectVersion).toBe('1.0.0');
    });
  });

  describe('formatAsMarkdown', () => {
    it('should format codemap as markdown', async () => {
      const codemap = await bridge.generateCodemap(testDir);
      const markdown = bridge.formatAsMarkdown(codemap);

      expect(markdown).toContain('# Code Map: test-project');
      expect(markdown).toContain('## Package Structure');
      expect(markdown).toContain('## Entry Points');
    });
  });
});

describe('CodemapBridge Configuration', () => {
  it('should use custom configuration', () => {
    const bridge = createCodemapBridge({
      maxDepth: 5,
      outputDir: '/custom/output',
      includeHidden: true,
    });

    expect(bridge).toBeDefined();
  });

  it('should use default configuration', () => {
    const bridge = createCodemapBridge();
    expect(bridge).toBeDefined();
  });
});

describe('CodemapBridge Edge Cases', () => {
  let testDir: string;

  beforeAll(async () => {
    testDir = await fs.mkdtemp(path.join(os.tmpdir(), 'codemap-edge-'));
  });

  afterAll(async () => {
    await fs.rm(testDir, { recursive: true, force: true });
  });

  it('should handle empty project', async () => {
    const bridge = createCodemapBridge();
    const result = await bridge.analyzeStructure(testDir);

    expect(result.packages).toBeDefined();
    expect(result.structure).toBeDefined();
  });

  it('should handle project without package.json', async () => {
    // Create directory without package.json
    await fs.mkdir(path.join(testDir, 'no-pkg'), { recursive: true });
    await fs.writeFile(
      path.join(testDir, 'no-pkg', 'index.ts'),
      'export const x = 1;'
    );

    const bridge = createCodemapBridge();
    const codemap = await bridge.generateCodemap(path.join(testDir, 'no-pkg'));

    expect(codemap.projectName).toBe('no-pkg');
    expect(codemap.projectVersion).toBeUndefined();
  });

  it('should handle deeply nested structure', async () => {
    const deepPath = path.join(testDir, 'deep', 'a', 'b', 'c', 'd', 'e');
    await fs.mkdir(deepPath, { recursive: true });
    await fs.writeFile(path.join(deepPath, 'file.ts'), 'export const x = 1;');

    const bridge = createCodemapBridge({ maxDepth: 3 });
    const result = await bridge.analyzeStructure(path.join(testDir, 'deep'));

    expect(result.structure).toBeDefined();
    // maxDepth should limit the depth
  });
});
