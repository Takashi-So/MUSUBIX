/**
 * @fileoverview Dependency Parser Unit Tests
 * @module @nahisaho/musubix-security/tests/cve/dependency-parser.test
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs';
import * as path from 'node:path';
import * as os from 'node:os';
import {
  DependencyParser,
  resolveVersionSpecifier,
  filterDependenciesForScanning,
  getUniquePackages,
} from '../../src/cve/dependency-parser.js';
import type { ParsedDependency } from '../../src/cve/dependency-parser.js';

describe('DependencyParser', () => {
  describe('parsePackageJson', () => {
    it('should parse dependencies', () => {
      const packageJson = JSON.stringify({
        name: 'test-project',
        dependencies: {
          express: '^4.18.0',
          lodash: '4.17.21',
        },
      });

      const parser = new DependencyParser();
      const deps = parser.parsePackageJson(packageJson);

      expect(deps).toHaveLength(2);
      expect(deps.find((d) => d.name === 'express')).toMatchObject({
        name: 'express',
        versionSpecifier: '^4.18.0',
        type: 'dependencies',
        isDirect: true,
      });
    });

    it('should parse devDependencies by default', () => {
      const packageJson = JSON.stringify({
        devDependencies: {
          vitest: '^1.0.0',
        },
      });

      const parser = new DependencyParser();
      const deps = parser.parsePackageJson(packageJson);

      expect(deps).toHaveLength(1);
      expect(deps[0].type).toBe('devDependencies');
    });

    it('should exclude devDependencies when configured', () => {
      const packageJson = JSON.stringify({
        dependencies: { express: '^4.0.0' },
        devDependencies: { vitest: '^1.0.0' },
      });

      const parser = new DependencyParser({ includeDevDependencies: false });
      const deps = parser.parsePackageJson(packageJson);

      expect(deps).toHaveLength(1);
      expect(deps[0].name).toBe('express');
    });

    it('should exclude peerDependencies by default', () => {
      const packageJson = JSON.stringify({
        dependencies: { express: '^4.0.0' },
        peerDependencies: { react: '^18.0.0' },
      });

      const parser = new DependencyParser();
      const deps = parser.parsePackageJson(packageJson);

      expect(deps).toHaveLength(1);
      expect(deps[0].name).toBe('express');
    });

    it('should include peerDependencies when configured', () => {
      const packageJson = JSON.stringify({
        dependencies: { express: '^4.0.0' },
        peerDependencies: { react: '^18.0.0' },
      });

      const parser = new DependencyParser({ includePeerDependencies: true });
      const deps = parser.parsePackageJson(packageJson);

      expect(deps).toHaveLength(2);
    });

    it('should include optionalDependencies by default', () => {
      const packageJson = JSON.stringify({
        dependencies: { express: '^4.0.0' },
        optionalDependencies: { fsevents: '^2.0.0' },
      });

      const parser = new DependencyParser();
      const deps = parser.parsePackageJson(packageJson);

      expect(deps).toHaveLength(2);
      expect(deps.find((d) => d.name === 'fsevents')?.type).toBe('optionalDependencies');
    });

    it('should handle empty dependencies', () => {
      const packageJson = JSON.stringify({
        name: 'empty-project',
      });

      const parser = new DependencyParser();
      const deps = parser.parsePackageJson(packageJson);

      expect(deps).toHaveLength(0);
    });
  });

  describe('parsePackageLock (v2/v3)', () => {
    it('should parse packages from lock file', () => {
      const lockFile = JSON.stringify({
        lockfileVersion: 3,
        packages: {
          '': { name: 'test', version: '1.0.0' },
          'node_modules/express': {
            version: '4.18.2',
            resolved: 'https://registry.npmjs.org/express/-/express-4.18.2.tgz',
            integrity: 'sha512-...',
          },
          'node_modules/lodash': {
            version: '4.17.21',
            resolved: 'https://registry.npmjs.org/lodash/-/lodash-4.17.21.tgz',
          },
        },
      });

      const parser = new DependencyParser();
      const deps = parser.parsePackageLock(lockFile);

      expect(deps).toHaveLength(2);
      expect(deps.find((d) => d.name === 'express')).toMatchObject({
        name: 'express',
        resolvedVersion: '4.18.2',
        integrity: 'sha512-...',
      });
    });

    it('should handle scoped packages', () => {
      const lockFile = JSON.stringify({
        lockfileVersion: 3,
        packages: {
          '': { name: 'test' },
          'node_modules/@types/node': {
            version: '20.0.0',
            dev: true,
          },
        },
      });

      const parser = new DependencyParser();
      const deps = parser.parsePackageLock(lockFile);

      expect(deps).toHaveLength(1);
      expect(deps[0].name).toBe('@types/node');
      expect(deps[0].type).toBe('devDependencies');
    });

    it('should identify dev dependencies', () => {
      const lockFile = JSON.stringify({
        lockfileVersion: 3,
        packages: {
          '': {},
          'node_modules/vitest': { version: '1.0.0', dev: true },
          'node_modules/express': { version: '4.0.0' },
        },
      });

      const parser = new DependencyParser();
      const deps = parser.parsePackageLock(lockFile);

      expect(deps.find((d) => d.name === 'vitest')?.type).toBe('devDependencies');
      expect(deps.find((d) => d.name === 'express')?.type).toBe('dependencies');
    });

    it('should identify optional dependencies', () => {
      const lockFile = JSON.stringify({
        lockfileVersion: 3,
        packages: {
          '': {},
          'node_modules/fsevents': { version: '2.0.0', optional: true },
        },
      });

      const parser = new DependencyParser();
      const deps = parser.parsePackageLock(lockFile);

      expect(deps[0].type).toBe('optionalDependencies');
    });
  });

  describe('parseDirectory', () => {
    let tempDir: string;

    beforeEach(() => {
      tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'dep-parser-test-'));
    });

    afterEach(() => {
      fs.rmSync(tempDir, { recursive: true, force: true });
    });

    it('should parse directory with package.json', async () => {
      const packageJson = {
        name: 'test-project',
        version: '1.0.0',
        dependencies: { express: '^4.18.0' },
      };
      fs.writeFileSync(
        path.join(tempDir, 'package.json'),
        JSON.stringify(packageJson)
      );

      const parser = new DependencyParser();
      const result = await parser.parseDirectory(tempDir);

      expect(result.projectName).toBe('test-project');
      expect(result.projectVersion).toBe('1.0.0');
      expect(result.dependencies).toHaveLength(1);
      expect(result.directCount).toBe(1);
    });

    it('should enrich with lock file data', async () => {
      const packageJson = {
        name: 'test-project',
        dependencies: { express: '^4.18.0' },
      };
      const lockFile = {
        lockfileVersion: 3,
        packages: {
          '': { name: 'test-project' },
          'node_modules/express': {
            version: '4.18.2',
            integrity: 'sha512-test',
          },
          'node_modules/body-parser': {
            version: '1.20.0',
          },
        },
      };

      fs.writeFileSync(
        path.join(tempDir, 'package.json'),
        JSON.stringify(packageJson)
      );
      fs.writeFileSync(
        path.join(tempDir, 'package-lock.json'),
        JSON.stringify(lockFile)
      );

      const parser = new DependencyParser();
      const result = await parser.parseDirectory(tempDir);

      expect(result.dependencies).toHaveLength(2);
      expect(result.directCount).toBe(1);
      expect(result.transitiveCount).toBe(1);

      const express = result.dependencies.find((d) => d.name === 'express');
      expect(express?.isDirect).toBe(true);
      expect(express?.resolvedVersion).toBe('4.18.2');

      const bodyParser = result.dependencies.find((d) => d.name === 'body-parser');
      expect(bodyParser?.isDirect).toBe(false);
    });

    it('should throw if package.json not found', async () => {
      const parser = new DependencyParser();

      await expect(parser.parseDirectory(tempDir)).rejects.toThrow(
        'package.json not found'
      );
    });

    it('should warn if package-lock.json not found', async () => {
      const packageJson = { dependencies: { express: '^4.0.0' } };
      fs.writeFileSync(
        path.join(tempDir, 'package.json'),
        JSON.stringify(packageJson)
      );

      const parser = new DependencyParser();
      const result = await parser.parseDirectory(tempDir);

      expect(result.warnings).toContain(
        'package-lock.json not found, using version specifiers only'
      );
    });
  });
});

describe('resolveVersionSpecifier', () => {
  it('should identify exact version', () => {
    expect(resolveVersionSpecifier('4.18.2')).toEqual({
      type: 'exact',
      version: '4.18.2',
    });
  });

  it('should identify caret range', () => {
    const result = resolveVersionSpecifier('^4.18.0');
    expect(result.type).toBe('range');
    expect(result.minVersion).toBe('4.18.0');
  });

  it('should identify tilde range', () => {
    const result = resolveVersionSpecifier('~4.18.0');
    expect(result.type).toBe('range');
    expect(result.minVersion).toBe('4.18.0');
  });

  it('should identify URL', () => {
    expect(resolveVersionSpecifier('https://example.com/pkg.tgz')).toEqual({
      type: 'url',
    });
  });

  it('should identify git', () => {
    expect(resolveVersionSpecifier('github:user/repo')).toEqual({
      type: 'git',
    });
    expect(resolveVersionSpecifier('git+https://github.com/user/repo')).toEqual({
      type: 'git',
    });
  });

  it('should identify tag', () => {
    expect(resolveVersionSpecifier('latest')).toEqual({ type: 'tag' });
    expect(resolveVersionSpecifier('next')).toEqual({ type: 'tag' });
  });

  it('should handle greater than', () => {
    const result = resolveVersionSpecifier('>=1.0.0');
    expect(result.type).toBe('range');
    expect(result.minVersion).toBe('1.0.0');
  });
});

describe('filterDependenciesForScanning', () => {
  const deps: ParsedDependency[] = [
    { name: 'express', versionSpecifier: '^4.0.0', type: 'dependencies', isDirect: true },
    { name: 'vitest', versionSpecifier: '^1.0.0', type: 'devDependencies', isDirect: true },
    { name: 'body-parser', versionSpecifier: '1.0.0', type: 'dependencies', isDirect: false },
  ];

  it('should return all by default', () => {
    const filtered = filterDependenciesForScanning(deps);
    expect(filtered).toHaveLength(3);
  });

  it('should filter out dev dependencies', () => {
    const filtered = filterDependenciesForScanning(deps, {
      includeDevDependencies: false,
    });
    expect(filtered).toHaveLength(2);
    expect(filtered.find((d) => d.name === 'vitest')).toBeUndefined();
  });

  it('should filter out transitive dependencies', () => {
    const filtered = filterDependenciesForScanning(deps, {
      includeTransitive: false,
    });
    expect(filtered).toHaveLength(2);
    expect(filtered.find((d) => d.name === 'body-parser')).toBeUndefined();
  });

  it('should return only direct dependencies', () => {
    const filtered = filterDependenciesForScanning(deps, { directOnly: true });
    expect(filtered).toHaveLength(2);
    expect(filtered.every((d) => d.isDirect)).toBe(true);
  });
});

describe('getUniquePackages', () => {
  it('should deduplicate by name', () => {
    const deps: ParsedDependency[] = [
      { name: 'lodash', versionSpecifier: '4.17.21', type: 'dependencies', isDirect: true },
      { name: 'lodash', versionSpecifier: '4.17.20', type: 'dependencies', isDirect: false },
    ];

    const unique = getUniquePackages(deps);
    expect(unique).toHaveLength(1);
  });

  it('should prefer direct dependencies', () => {
    const deps: ParsedDependency[] = [
      { name: 'lodash', versionSpecifier: '4.17.20', type: 'dependencies', isDirect: false },
      { name: 'lodash', versionSpecifier: '4.17.21', type: 'dependencies', isDirect: true },
    ];

    const unique = getUniquePackages(deps);
    expect(unique[0].versionSpecifier).toBe('4.17.21');
    expect(unique[0].isDirect).toBe(true);
  });
});
