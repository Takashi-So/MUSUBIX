/**
 * @fileoverview Config Parser Tests
 * @module @nahisaho/musubix-security/rules/config/config-parser.test
 * @trace TSK-RULE-002
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs';
import * as path from 'node:path';
import * as os from 'node:os';
import {
  parseConfig,
  loadConfigFile,
  findConfigFile,
  loadProjectConfig,
  createConfigBuilder,
  validateConfig,
  writeConfigFile,
  DEFAULT_CONFIG,
} from '../../../src/rules/config/config-parser.js';
import { getProfile } from '../../../src/rules/config/profiles.js';

describe('Config Parser', () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'config-test-'));
  });

  afterEach(() => {
    fs.rmSync(tempDir, { recursive: true, force: true });
  });

  describe('parseConfig', () => {
    it('should parse minimal config', () => {
      const config = parseConfig({});
      expect(config.profile).toBe('standard');
      expect(config.severityThreshold).toBe('medium');
    });

    it('should apply profile defaults', () => {
      const config = parseConfig({ profile: 'strict' });
      expect(config.severityThreshold).toBe('info');
      expect(config.enableTaintAnalysis).toBe(true);
      expect(config.enableDFG).toBe(true);
    });

    it('should parse rule settings as boolean', () => {
      const config = parseConfig({
        rules: {
          'test-rule': true,
          'disabled-rule': false,
        },
      });
      expect(config.rules['test-rule'].enabled).toBe(true);
      expect(config.rules['disabled-rule'].enabled).toBe(false);
    });

    it('should parse rule settings as severity', () => {
      const config = parseConfig({
        rules: {
          'test-rule': 'critical',
        },
      });
      expect(config.rules['test-rule'].enabled).toBe(true);
      expect(config.rules['test-rule'].severity).toBe('critical');
    });

    it('should parse rule settings as object', () => {
      const config = parseConfig({
        rules: {
          'test-rule': {
            enabled: true,
            severity: 'high',
            options: { maxLength: 100 },
          },
        },
      });
      expect(config.rules['test-rule'].enabled).toBe(true);
      expect(config.rules['test-rule'].severity).toBe('high');
      expect(config.rules['test-rule'].options).toEqual({ maxLength: 100 });
    });

    it('should override profile rules', () => {
      const config = parseConfig({
        profile: 'standard',
        rules: {
          'owasp-a01-broken-access-control': { severity: 'critical' },
        },
      });
      expect(config.rules['owasp-a01-broken-access-control'].severity).toBe('critical');
    });
  });

  describe('loadConfigFile', () => {
    it('should load JSON config file', async () => {
      const configPath = path.join(tempDir, 'config.json');
      await fs.promises.writeFile(
        configPath,
        JSON.stringify({
          profile: 'minimal',
          severityThreshold: 'high',
        })
      );

      const result = await loadConfigFile(configPath);
      expect(result.errors).toHaveLength(0);
      expect(result.config.profile).toBe('minimal');
      expect(result.config.severityThreshold).toBe('high');
    });

    it('should handle missing file', async () => {
      const result = await loadConfigFile(path.join(tempDir, 'nonexistent.json'));
      expect(result.errors.length).toBeGreaterThan(0);
      expect(result.config).toEqual(DEFAULT_CONFIG);
    });

    it('should handle invalid JSON', async () => {
      const configPath = path.join(tempDir, 'invalid.json');
      await fs.promises.writeFile(configPath, 'not valid json');

      const result = await loadConfigFile(configPath);
      expect(result.errors.length).toBeGreaterThan(0);
    });

    it('should handle extends with preset', async () => {
      const configPath = path.join(tempDir, 'config.json');
      await fs.promises.writeFile(
        configPath,
        JSON.stringify({
          extends: 'musubix:strict',
          rules: {
            'custom-rule': true,
          },
        })
      );

      const result = await loadConfigFile(configPath);
      expect(result.errors).toHaveLength(0);
      expect(result.config.enableDFG).toBe(true); // From strict profile
      expect(result.config.rules['custom-rule']).toBeDefined();
    });
  });

  describe('findConfigFile', () => {
    it('should find musubix-security.config.json', async () => {
      const configPath = path.join(tempDir, 'musubix-security.config.json');
      await fs.promises.writeFile(configPath, '{}');

      const found = await findConfigFile(tempDir);
      expect(found).toBe(configPath);
    });

    it('should find .musubixsecurity.json', async () => {
      const configPath = path.join(tempDir, '.musubixsecurity.json');
      await fs.promises.writeFile(configPath, '{}');

      const found = await findConfigFile(tempDir);
      expect(found).toBe(configPath);
    });

    it('should find config in package.json', async () => {
      const packagePath = path.join(tempDir, 'package.json');
      await fs.promises.writeFile(
        packagePath,
        JSON.stringify({
          name: 'test',
          'musubix-security': {
            profile: 'minimal',
          },
        })
      );

      const found = await findConfigFile(tempDir);
      expect(found).toBe(packagePath);
    });

    it('should return undefined when no config exists', async () => {
      const found = await findConfigFile(tempDir);
      expect(found).toBeUndefined();
    });
  });

  describe('loadProjectConfig', () => {
    it('should load project config', async () => {
      const configPath = path.join(tempDir, 'musubix-security.config.json');
      await fs.promises.writeFile(
        configPath,
        JSON.stringify({ profile: 'strict' })
      );

      const result = await loadProjectConfig(tempDir);
      expect(result.errors).toHaveLength(0);
      expect(result.config.profile).toBe('strict');
      expect(result.configPath).toBe(configPath);
    });

    it('should return defaults with warning when no config', async () => {
      const result = await loadProjectConfig(tempDir);
      expect(result.errors).toHaveLength(0);
      expect(result.warnings.length).toBeGreaterThan(0);
      expect(result.config).toEqual(DEFAULT_CONFIG);
    });

    it('should load from package.json', async () => {
      await fs.promises.writeFile(
        path.join(tempDir, 'package.json'),
        JSON.stringify({
          name: 'test',
          'musubix-security': {
            profile: 'minimal',
            severityThreshold: 'high',
          },
        })
      );

      const result = await loadProjectConfig(tempDir);
      expect(result.config.profile).toBe('minimal');
    });
  });

  describe('createConfigBuilder', () => {
    it('should create config with builder pattern', () => {
      const config = createConfigBuilder()
        .withProfile('strict')
        .withSeverityThreshold('critical')
        .withRule('test-rule', true, 'high')
        .withTaintAnalysis()
        .withDFG()
        .build();

      expect(config.profile).toBe('strict');
      expect(config.severityThreshold).toBe('critical');
      expect(config.rules['test-rule'].enabled).toBe(true);
      expect(config.rules['test-rule'].severity).toBe('high');
      expect(config.enableTaintAnalysis).toBe(true);
      expect(config.enableDFG).toBe(true);
    });

    it('should set include patterns', () => {
      const config = createConfigBuilder()
        .withInclude(['**/*.ts', '**/*.js'])
        .build();

      expect(config.include).toEqual(['**/*.ts', '**/*.js']);
    });

    it('should set exclude patterns', () => {
      const config = createConfigBuilder()
        .withExclude(['**/test/**'])
        .build();

      expect(config.exclude).toEqual(['**/test/**']);
    });
  });

  describe('validateConfig', () => {
    it('should validate correct config', () => {
      const errors = validateConfig({
        profile: 'standard',
        rules: {},
        include: ['**/*.ts'],
        exclude: ['**/node_modules/**'],
        severityThreshold: 'medium',
        enableTaintAnalysis: false,
        enableDFG: false,
      });
      expect(errors).toHaveLength(0);
    });

    it('should detect unknown profile', () => {
      const errors = validateConfig({
        profile: 'unknown-profile',
        rules: {},
        include: [],
        exclude: [],
        severityThreshold: 'medium',
        enableTaintAnalysis: false,
        enableDFG: false,
      });
      expect(errors.some(e => e.includes('Unknown profile'))).toBe(true);
    });

    it('should detect invalid severity threshold', () => {
      const errors = validateConfig({
        profile: 'standard',
        rules: {},
        include: [],
        exclude: [],
        severityThreshold: 'invalid' as any,
        enableTaintAnalysis: false,
        enableDFG: false,
      });
      expect(errors.some(e => e.includes('Invalid severity threshold'))).toBe(true);
    });

    it('should detect invalid rule severity', () => {
      const errors = validateConfig({
        profile: 'standard',
        rules: {
          'test-rule': { severity: 'invalid' as any },
        },
        include: [],
        exclude: [],
        severityThreshold: 'medium',
        enableTaintAnalysis: false,
        enableDFG: false,
      });
      expect(errors.some(e => e.includes('Invalid severity for rule'))).toBe(true);
    });
  });

  describe('writeConfigFile', () => {
    it('should write config to file', async () => {
      const configPath = path.join(tempDir, 'output.json');
      const config = createConfigBuilder()
        .withProfile('strict')
        .withSeverityThreshold('high')
        .build();

      await writeConfigFile(configPath, config);

      const content = await fs.promises.readFile(configPath, 'utf-8');
      const parsed = JSON.parse(content);
      expect(parsed.profile).toBe('strict');
      expect(parsed.severityThreshold).toBe('high');
    });
  });

  describe('DEFAULT_CONFIG', () => {
    it('should have sensible defaults', () => {
      expect(DEFAULT_CONFIG.profile).toBe('standard');
      expect(DEFAULT_CONFIG.severityThreshold).toBe('info');
      expect(DEFAULT_CONFIG.include).toContain('**/*.ts');
      expect(DEFAULT_CONFIG.exclude).toContain('**/node_modules/**');
    });
  });
});
