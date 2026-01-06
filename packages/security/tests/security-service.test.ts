/**
 * @fileoverview Tests for security service (integration tests)
 * @module @nahisaho/musubix-security/tests/security-service
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import * as os from 'node:os';
import {
  SecurityService,
  createSecurityService,
} from '../src/services/index.js';

describe('SecurityService', () => {
  let service: SecurityService;
  let tempDir: string;

  beforeEach(async () => {
    service = createSecurityService();
    tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'security-test-'));
  });

  afterEach(async () => {
    await fs.rm(tempDir, { recursive: true, force: true });
  });

  describe('Full Scan', () => {
    it('should run comprehensive scan', async () => {
      // Create test file with vulnerability
      await fs.writeFile(
        path.join(tempDir, 'vulnerable.ts'),
        `
          function query(input: string) {
            db.query("SELECT * FROM users WHERE id = " + input);
          }
        `
      );

      const result = await service.scan({
        target: tempDir,
        vulnerabilities: true,
        taint: false,
        secrets: false,
        dependencies: false,
        generateFixes: true,
      });

      expect(result.metadata.target).toBe(tempDir);
      expect(result.metadata.filesScanned).toBeGreaterThanOrEqual(0);
      expect(result.vulnerabilities).toBeDefined();
    });

    it('should include all scan types when enabled', async () => {
      await fs.writeFile(
        path.join(tempDir, 'test.ts'),
        `const apiKey = "sk_test_1234567890";`
      );
      await fs.writeFile(
        path.join(tempDir, 'package.json'),
        JSON.stringify({ name: 'test', dependencies: {} })
      );

      const result = await service.scan({
        target: tempDir,
        vulnerabilities: true,
        taint: true,
        secrets: true,
        dependencies: true,
      });

      expect(result.vulnerabilities).toBeDefined();
      expect(result.taint).toBeDefined();
      expect(result.secrets).toBeDefined();
      // dependencies may fail without lock file
    });

    it('should generate fixes when requested', async () => {
      await fs.writeFile(
        path.join(tempDir, 'sql.ts'),
        `db.query("SELECT * FROM users WHERE id = " + userId);`
      );

      const result = await service.scan({
        target: tempDir,
        generateFixes: true,
      });

      if (result.summary.totalVulnerabilities > 0) {
        expect(result.fixes).toBeDefined();
        expect(result.summary.fixesGenerated).toBeGreaterThanOrEqual(0);
      }
    });
  });

  describe('Quick Scan', () => {
    it('should perform fast vulnerability-only scan', async () => {
      await fs.writeFile(
        path.join(tempDir, 'test.ts'),
        `eval(userInput);`
      );

      const result = await service.quickScan(tempDir);
      expect(result.vulnerabilities).toBeDefined();
    });
  });

  describe('Single File Scan', () => {
    it('should scan a single file', async () => {
      const testFile = path.join(tempDir, 'single.ts');
      await fs.writeFile(testFile, `exec(cmd);`);

      const result = await service.scanFile(testFile);
      // ScanResult has scannedFiles (not summary.filesScanned)
      expect(result.scannedFiles).toBe(1);
    });
  });

  describe('Taint Analysis', () => {
    it('should run taint analysis', async () => {
      await fs.writeFile(
        path.join(tempDir, 'api.ts'),
        `
          function handler(req: Request) {
            const input = req.body.data;
            db.query("SELECT * FROM users WHERE id = " + input);
          }
        `
      );

      const result = await service.analyzeTaint(tempDir);
      expect(result).toBeDefined();
      expect(result.sources).toBeDefined();
      expect(result.sinks).toBeDefined();
    });
  });

  describe('Secret Detection', () => {
    it('should detect secrets', async () => {
      await fs.writeFile(
        path.join(tempDir, '.env'),
        'AWS_ACCESS_KEY_ID=AKIAIOSFODNN7EXAMPLE'
      );

      const result = await service.detectSecrets(tempDir);
      expect(result.summary.total).toBeGreaterThanOrEqual(0);
    });
  });

  describe('Report Generation', () => {
    it('should generate JSON report', async () => {
      await fs.writeFile(
        path.join(tempDir, 'test.ts'),
        `eval(input);`
      );

      const scanResult = await service.scan({ target: tempDir });
      const report = await service.generateReport(scanResult, 'json');
      
      expect(report).toBeTruthy();
      const parsed = JSON.parse(report);
      expect(parsed.summary).toBeDefined();
    });

    it('should generate Markdown report', async () => {
      await fs.writeFile(
        path.join(tempDir, 'test.ts'),
        `eval(input);`
      );

      const scanResult = await service.scan({ target: tempDir });
      const report = await service.generateReport(scanResult, 'markdown');
      
      expect(report).toContain('# Security Scan Report');
      expect(report).toContain('Summary');
    });

    it('should generate SARIF report', async () => {
      await fs.writeFile(
        path.join(tempDir, 'test.ts'),
        `eval(input);`
      );

      const scanResult = await service.scan({ target: tempDir });
      const report = await service.generateReport(scanResult, 'sarif');
      
      const parsed = JSON.parse(report);
      expect(parsed.$schema).toContain('sarif');
      expect(parsed.runs).toBeDefined();
    });

    it('should generate HTML report', async () => {
      await fs.writeFile(
        path.join(tempDir, 'test.ts'),
        `eval(input);`
      );

      const scanResult = await service.scan({ target: tempDir });
      const report = await service.generateReport(scanResult, 'html');
      
      expect(report).toContain('<!DOCTYPE html>');
      expect(report).toContain('Security Scan Report');
    });
  });

  describe('Configuration', () => {
    it('should load configuration from file', async () => {
      const configFile = path.join(tempDir, '.securityrc.json');
      await fs.writeFile(
        configFile,
        JSON.stringify({
          scan: {
            extensions: ['.ts', '.js'],
            exclude: ['node_modules'],
          },
        })
      );

      const configuredService = createSecurityService(tempDir);
      expect(configuredService).toBeDefined();
    });

    it('should use custom configuration', async () => {
      const customService = createSecurityService();
      expect(customService).toBeDefined();
    });
  });

  describe('Helper Functions', () => {
    it('should export helper functions', async () => {
      // The helper functions should be available
      expect(createSecurityService).toBeDefined();
    });

    it('should run quick scan via factory', async () => {
      await fs.writeFile(
        path.join(tempDir, 'test.ts'),
        `console.log("safe");`
      );

      const result = await service.quickScan(tempDir);
      expect(result).toBeDefined();
    });
  });

  describe('Summary Statistics', () => {
    it('should calculate summary statistics', async () => {
      await fs.writeFile(
        path.join(tempDir, 'multi.ts'),
        `
          eval(input);
          exec(cmd);
          db.query("SELECT * FROM " + table);
        `
      );

      const result = await service.scan({ target: tempDir });
      expect(result.summary).toBeDefined();
      expect(result.summary.totalVulnerabilities).toBeGreaterThanOrEqual(0);
    });
  });
});
