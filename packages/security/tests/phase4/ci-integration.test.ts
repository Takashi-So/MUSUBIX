/**
 * @fileoverview CI Integration Tests
 * @module @nahisaho/musubix-security/tests/phase4/ci-integration
 */

import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest';
import {
  CIIntegration,
  createCIIntegration,
  isCI,
  detectCIPlatform,
  type CIPlatform,
  type CIIntegrationOptions,
} from '../../src/integrations/ci-integration.js';
import type { ScanResult, Vulnerability } from '../../src/types/index.js';

describe('CIIntegration', () => {
  let originalEnv: NodeJS.ProcessEnv;

  beforeEach(() => {
    originalEnv = { ...process.env };
    // Clear CI environment variables
    delete process.env.CI;
    delete process.env.GITHUB_ACTIONS;
    delete process.env.GITLAB_CI;
    delete process.env.TF_BUILD;
    delete process.env.JENKINS_URL;
    delete process.env.CIRCLECI;
  });

  afterEach(() => {
    process.env = originalEnv;
  });

  const createMockScanResult = (overrides?: Partial<ScanResult>): ScanResult => ({
    vulnerabilities: [],
    scannedFiles: 10,
    skippedFiles: 0,
    duration: 100,
    timestamp: new Date(),
    options: {},
    summary: {
      total: 0,
      critical: 0,
      high: 0,
      medium: 0,
      low: 0,
      info: 0,
    },
    ...overrides,
  });

  const createMockVulnerability = (severity: 'critical' | 'high' | 'medium' | 'low' | 'info'): Vulnerability => ({
    id: `VULN-${Date.now()}`,
    type: 'xss',
    ruleId: `SEC-${severity.toUpperCase()}-001`,
    severity,
    description: `Test ${severity} vulnerability`,
    recommendation: 'Fix the issue',
    confidence: 0.9,
    cwes: ['CWE-79'],
    owasp: ['A01:2021'],
    detectedAt: new Date(),
    location: {
      file: 'src/test.ts',
      startLine: 10,
      endLine: 10,
      startColumn: 5,
      endColumn: 50,
    },
  });

  describe('createCIIntegration', () => {
    it('should create CI integration with default options', () => {
      const ci = createCIIntegration();
      expect(ci).toBeInstanceOf(CIIntegration);
    });

    it('should create CI integration with custom options', () => {
      const ci = createCIIntegration({
        failOn: ['critical'],
        annotations: false,
        prComment: true,
      });
      expect(ci).toBeInstanceOf(CIIntegration);
    });
  });

  describe('detectEnvironment', () => {
    it('should detect non-CI environment', () => {
      const ci = createCIIntegration();
      const env = ci.detectEnvironment();
      
      expect(env.isCI).toBe(false);
      expect(env.platform).toBe('generic');
    });

    it('should detect GitHub Actions', () => {
      process.env.GITHUB_ACTIONS = 'true';
      process.env.GITHUB_REPOSITORY = 'owner/repo';
      process.env.GITHUB_SHA = 'abc123';
      process.env.GITHUB_REF_NAME = 'main';
      process.env.GITHUB_ACTOR = 'testuser';
      
      const ci = createCIIntegration();
      const env = ci.detectEnvironment();
      
      expect(env.isCI).toBe(true);
      expect(env.platform).toBe('github-actions');
      expect(env.metadata.repository).toBe('owner/repo');
      expect(env.metadata.commitSha).toBe('abc123');
      expect(env.metadata.branch).toBe('main');
    });

    it('should detect GitLab CI', () => {
      process.env.GITLAB_CI = 'true';
      process.env.CI_PROJECT_PATH = 'group/project';
      process.env.CI_COMMIT_SHA = 'def456';
      
      const ci = createCIIntegration();
      const env = ci.detectEnvironment();
      
      expect(env.isCI).toBe(true);
      expect(env.platform).toBe('gitlab-ci');
      expect(env.metadata.repository).toBe('group/project');
    });

    it('should detect Azure Pipelines', () => {
      process.env.TF_BUILD = 'True';
      process.env.BUILD_REPOSITORY_NAME = 'my-repo';
      
      const ci = createCIIntegration();
      const env = ci.detectEnvironment();
      
      expect(env.isCI).toBe(true);
      expect(env.platform).toBe('azure-pipelines');
    });

    it('should detect Jenkins', () => {
      process.env.JENKINS_URL = 'http://jenkins.example.com';
      process.env.BUILD_NUMBER = '123';
      
      const ci = createCIIntegration();
      const env = ci.detectEnvironment();
      
      expect(env.isCI).toBe(true);
      expect(env.platform).toBe('jenkins');
      expect(env.metadata.buildId).toBe('123');
    });

    it('should detect CircleCI', () => {
      process.env.CIRCLECI = 'true';
      process.env.CIRCLE_SHA1 = 'ghi789';
      
      const ci = createCIIntegration();
      const env = ci.detectEnvironment();
      
      expect(env.isCI).toBe(true);
      expect(env.platform).toBe('circleci');
      expect(env.metadata.commitSha).toBe('ghi789');
    });

    it('should detect generic CI', () => {
      process.env.CI = 'true';
      
      const ci = createCIIntegration();
      const env = ci.detectEnvironment();
      
      expect(env.isCI).toBe(true);
      expect(env.platform).toBe('generic');
    });
  });

  describe('processScanResult', () => {
    it('should process clean scan result as passing', () => {
      const ci = createCIIntegration();
      const scanResult = createMockScanResult();
      
      const result = ci.processScanResult(scanResult);
      
      expect(result.shouldFail).toBe(false);
      expect(result.exitCode).toBe(0);
      expect(result.summary.passed).toBe(true);
    });

    it('should fail on critical vulnerabilities', () => {
      const ci = createCIIntegration({ failOn: ['critical'] });
      const scanResult = createMockScanResult({
        vulnerabilities: [createMockVulnerability('critical')],
        summary: {
          total: 1,
          critical: 1,
          high: 0,
          medium: 0,
          low: 0,
          info: 0,
        },
      });
      
      const result = ci.processScanResult(scanResult);
      
      expect(result.shouldFail).toBe(true);
      expect(result.exitCode).toBe(1);
      expect(result.failureReasons.length).toBeGreaterThan(0);
    });

    it('should respect threshold settings', () => {
      const ci = createCIIntegration({
        failOn: [],
        thresholds: {
          maxCritical: 0,
          maxTotal: 5,
        },
      });
      
      const scanResult = createMockScanResult({
        vulnerabilities: [
          createMockVulnerability('medium'),
          createMockVulnerability('medium'),
        ],
        summary: {
          total: 2,
          critical: 0,
          high: 0,
          medium: 2,
          low: 0,
          info: 0,
        },
      });
      
      const result = ci.processScanResult(scanResult);
      
      // Should pass since we only have 2 medium issues and maxTotal is 5
      expect(result.shouldFail).toBe(false);
    });

    it('should fail when exceeding maxTotal threshold', () => {
      const ci = createCIIntegration({
        failOn: [],
        thresholds: { maxTotal: 1 },
      });
      
      const scanResult = createMockScanResult({
        vulnerabilities: [
          createMockVulnerability('medium'),
          createMockVulnerability('low'),
        ],
        summary: {
          total: 2,
          critical: 0,
          high: 0,
          medium: 1,
          low: 1,
          info: 0,
        },
      });
      
      const result = ci.processScanResult(scanResult);
      
      expect(result.shouldFail).toBe(true);
      expect(result.failureReasons).toContain('Total vulnerabilities (2) exceed threshold (1)');
    });
  });

  describe('generateAnnotations', () => {
    it('should generate annotations for vulnerabilities', () => {
      const ci = createCIIntegration({ annotations: true });
      const scanResult = createMockScanResult({
        vulnerabilities: [createMockVulnerability('high')],
      });
      
      const annotations = ci.generateAnnotations(scanResult);
      
      expect(annotations.length).toBe(1);
      expect(annotations[0].level).toBe('error');
      expect(annotations[0].file).toBe('src/test.ts');
      expect(annotations[0].startLine).toBe(10);
    });

    it('should not generate annotations when disabled', () => {
      const ci = createCIIntegration({ annotations: false });
      const scanResult = createMockScanResult({
        vulnerabilities: [createMockVulnerability('high')],
      });
      
      const annotations = ci.generateAnnotations(scanResult);
      
      expect(annotations.length).toBe(0);
    });

    it('should map severity to annotation level correctly', () => {
      const ci = createCIIntegration({ annotations: true });
      
      const criticalResult = createMockScanResult({
        vulnerabilities: [createMockVulnerability('critical')],
      });
      const mediumResult = createMockScanResult({
        vulnerabilities: [createMockVulnerability('medium')],
      });
      const lowResult = createMockScanResult({
        vulnerabilities: [createMockVulnerability('low')],
      });
      
      expect(ci.generateAnnotations(criticalResult)[0].level).toBe('error');
      expect(ci.generateAnnotations(mediumResult)[0].level).toBe('warning');
      expect(ci.generateAnnotations(lowResult)[0].level).toBe('notice');
    });
  });

  describe('generateSummary', () => {
    it('should calculate security score correctly', () => {
      const ci = createCIIntegration();
      const scanResult = createMockScanResult({
        summary: {
          total: 2,
          critical: 1, // -25
          high: 1,     // -10
          medium: 0,
          low: 0,
          info: 0,
        },
      });
      
      const summary = ci.generateSummary(scanResult);
      
      expect(summary.securityScore).toBe(65); // 100 - 25 - 10 = 65
      expect(summary.total).toBe(2);
    });

    it('should show passed status for clean scan', () => {
      const ci = createCIIntegration();
      const scanResult = createMockScanResult();
      
      const summary = ci.generateSummary(scanResult);
      
      expect(summary.passed).toBe(true);
      expect(summary.statusEmoji).toBe('✅');
    });
  });

  describe('generateWorkflowFile', () => {
    it('should generate GitHub Actions workflow', () => {
      const ci = createCIIntegration();
      const workflow = ci.generateWorkflowFile('github-actions');
      
      expect(workflow).toContain('name: Security Scan');
      expect(workflow).toContain('uses: actions/checkout@v4');
      expect(workflow).toContain('musubix-security');
    });

    it('should generate GitLab CI config', () => {
      const ci = createCIIntegration();
      const config = ci.generateWorkflowFile('gitlab-ci');
      
      expect(config).toContain('security-scan:');
      expect(config).toContain('image: node:20');
    });

    it('should generate Azure Pipelines config', () => {
      const ci = createCIIntegration();
      const config = ci.generateWorkflowFile('azure-pipelines');
      
      expect(config).toContain('trigger:');
      expect(config).toContain('vmImage:');
    });

    it('should generate generic script', () => {
      const ci = createCIIntegration();
      const script = ci.generateWorkflowFile('generic');
      
      expect(script).toContain('#!/bin/bash');
      expect(script).toContain('npm ci');
    });
  });

  describe('formatOutput', () => {
    it('should format output with scan results', () => {
      process.env.GITHUB_ACTIONS = 'true';
      process.env.GITHUB_REPOSITORY = 'owner/repo';
      
      const ci = createCIIntegration();
      const scanResult = createMockScanResult({
        summary: {
          total: 1,
          critical: 1,
          high: 0,
          medium: 0,
          low: 0,
          info: 0,
        },
      });
      
      const result = ci.processScanResult(scanResult);
      
      expect(result.formattedOutput).toContain('MUSUBIX Security Scan Results');
      expect(result.formattedOutput).toContain('github-actions');
      expect(result.formattedOutput).toContain('owner/repo');
    });
  });

  describe('generateCacheKey', () => {
    it('should generate consistent cache keys', () => {
      const ci = createCIIntegration({ cacheKeyPrefix: 'test' });
      
      const key1 = ci.generateCacheKey(['file1.ts', 'file2.ts']);
      const key2 = ci.generateCacheKey(['file2.ts', 'file1.ts']);
      
      expect(key1).toBe(key2); // Should be same regardless of order
      expect(key1).toContain('test-');
    });
  });

  describe('helper functions', () => {
    it('isCI should return false when not in CI', () => {
      expect(isCI()).toBe(false);
    });

    it('isCI should return true in CI environment', () => {
      process.env.CI = 'true';
      expect(isCI()).toBe(true);
    });

    it('detectCIPlatform should return platform', () => {
      process.env.GITHUB_ACTIONS = 'true';
      expect(detectCIPlatform()).toBe('github-actions');
    });
  });
});
