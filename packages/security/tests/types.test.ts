/**
 * @fileoverview Tests for type definitions
 * @module @nahisaho/musubix-security/tests/types
 */

import { describe, it, expect } from 'vitest';
import {
  DEFAULT_CONFIG,
  BUILTIN_SECRET_PATTERNS,
  BUILTIN_SANITIZERS,
  type Vulnerability,
  type Severity,
  type TaintSource,
  type TaintSink,
  type Fix,
  type Secret,
} from '../src/types/index.js';

describe('Type Definitions', () => {
  describe('Vulnerability Type', () => {
    it('should allow creating a valid vulnerability object', () => {
      const vuln: Vulnerability = {
        id: 'VULN-001',
        ruleId: 'sql-injection',
        name: 'SQL Injection',
        description: 'Potential SQL injection vulnerability',
        severity: 'high',
        location: {
          file: 'src/db.ts',
          line: 10,
          column: 5,
        },
        cweId: 'CWE-89',
        owaspCategory: 'A03:2021',
        snippet: 'query(`SELECT * FROM users WHERE id = ${id}`)',
        remediation: 'Use parameterized queries',
      };

      expect(vuln.id).toBe('VULN-001');
      expect(vuln.severity).toBe('high');
      expect(vuln.location.file).toBe('src/db.ts');
    });

    it('should support all severity levels', () => {
      const severities: Severity[] = ['critical', 'high', 'medium', 'low', 'info'];
      expect(severities.length).toBe(5);
    });
  });

  describe('TaintSource and TaintSink Types', () => {
    it('should allow creating taint source', () => {
      const source: TaintSource = {
        id: 'SRC-001',
        variableName: 'req.body',
        location: {
          file: 'src/api.ts',
          line: 15,
          column: 10,
        },
        category: 'user-input',
        expression: 'req.body',
        description: 'User input from request body',
        confidence: 0.9,
      };

      expect(source.category).toBe('user-input');
    });

    it('should allow creating taint sink', () => {
      const sink: TaintSink = {
        id: 'SINK-001',
        functionName: 'db.query',
        location: {
          file: 'src/db.ts',
          line: 20,
          column: 5,
        },
        category: 'sql-query',
        argumentIndex: 0,
        expectedSanitizers: ['escape', 'parameterize'],
        description: 'SQL query execution',
        severity: 'critical',
      };

      expect(sink.category).toBe('sql-query');
      expect(sink.severity).toBe('critical');
    });
  });

  describe('Fix Type', () => {
    it('should allow creating a fix object', () => {
      const fix: Fix = {
        id: 'FIX-001',
        vulnerabilityId: 'VULN-001',
        description: 'Use parameterized query',
        strategy: 'parameterized-query',
        confidence: 0.95,
        edits: [
          {
            file: 'src/db.ts',
            startLine: 10,
            endLine: 10,
            originalCode: 'query(`SELECT * FROM users WHERE id = ${id}`)',
            newCode: 'query("SELECT * FROM users WHERE id = ?", [id])',
          },
        ],
      };

      expect(fix.strategy).toBe('parameterized-query');
      expect(fix.confidence).toBeGreaterThan(0.9);
      expect(fix.edits.length).toBe(1);
    });
  });

  describe('Secret Type', () => {
    it('should allow creating a secret object', () => {
      const secret: Secret = {
        id: 'SEC-001',
        type: 'aws-access-key',
        value: 'AKIAIOSFODNN7EXAMPLE',
        masked: 'AKIA************MPLE',
        file: '.env',
        line: 5,
        column: 1,
        context: 'AWS_ACCESS_KEY_ID=AKIAIOSFODNN7EXAMPLE',
        confidence: 0.99,
        isTestValue: false,
      };

      expect(secret.type).toBe('aws-access-key');
      expect(secret.masked).toContain('****');
    });
  });

  describe('DEFAULT_CONFIG', () => {
    it('should have all required properties', () => {
      expect(DEFAULT_CONFIG).toBeDefined();
      expect(DEFAULT_CONFIG.scan).toBeDefined();
      expect(DEFAULT_CONFIG.taint).toBeDefined();
      // Note: config uses 'secret' (singular) not 'secrets'
      expect(DEFAULT_CONFIG.secret).toBeDefined();
      // Note: config uses 'audit' not 'dependencies'
      expect(DEFAULT_CONFIG.audit).toBeDefined();
      expect(DEFAULT_CONFIG.report).toBeDefined();
      expect(DEFAULT_CONFIG.cache).toBeDefined();
    });

    it('should have sensible default values', () => {
      // scan has severityFilter and rulesets, not extensions/exclude
      expect(DEFAULT_CONFIG.scan?.severityFilter).toBeDefined();
      expect(DEFAULT_CONFIG.scan?.severityFilter).toContain('critical');
      expect(DEFAULT_CONFIG.scan?.severityFilter).toContain('high');
    });

    it('should have proper taint and AI configuration', () => {
      expect(DEFAULT_CONFIG.taint?.interprocedural).toBe(true);
      expect(DEFAULT_CONFIG.taint?.trackAsync).toBe(true);
      expect(DEFAULT_CONFIG.ai?.enabled).toBe(false);
    });
  });

  describe('BUILTIN_SECRET_PATTERNS', () => {
    it('should contain common secret patterns', () => {
      // Use 'type' field instead of 'name' (name is human-readable)
      const patternTypes = BUILTIN_SECRET_PATTERNS.map((p) => p.type);
      expect(patternTypes).toContain('aws-access-key');
      expect(patternTypes).toContain('github-token');
      expect(patternTypes).toContain('api-key'); // generic-api-key maps to 'api-key' type
    });

    it('should have valid pattern structure', () => {
      for (const pattern of BUILTIN_SECRET_PATTERNS) {
        expect(pattern.id).toBeDefined();
        expect(pattern.name).toBeDefined();
        expect(pattern.type).toBeDefined();
        expect(pattern.severity).toBeDefined();
        expect(pattern.enabled).toBeDefined();
      }
    });
  });

  describe('BUILTIN_SANITIZERS', () => {
    it('should contain common sanitizers', () => {
      const sanitizerNames = BUILTIN_SANITIZERS.map((s) => s.name);
      expect(sanitizerNames).toContain('escapeHtml');
      expect(sanitizerNames).toContain('parameterize');
    });

    it('should specify sanitizer protections', () => {
      const htmlSanitizer = BUILTIN_SANITIZERS.find((s) => s.name === 'escapeHtml');
      expect(htmlSanitizer?.protects).toContain('html-output');
    });
  });
});
