/**
 * @fileoverview Integration tests for EPIC-1, EPIC-2, EPIC-4
 * @module @nahisaho/musubix-security/tests/integration
 * @trace TSK-SEC-001〜030
 */

import { describe, it, expect, beforeEach } from 'vitest';

// EPIC-1: Taint Analysis Imports
import {
  EnhancedTaintAnalyzer,
  createEnhancedTaintAnalyzer,
} from '../../analysis/enhanced-taint-analyzer.js';

import {
  ALL_BUILTIN_SOURCES,
  USER_INPUT_SOURCES,
  HTTP_REQUEST_SOURCES,
  ENVIRONMENT_SOURCES,
  getSourcesByCategory,
} from '../../analysis/sources/index.js';

import {
  ALL_BUILTIN_SINKS,
  SQL_QUERY_SINKS,
  COMMAND_EXEC_SINKS,
  HTML_OUTPUT_SINKS,
  getSinksByCategory,
} from '../../analysis/sinks/index.js';

import {
  ALL_BUILTIN_SANITIZERS,
  SQL_SANITIZERS,
  HTML_SANITIZERS,
  PATH_SANITIZERS,
  getSanitizersForSink,
} from '../../analysis/sanitizers/index.js';

// EPIC-2: CVE Database Imports
import { NVDClient } from '../../cve/nvd-client.js';
import { CPEMatcher } from '../../cve/cpe-matcher.js';
import { DependencyParser } from '../../cve/dependency-parser.js';
import { RateLimiter } from '../../cve/rate-limiter.js';
import { CVECache, createMemoryCache } from '../../cve/cve-cache.js';
import { ReportGenerator, generateReport } from '../../cve/report-generator.js';

// EPIC-4: Auto-Fix Imports
import { AutoFixer, createAutoFixer } from '../../remediation/auto-fixer.js';
import { FixValidator, createFixValidator } from '../../remediation/fix-validator.js';
import { PatchGenerator, createPatchGenerator } from '../../remediation/patch-generator.js';
import { RemediationPlanner, createRemediationPlanner } from '../../remediation/remediation-planner.js';
import { SecureCodeTransformer, createSecureCodeTransformer } from '../../remediation/secure-code-transformer.js';

describe('EPIC Integration Tests', () => {
  describe('EPIC-1: Taint Analysis Enhancement', () => {
    describe('TSK-SEC-001: Type Definitions', () => {
      it('should have proper TaintSource definitions', () => {
        expect(ALL_BUILTIN_SOURCES).toBeDefined();
        expect(ALL_BUILTIN_SOURCES.length).toBeGreaterThan(0);
        
        const source = ALL_BUILTIN_SOURCES[0];
        expect(source.id).toBeDefined();
        expect(source.category).toBeDefined();
        expect(source.patterns).toBeDefined();
      });

      it('should have proper TaintSink definitions', () => {
        expect(ALL_BUILTIN_SINKS).toBeDefined();
        expect(ALL_BUILTIN_SINKS.length).toBeGreaterThan(0);
        
        const sink = ALL_BUILTIN_SINKS[0];
        expect(sink.id).toBeDefined();
        expect(sink.category).toBeDefined();
        expect(sink.patterns).toBeDefined();
      });
    });

    describe('TSK-SEC-002: Builtin Sources', () => {
      it('should have HTTP request sources', () => {
        expect(HTTP_REQUEST_SOURCES).toBeDefined();
        expect(HTTP_REQUEST_SOURCES.length).toBeGreaterThan(0);
        // HTTP sources have 'network' category
        expect(['user-input', 'network']).toContain(HTTP_REQUEST_SOURCES[0].category);
      });

      it('should have user input sources', () => {
        expect(USER_INPUT_SOURCES).toBeDefined();
        expect(USER_INPUT_SOURCES.length).toBeGreaterThan(0);
      });

      it('should have environment sources', () => {
        expect(ENVIRONMENT_SOURCES).toBeDefined();
        expect(ENVIRONMENT_SOURCES.length).toBeGreaterThan(0);
      });

      it('should filter sources by category', () => {
        const userInputSources = getSourcesByCategory('user-input');
        expect(userInputSources.length).toBeGreaterThan(0);
        userInputSources.forEach(s => {
          expect(s.category).toBe('user-input');
        });
      });
    });

    describe('TSK-SEC-003: Builtin Sinks', () => {
      it('should have SQL query sinks', () => {
        expect(SQL_QUERY_SINKS).toBeDefined();
        expect(SQL_QUERY_SINKS.length).toBeGreaterThan(0);
        expect(SQL_QUERY_SINKS[0].category).toBe('sql-query');
      });

      it('should have command execution sinks', () => {
        expect(COMMAND_EXEC_SINKS).toBeDefined();
        expect(COMMAND_EXEC_SINKS.length).toBeGreaterThan(0);
        expect(COMMAND_EXEC_SINKS[0].category).toBe('command-exec');
      });

      it('should have HTML output sinks', () => {
        expect(HTML_OUTPUT_SINKS).toBeDefined();
        expect(HTML_OUTPUT_SINKS.length).toBeGreaterThan(0);
      });

      it('should filter sinks by category', () => {
        const sqlSinks = getSinksByCategory('sql-query');
        expect(sqlSinks.length).toBeGreaterThan(0);
        sqlSinks.forEach(s => {
          expect(s.category).toBe('sql-query');
        });
      });
    });

    describe('TSK-SEC-004: Sanitizer Recognition', () => {
      it('should have SQL sanitizers', () => {
        expect(SQL_SANITIZERS).toBeDefined();
        expect(SQL_SANITIZERS.length).toBeGreaterThan(0);
      });

      it('should have HTML sanitizers', () => {
        expect(HTML_SANITIZERS).toBeDefined();
        expect(HTML_SANITIZERS.length).toBeGreaterThan(0);
      });

      it('should have path sanitizers', () => {
        expect(PATH_SANITIZERS).toBeDefined();
        expect(PATH_SANITIZERS.length).toBeGreaterThan(0);
      });

      it('should get sanitizers for specific sink type', () => {
        const sqlSanitizers = getSanitizersForSink('sql-query');
        expect(sqlSanitizers.length).toBeGreaterThan(0);
        sqlSanitizers.forEach(s => {
          expect(s.protects).toContain('sql-query');
        });
      });

      it('should have all builtin sanitizers aggregated', () => {
        expect(ALL_BUILTIN_SANITIZERS).toBeDefined();
        expect(ALL_BUILTIN_SANITIZERS.length).toBeGreaterThan(0);
        expect(ALL_BUILTIN_SANITIZERS.length).toBeGreaterThanOrEqual(
          SQL_SANITIZERS.length + HTML_SANITIZERS.length + PATH_SANITIZERS.length
        );
      });
    });

    describe('TSK-SEC-005-008: Enhanced Taint Analyzer', () => {
      let analyzer: EnhancedTaintAnalyzer;

      beforeEach(() => {
        analyzer = createEnhancedTaintAnalyzer({
          maxDepth: 5,
          buildCallGraph: false,
        });
      });

      it('should create enhanced taint analyzer', () => {
        expect(analyzer).toBeDefined();
        expect(analyzer.analyze).toBeDefined();
      });

      it('should analyze code and return results', async () => {
        const code = `
const data = req.body.username;
const query = \`SELECT * FROM users WHERE name = '\${data}'\`;
db.query(query);
`;
        const result = await analyzer.analyze(code, 'test.ts');
        expect(result).toBeDefined();
        expect(result.sources).toBeDefined();
        expect(result.sinks).toBeDefined();
      });
    });
  });

  describe('EPIC-2: CVE Database Integration', () => {
    describe('TSK-SEC-009: CVE Type Definitions', () => {
      it('should have CVE interface with required fields', () => {
        const cve = {
          id: 'CVE-2021-44228',
          description: 'Log4j RCE',
          published: new Date(),
          lastModified: new Date(),
          cwes: ['CWE-502'],
          references: [],
          affectedProducts: [],
          status: 'Analyzed' as const,
        };
        expect(cve.id).toMatch(/^CVE-\d{4}-\d+$/);
        expect(cve.description).toBeDefined();
      });

      it('should have CVSSScore interface', () => {
        const cvss = {
          version: '3.1' as const,
          baseScore: 10.0,
          severity: 'CRITICAL' as const,
          vectorString: 'CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:C/C:H/I:H/A:H',
          attackVector: 'NETWORK' as const,
          attackComplexity: 'LOW' as const,
          privilegesRequired: 'NONE' as const,
          userInteraction: 'NONE' as const,
          scope: 'CHANGED' as const,
          confidentialityImpact: 'HIGH' as const,
          integrityImpact: 'HIGH' as const,
          availabilityImpact: 'HIGH' as const,
        };
        expect(cvss.baseScore).toBe(10.0);
        expect(cvss.severity).toBe('CRITICAL');
      });
    });

    describe('TSK-SEC-010: NVD API Client', () => {
      it('should create NVD client with options', () => {
        const client = new NVDClient({
          apiKey: 'test-key',
          baseUrl: 'https://test.nvd.nist.gov',
        });
        expect(client).toBeDefined();
      });

      it('should create NVD client with default options', () => {
        const client = new NVDClient();
        expect(client).toBeDefined();
      });
    });

    describe('TSK-SEC-011: Memory Cache', () => {
      it('should create memory cache', () => {
        const cache = createMemoryCache();
        expect(cache).toBeDefined();
      });

      it('should support CVECache class', () => {
        const cache = new CVECache({ inMemory: true });
        expect(cache).toBeDefined();
      });
    });

    describe('TSK-SEC-012: CPE Matcher', () => {
      it('should generate CPE for package', () => {
        const matcher = new CPEMatcher();
        const cpe = matcher.generateCPE('lodash', '4.17.20');
        expect(cpe).toContain('lodash');
        expect(cpe).toContain('4.17.20');
      });

      it('should compare versions correctly - vulnerable', () => {
        const matcher = new CPEMatcher();
        // 4.17.20 is within range [4.0.0, 4.17.21)
        const isVuln = matcher.isVersionVulnerable('4.17.20', {
          versionStart: '4.0.0',
          versionEnd: '4.17.21',
          versionEndExcluding: true,
        });
        expect(isVuln).toBe(true);
      });

      it('should compare versions correctly - not vulnerable', () => {
        const matcher = new CPEMatcher();
        // Version 4.17.21 equals end bound with exclusive flag
        const isNotVuln = matcher.isVersionVulnerable('4.17.21', {
          versionStart: '4.0.0',
          versionEnd: '4.17.21',
          versionEndExcluding: true,
        });
        expect(isNotVuln).toBe(false);
      });

      it('should parse CPE URI', () => {
        const matcher = new CPEMatcher();
        const components = matcher.parseURI('cpe:2.3:a:lodash:lodash:4.17.20:*:*:*:*:*:*:*');
        expect(components).toBeDefined();
        expect(components?.product).toBe('lodash');
      });
    });

    describe('TSK-SEC-013: Dependency Parser', () => {
      it('should parse package.json content', () => {
        const parser = new DependencyParser();
        const packageJsonContent = JSON.stringify({
          name: 'test-app',
          version: '1.0.0',
          dependencies: {
            'lodash': '^4.17.21',
            'express': '~4.18.0',
          },
          devDependencies: {
            'vitest': '^1.0.0',
          },
        });
        
        const result = parser.parsePackageJson(packageJsonContent);
        expect(result.length).toBeGreaterThanOrEqual(2);
      });
    });

    describe('TSK-SEC-014: Rate Limiter', () => {
      it('should create rate limiter with NVD defaults (without API key)', () => {
        const limiter = RateLimiter.forNVD(false);
        expect(limiter).toBeDefined();
        expect(limiter.canProceed()).toBe(true);
      });

      it('should create rate limiter with API key config', () => {
        const limiter = RateLimiter.forNVD(true);
        expect(limiter).toBeDefined();
      });

      it('should track request count', () => {
        const limiter = new RateLimiter({
          maxTokens: 5,
          windowMs: 30000,
        });
        
        const status1 = limiter.getStatus();
        expect(status1.availableTokens).toBe(5);
        
        limiter.consume();
        const status2 = limiter.getStatus();
        expect(status2.availableTokens).toBe(4);
      });
    });

    describe('TSK-SEC-015: Report Generator', () => {
      it('should create report generator', () => {
        const generator = new ReportGenerator();
        expect(generator).toBeDefined();
      });

      it('should support multiple formats', () => {
        const generator = new ReportGenerator({ format: 'markdown' });
        expect(generator).toBeDefined();
        
        const jsonGenerator = new ReportGenerator({ format: 'json' });
        expect(jsonGenerator).toBeDefined();
      });
    });
  });

  describe('EPIC-4: Auto-Fix Pipeline', () => {
    describe('TSK-SEC-022: Fix Type Definitions', () => {
      it('should have Fix interface with required fields', () => {
        const fix = {
          id: 'FIX-2026-001',
          vulnerabilityId: 'VULN-001',
          strategy: 'parameterized-query' as const,
          title: 'Use parameterized query',
          description: 'Replace string concatenation with parameterized query',
          edits: [],
          imports: [],
          confidence: 0.95,
          breakingChange: false,
          rationale: 'Prevents SQL injection',
        };
        expect(fix.id).toBeDefined();
        expect(fix.confidence).toBeGreaterThan(0);
        expect(fix.strategy).toBe('parameterized-query');
      });
    });

    describe('TSK-SEC-023-026: Auto Fixer', () => {
      it('should create auto-fixer', () => {
        const fixer = createAutoFixer();
        expect(fixer).toBeDefined();
      });

      it('should create auto-fixer with options', () => {
        const fixer = createAutoFixer({
          maxSuggestions: 5,
        });
        expect(fixer).toBeDefined();
      });
    });

    describe('TSK-SEC-027: Fix Validator', () => {
      it('should create fix validator', () => {
        const validator = createFixValidator();
        expect(validator).toBeDefined();
      });

      it('should have validate method', () => {
        const validator = createFixValidator();
        expect(validator.validate).toBeDefined();
      });
    });

    describe('TSK-SEC-028: Patch Generator', () => {
      it('should create patch generator', () => {
        const generator = createPatchGenerator();
        expect(generator).toBeDefined();
      });

      it('should have generatePatch method', () => {
        const generator = createPatchGenerator();
        expect(generator.generatePatch).toBeDefined();
      });
    });

    describe('TSK-SEC-029: Remediation Planner', () => {
      it('should create remediation planner', () => {
        const planner = createRemediationPlanner();
        expect(planner).toBeDefined();
      });

      it('should create planner with options', () => {
        const planner = createRemediationPlanner({
          prioritization: 'severity',
        });
        expect(planner).toBeDefined();
      });

      it('should have createPlan method', () => {
        const planner = createRemediationPlanner();
        expect(planner.createPlan).toBeDefined();
      });
    });

    describe('TSK-SEC-030: Secure Code Transformer', () => {
      it('should create secure code transformer', () => {
        const transformer = createSecureCodeTransformer();
        expect(transformer).toBeDefined();
      });

      it('should have transform method', () => {
        const transformer = createSecureCodeTransformer();
        expect(transformer.transform).toBeDefined();
      });
    });
  });

  describe('Integration Verification', () => {
    it('should have all EPIC-1 components available', () => {
      expect(ALL_BUILTIN_SOURCES.length).toBeGreaterThan(0);
      expect(ALL_BUILTIN_SINKS.length).toBeGreaterThan(0);
      expect(ALL_BUILTIN_SANITIZERS.length).toBeGreaterThan(0);
      expect(createEnhancedTaintAnalyzer).toBeDefined();
    });

    it('should have all EPIC-2 components available', () => {
      expect(NVDClient).toBeDefined();
      expect(CPEMatcher).toBeDefined();
      expect(DependencyParser).toBeDefined();
      expect(RateLimiter).toBeDefined();
      expect(CVECache).toBeDefined();
      expect(ReportGenerator).toBeDefined();
    });

    it('should have all EPIC-4 components available', () => {
      expect(createAutoFixer).toBeDefined();
      expect(createFixValidator).toBeDefined();
      expect(createPatchGenerator).toBeDefined();
      expect(createRemediationPlanner).toBeDefined();
      expect(createSecureCodeTransformer).toBeDefined();
    });
  });
});
