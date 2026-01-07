/**
 * @fileoverview Phase 3 - API Security Analyzer Tests
 * @module @nahisaho/musubix-security/tests/phase3/api-security-analyzer.test
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  APISecurityAnalyzer,
  createAPISecurityAnalyzer,
  type OpenAPISpec,
  type APISecurityResult,
} from '../../src/analyzers/api/api-security-analyzer.js';

describe('APISecurityAnalyzer', () => {
  let analyzer: APISecurityAnalyzer;

  const sampleSpec: OpenAPISpec = {
    openapi: '3.0.0',
    info: {
      title: 'Test API',
      version: '1.0.0',
    },
    servers: [
      { url: 'https://api.example.com', description: 'Production' },
    ],
    paths: {
      '/users': {
        get: {
          operationId: 'getUsers',
          summary: 'Get all users',
          responses: {
            '200': {
              description: 'Success',
              content: {
                'application/json': {
                  schema: {
                    type: 'array',
                    items: { type: 'object' },
                  },
                },
              },
            },
          },
          security: [{ bearerAuth: [] }],
        },
        post: {
          operationId: 'createUser',
          summary: 'Create a user',
          requestBody: {
            required: true,
            content: {
              'application/json': {
                schema: {
                  type: 'object',
                  properties: {
                    name: { type: 'string', maxLength: 100 },
                    email: { type: 'string', format: 'email' },
                  },
                },
              },
            },
          },
          responses: {
            '201': { description: 'Created' },
          },
          security: [{ bearerAuth: ['users:write'] }],
        },
      },
      '/users/{id}': {
        get: {
          operationId: 'getUser',
          summary: 'Get a user by ID',
          parameters: [
            {
              name: 'id',
              in: 'path',
              required: true,
              schema: { type: 'string', pattern: '^[a-f0-9-]+$' },
            },
          ],
          responses: {
            '200': { description: 'Success' },
          },
          security: [{ bearerAuth: [] }],
        },
      },
      '/public/health': {
        get: {
          operationId: 'healthCheck',
          summary: 'Health check endpoint',
          responses: {
            '200': { description: 'OK' },
          },
        },
      },
    },
    components: {
      securitySchemes: {
        bearerAuth: {
          type: 'http',
          scheme: 'bearer',
          bearerFormat: 'JWT',
        },
      },
    },
  };

  beforeEach(() => {
    analyzer = createAPISecurityAnalyzer();
  });

  describe('constructor and factory', () => {
    it('should create analyzer with default options', () => {
      const a = new APISecurityAnalyzer();
      expect(a).toBeInstanceOf(APISecurityAnalyzer);
    });

    it('should create analyzer with custom options', () => {
      const a = createAPISecurityAnalyzer({
        checkAuth: false,
        checkInjection: true,
        skipPaths: ['/internal/*'],
      });
      expect(a).toBeInstanceOf(APISecurityAnalyzer);
    });
  });

  describe('analyze', () => {
    it('should analyze OpenAPI spec object', async () => {
      const result = await analyzer.analyze(sampleSpec);
      
      expect(result).toBeDefined();
      expect(result.timestamp).toBeInstanceOf(Date);
      expect(result.specVersion).toBe('3.0.0');
      expect(result.title).toBe('Test API');
    });

    it('should analyze OpenAPI spec string', async () => {
      const result = await analyzer.analyze(JSON.stringify(sampleSpec));
      
      expect(result).toBeDefined();
      expect(result.specVersion).toBe('3.0.0');
    });

    it('should count endpoints correctly', async () => {
      const result = await analyzer.analyze(sampleSpec);
      
      // 4 operations: GET /users, POST /users, GET /users/{id}, GET /public/health
      expect(result.endpoints).toBe(4);
    });

    it('should identify issues', async () => {
      const result = await analyzer.analyze(sampleSpec);
      
      expect(Array.isArray(result.issues)).toBe(true);
    });

    it('should calculate security coverage', async () => {
      const result = await analyzer.analyze(sampleSpec);
      
      expect(result.coverage).toBeDefined();
      expect(typeof result.coverage.authCoverage).toBe('number');
      expect(typeof result.coverage.validationCoverage).toBe('number');
    });

    it('should calculate security score', async () => {
      const result = await analyzer.analyze(sampleSpec);
      
      expect(typeof result.score).toBe('number');
      expect(result.score).toBeGreaterThanOrEqual(0);
      expect(result.score).toBeLessThanOrEqual(100);
    });

    it('should generate summary', async () => {
      const result = await analyzer.analyze(sampleSpec);
      
      expect(result.summary).toBeDefined();
      expect(typeof result.summary.criticalIssues).toBe('number');
      expect(typeof result.summary.highIssues).toBe('number');
      expect(typeof result.summary.mediumIssues).toBe('number');
      expect(typeof result.summary.lowIssues).toBe('number');
    });
  });

  describe('authentication checks', () => {
    it('should detect missing authentication on non-public endpoints', async () => {
      const specWithoutAuth: OpenAPISpec = {
        openapi: '3.0.0',
        info: { title: 'Test', version: '1.0.0' },
        paths: {
          '/users': {
            get: {
              operationId: 'getUsers',
              responses: { '200': { description: 'OK' } },
            },
          },
        },
      };

      const result = await analyzer.analyze(specWithoutAuth);
      
      const authIssues = result.issues.filter(i => i.category === 'authentication');
      expect(authIssues.length).toBeGreaterThan(0);
    });

    it('should not flag public/health endpoints for missing auth', async () => {
      const result = await analyzer.analyze(sampleSpec);
      
      const healthAuthIssues = result.issues.filter(
        i => i.category === 'authentication' && i.endpoint?.includes('/public/health')
      );
      expect(healthAuthIssues.length).toBe(0);
    });

    it('should detect weak authentication schemes', async () => {
      const specWithWeakAuth: OpenAPISpec = {
        openapi: '3.0.0',
        info: { title: 'Test', version: '1.0.0' },
        paths: {
          '/users': {
            get: {
              operationId: 'getUsers',
              responses: { '200': { description: 'OK' } },
              security: [{ apiKey: [] }],
            },
          },
        },
        components: {
          securitySchemes: {
            apiKey: {
              type: 'apiKey',
              in: 'query',
              name: 'api_key',
            },
          },
        },
      };

      const result = await analyzer.analyze(specWithWeakAuth);
      
      const weakAuthIssues = result.issues.filter(
        i => i.title.toLowerCase().includes('weak')
      );
      expect(weakAuthIssues.length).toBeGreaterThan(0);
    });
  });

  describe('input validation checks', () => {
    it('should detect missing input validation', async () => {
      const specWithoutValidation: OpenAPISpec = {
        openapi: '3.0.0',
        info: { title: 'Test', version: '1.0.0' },
        paths: {
          '/search': {
            get: {
              operationId: 'search',
              parameters: [
                {
                  name: 'query',
                  in: 'query',
                  schema: { type: 'string' }, // No pattern, maxLength, or enum
                },
              ],
              responses: { '200': { description: 'OK' } },
              security: [{ bearerAuth: [] }],
            },
          },
        },
        components: {
          securitySchemes: {
            bearerAuth: { type: 'http', scheme: 'bearer' },
          },
        },
      };

      const result = await analyzer.analyze(specWithoutValidation);
      
      const validationIssues = result.issues.filter(
        i => i.category === 'input-validation'
      );
      expect(validationIssues.length).toBeGreaterThan(0);
    });

    it('should not flag validated parameters', async () => {
      const result = await analyzer.analyze(sampleSpec);
      
      // The /users/{id} endpoint has pattern validation
      const idValidationIssues = result.issues.filter(
        i => i.category === 'input-validation' && i.endpoint === '/users/{id}'
      );
      // Should not have issues since pattern is defined
      expect(idValidationIssues.length).toBe(0);
    });
  });

  describe('injection checks', () => {
    it('should detect SQL injection risk in query parameters', async () => {
      const specWithSqlRisk: OpenAPISpec = {
        openapi: '3.0.0',
        info: { title: 'Test', version: '1.0.0' },
        paths: {
          '/users': {
            get: {
              operationId: 'getUsers',
              parameters: [
                {
                  name: 'filter',
                  in: 'query',
                  schema: { type: 'string' }, // Dangerous: no validation on filter param
                },
              ],
              responses: { '200': { description: 'OK' } },
              security: [{ bearerAuth: [] }],
            },
          },
        },
        components: {
          securitySchemes: {
            bearerAuth: { type: 'http', scheme: 'bearer' },
          },
        },
      };

      const result = await analyzer.analyze(specWithSqlRisk);
      
      const injectionIssues = result.issues.filter(
        i => i.category === 'injection'
      );
      expect(injectionIssues.length).toBeGreaterThan(0);
    });
  });

  describe('data exposure checks', () => {
    it('should detect sensitive data in responses', async () => {
      const specWithSensitiveData: OpenAPISpec = {
        openapi: '3.0.0',
        info: { title: 'Test', version: '1.0.0' },
        paths: {
          '/users': {
            get: {
              operationId: 'getUsers',
              responses: {
                '200': {
                  description: 'OK',
                  content: {
                    'application/json': {
                      schema: {
                        type: 'object',
                        properties: {
                          id: { type: 'string' },
                          name: { type: 'string' },
                          password: { type: 'string' }, // Sensitive!
                        },
                      },
                    },
                  },
                },
              },
              security: [{ bearerAuth: [] }],
            },
          },
        },
        components: {
          securitySchemes: {
            bearerAuth: { type: 'http', scheme: 'bearer' },
          },
        },
      };

      const result = await analyzer.analyze(specWithSensitiveData);
      
      const dataExposureIssues = result.issues.filter(
        i => i.category === 'data-exposure'
      );
      expect(dataExposureIssues.length).toBeGreaterThan(0);
    });
  });

  describe('transport security checks', () => {
    it('should detect HTTP server URLs', async () => {
      const specWithHttp: OpenAPISpec = {
        openapi: '3.0.0',
        info: { title: 'Test', version: '1.0.0' },
        servers: [
          { url: 'http://api.example.com' }, // Should flag
        ],
        paths: {
          '/test': {
            get: {
              operationId: 'test',
              responses: { '200': { description: 'OK' } },
            },
          },
        },
      };

      const result = await analyzer.analyze(specWithHttp);
      
      const transportIssues = result.issues.filter(
        i => i.category === 'transport-security'
      );
      expect(transportIssues.length).toBeGreaterThan(0);
    });

    it('should not flag localhost HTTP', async () => {
      const specWithLocalhost: OpenAPISpec = {
        openapi: '3.0.0',
        info: { title: 'Test', version: '1.0.0' },
        servers: [
          { url: 'http://localhost:3000' }, // OK for development
        ],
        paths: {
          '/test': {
            get: {
              operationId: 'test',
              responses: { '200': { description: 'OK' } },
            },
          },
        },
      };

      const result = await analyzer.analyze(specWithLocalhost);
      
      const transportIssues = result.issues.filter(
        i => i.category === 'transport-security'
      );
      expect(transportIssues.length).toBe(0);
    });
  });

  describe('skip paths', () => {
    it('should skip configured paths', async () => {
      const a = createAPISecurityAnalyzer({
        skipPaths: ['/public'],
      });

      const result = await a.analyze(sampleSpec);
      
      // Should not have issues for /public/health
      const publicIssues = result.issues.filter(
        i => i.endpoint?.startsWith('/public')
      );
      expect(publicIssues.length).toBe(0);
    });
  });

  describe('toVulnerabilities', () => {
    it('should convert issues to vulnerabilities', async () => {
      const result = await analyzer.analyze(sampleSpec);
      const vulnerabilities = analyzer.toVulnerabilities(result);
      
      expect(Array.isArray(vulnerabilities)).toBe(true);
      expect(vulnerabilities.length).toBe(result.issues.length);
    });

    it('should preserve severity in conversion', async () => {
      const result = await analyzer.analyze(sampleSpec);
      const vulnerabilities = analyzer.toVulnerabilities(result);
      
      for (const vuln of vulnerabilities) {
        expect(['critical', 'high', 'medium', 'low', 'info']).toContain(vuln.severity);
      }
    });

    it('should include OWASP references', async () => {
      const result = await analyzer.analyze(sampleSpec);
      const vulnerabilities = analyzer.toVulnerabilities(result);
      
      for (const vuln of vulnerabilities) {
        expect(Array.isArray(vuln.owasp)).toBe(true);
      }
    });

    it('should include CWE references', async () => {
      const result = await analyzer.analyze(sampleSpec);
      const vulnerabilities = analyzer.toVulnerabilities(result);
      
      for (const vuln of vulnerabilities) {
        expect(Array.isArray(vuln.cwes)).toBe(true);
      }
    });
  });

  describe('custom rules', () => {
    it('should apply custom rules', async () => {
      const a = createAPISecurityAnalyzer({
        customRules: [
          {
            id: 'CUSTOM-001',
            name: 'Custom Test Rule',
            severity: 'medium',
            category: 'misconfiguration',
            check: (endpoint) => endpoint.path === '/users',
            message: 'Custom rule triggered',
            recommendation: 'Fix the custom issue',
          },
        ],
      });

      const result = await a.analyze(sampleSpec);
      
      const customIssues = result.issues.filter(i => i.id.startsWith('CUSTOM-001'));
      expect(customIssues.length).toBeGreaterThan(0);
    });
  });
});
