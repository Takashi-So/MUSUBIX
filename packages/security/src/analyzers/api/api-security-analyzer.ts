/**
 * @fileoverview API Security Analyzer - OpenAPI/REST API security analysis
 * @module @nahisaho/musubix-security/analyzers/api/api-security-analyzer
 * @trace DES-SEC3-API-001, REQ-SEC3-API-001
 */

import type { Vulnerability, Severity, OWASPCategory } from '../../types/vulnerability.js';

/**
 * API endpoint information
 */
export interface APIEndpoint {
  path: string;
  method: 'GET' | 'POST' | 'PUT' | 'PATCH' | 'DELETE' | 'OPTIONS' | 'HEAD';
  operationId?: string;
  summary?: string;
  tags?: string[];
  parameters?: APIParameter[];
  requestBody?: APIRequestBody;
  responses?: Record<string, APIResponse>;
  security?: SecurityRequirement[];
}

/**
 * API parameter
 */
export interface APIParameter {
  name: string;
  in: 'path' | 'query' | 'header' | 'cookie';
  required?: boolean;
  schema?: SchemaObject;
  description?: string;
}

/**
 * API request body
 */
export interface APIRequestBody {
  required?: boolean;
  content?: Record<string, { schema?: SchemaObject }>;
}

/**
 * API response
 */
export interface APIResponse {
  description: string;
  content?: Record<string, { schema?: SchemaObject }>;
}

/**
 * Schema object (simplified)
 */
export interface SchemaObject {
  type?: string;
  format?: string;
  pattern?: string;
  minimum?: number;
  maximum?: number;
  minLength?: number;
  maxLength?: number;
  enum?: any[];
  properties?: Record<string, SchemaObject>;
  required?: string[];
  items?: SchemaObject;
}

/**
 * Security requirement
 */
export interface SecurityRequirement {
  [name: string]: string[];
}

/**
 * API security issue
 */
export interface APISecurityIssue {
  id: string;
  severity: Severity;
  category: APISecurityCategory;
  endpoint?: string;
  method?: string;
  title: string;
  description: string;
  recommendation: string;
  owasp?: string[];
  cwe?: string[];
}

/**
 * API security category
 */
export type APISecurityCategory =
  | 'authentication'
  | 'authorization'
  | 'injection'
  | 'data-exposure'
  | 'rate-limiting'
  | 'cors'
  | 'transport-security'
  | 'input-validation'
  | 'error-handling'
  | 'logging'
  | 'deprecated-api'
  | 'misconfiguration';

/**
 * API security analysis result
 */
export interface APISecurityResult {
  timestamp: Date;
  specVersion?: string;
  title?: string;
  endpoints: number;
  issues: APISecurityIssue[];
  coverage: SecurityCoverage;
  score: number;
  summary: APISecuritySummary;
}

/**
 * Security coverage metrics
 */
export interface SecurityCoverage {
  endpointsWithAuth: number;
  endpointsWithoutAuth: number;
  endpointsWithValidation: number;
  endpointsWithRateLimiting: number;
  totalEndpoints: number;
  authCoverage: number;
  validationCoverage: number;
}

/**
 * API security summary
 */
export interface APISecuritySummary {
  criticalIssues: number;
  highIssues: number;
  mediumIssues: number;
  lowIssues: number;
  topCategories: Array<{ category: APISecurityCategory; count: number }>;
  recommendations: string[];
}

/**
 * API security analyzer options
 */
export interface APISecurityOptions {
  checkAuth?: boolean;
  checkInjection?: boolean;
  checkDataExposure?: boolean;
  checkRateLimiting?: boolean;
  checkCORS?: boolean;
  skipPaths?: string[];
  customRules?: APISecurityRule[];
}

/**
 * Custom API security rule
 */
export interface APISecurityRule {
  id: string;
  name: string;
  severity: Severity;
  category: APISecurityCategory;
  check: (endpoint: APIEndpoint, spec: OpenAPISpec) => boolean;
  message: string;
  recommendation: string;
}

/**
 * OpenAPI specification (simplified)
 */
export interface OpenAPISpec {
  openapi?: string;
  swagger?: string;
  info?: {
    title?: string;
    version?: string;
  };
  servers?: Array<{ url: string; description?: string }>;
  paths?: Record<string, PathItem>;
  components?: {
    securitySchemes?: Record<string, SecurityScheme>;
    schemas?: Record<string, SchemaObject>;
  };
  security?: SecurityRequirement[];
}

/**
 * Path item
 */
interface PathItem {
  get?: OperationObject;
  post?: OperationObject;
  put?: OperationObject;
  patch?: OperationObject;
  delete?: OperationObject;
  options?: OperationObject;
  head?: OperationObject;
  parameters?: APIParameter[];
}

/**
 * Operation object
 */
interface OperationObject {
  operationId?: string;
  summary?: string;
  description?: string;
  tags?: string[];
  parameters?: APIParameter[];
  requestBody?: APIRequestBody;
  responses?: Record<string, APIResponse>;
  security?: SecurityRequirement[];
  deprecated?: boolean;
}

/**
 * Security scheme
 */
interface SecurityScheme {
  type: 'apiKey' | 'http' | 'oauth2' | 'openIdConnect';
  description?: string;
  name?: string;
  in?: 'query' | 'header' | 'cookie';
  scheme?: string;
  bearerFormat?: string;
}

/**
 * Built-in security rules
 */
const BUILTIN_RULES: Array<{
  id: string;
  name: string;
  category: APISecurityCategory;
  severity: Severity;
  check: (endpoint: APIEndpoint, spec: OpenAPISpec) => boolean;
  message: string;
  recommendation: string;
  owasp: string[];
  cwe: string[];
}> = [
  // Authentication rules
  {
    id: 'API-001',
    name: 'Missing Authentication',
    category: 'authentication',
    severity: 'high',
    check: (endpoint, spec) => {
      const hasGlobalAuth = spec.security && spec.security.length > 0;
      const hasEndpointAuth = endpoint.security && endpoint.security.length > 0;
      const isPublicPath = endpoint.path.includes('/health') || 
                           endpoint.path.includes('/public') ||
                           endpoint.path.includes('/docs');
      return !hasGlobalAuth && !hasEndpointAuth && !isPublicPath;
    },
    message: 'Endpoint has no authentication requirement',
    recommendation: 'Add authentication security scheme to protect this endpoint',
    owasp: ['A07:2021'],
    cwe: ['CWE-306'],
  },
  {
    id: 'API-002',
    name: 'Weak Authentication Scheme',
    category: 'authentication',
    severity: 'medium',
    check: (endpoint, spec) => {
      const schemes = spec.components?.securitySchemes ?? {};
      const usedSchemes = [...(spec.security ?? []), ...(endpoint.security ?? [])];
      
      for (const req of usedSchemes) {
        for (const schemeName of Object.keys(req)) {
          const scheme = schemes[schemeName];
          if (scheme?.type === 'apiKey' && scheme.in === 'query') {
            return true;
          }
          if (scheme?.type === 'http' && scheme.scheme === 'basic') {
            return true;
          }
        }
      }
      return false;
    },
    message: 'Endpoint uses weak authentication (API key in query or Basic Auth)',
    recommendation: 'Use Bearer tokens or OAuth2 for better security',
    owasp: ['A07:2021'],
    cwe: ['CWE-287'],
  },
  // Authorization rules
  {
    id: 'API-003',
    name: 'Missing Scope/Permission Check',
    category: 'authorization',
    severity: 'medium',
    check: (endpoint, spec) => {
      const security = endpoint.security ?? spec.security ?? [];
      // Check if any OAuth2 scope is defined
      for (const req of security) {
        for (const scopes of Object.values(req)) {
          if (Array.isArray(scopes) && scopes.length > 0) {
            return false;
          }
        }
      }
      // Sensitive operations should have scopes
      const sensitiveOps = ['POST', 'PUT', 'PATCH', 'DELETE'];
      return sensitiveOps.includes(endpoint.method);
    },
    message: 'Sensitive operation lacks specific permission scopes',
    recommendation: 'Define OAuth2 scopes or permission requirements for sensitive operations',
    owasp: ['A01:2021'],
    cwe: ['CWE-285'],
  },
  // Injection rules
  {
    id: 'API-004',
    name: 'Missing Input Validation',
    category: 'input-validation',
    severity: 'high',
    check: (endpoint) => {
      const params = endpoint.parameters ?? [];
      for (const param of params) {
        if (!param.schema) return true;
        const schema = param.schema;
        // Check if string params have validation
        if (schema.type === 'string' && !schema.pattern && !schema.maxLength && !schema.enum) {
          return true;
        }
      }
      return false;
    },
    message: 'Input parameters lack validation constraints',
    recommendation: 'Add pattern, maxLength, or enum constraints to string parameters',
    owasp: ['A03:2021'],
    cwe: ['CWE-20'],
  },
  {
    id: 'API-005',
    name: 'SQL Injection Risk',
    category: 'injection',
    severity: 'critical',
    check: (endpoint) => {
      // Check for dangerous parameter patterns
      const dangerousPatterns = ['query', 'filter', 'where', 'orderBy', 'sortBy', 'search'];
      const params = endpoint.parameters ?? [];
      
      for (const param of params) {
        if (dangerousPatterns.some(p => param.name.toLowerCase().includes(p))) {
          if (!param.schema?.pattern && !param.schema?.enum) {
            return true;
          }
        }
      }
      return false;
    },
    message: 'Query/filter parameter without validation may allow SQL injection',
    recommendation: 'Validate and sanitize query parameters; use parameterized queries',
    owasp: ['A03:2021'],
    cwe: ['CWE-89'],
  },
  // Data exposure rules
  {
    id: 'API-006',
    name: 'Sensitive Data in Response',
    category: 'data-exposure',
    severity: 'high',
    check: (endpoint) => {
      const sensitiveFields = ['password', 'secret', 'token', 'ssn', 'credit_card', 'cvv'];
      const responses = endpoint.responses ?? {};
      
      for (const [code, response] of Object.entries(responses)) {
        if (!code.startsWith('2')) continue;
        
        for (const mediaType of Object.values(response.content ?? {})) {
          const schema = mediaType.schema;
          if (schema?.properties) {
            for (const prop of Object.keys(schema.properties)) {
              if (sensitiveFields.some(s => prop.toLowerCase().includes(s))) {
                return true;
              }
            }
          }
        }
      }
      return false;
    },
    message: 'Response may contain sensitive data fields',
    recommendation: 'Remove sensitive fields from API responses or mask them',
    owasp: ['A01:2021'],
    cwe: ['CWE-200'],
  },
  {
    id: 'API-007',
    name: 'Missing Rate Limiting Header',
    category: 'rate-limiting',
    severity: 'medium',
    check: (endpoint) => {
      const responses = endpoint.responses ?? {};
      const hasRateLimitHeader = Object.values(responses).some(r => 
        r.description?.toLowerCase().includes('rate limit')
      );
      return !hasRateLimitHeader && endpoint.method === 'POST';
    },
    message: 'No rate limiting documented for POST endpoint',
    recommendation: 'Implement and document rate limiting headers (X-RateLimit-*)',
    owasp: ['A05:2021'],
    cwe: ['CWE-770'],
  },
  // Transport security
  {
    id: 'API-008',
    name: 'HTTP Server URL',
    category: 'transport-security',
    severity: 'high',
    check: (_endpoint, spec) => {
      const servers = spec.servers ?? [];
      return servers.some(s => s.url.startsWith('http://') && !s.url.includes('localhost'));
    },
    message: 'API server uses insecure HTTP protocol',
    recommendation: 'Use HTTPS for all API communications',
    owasp: ['A02:2021'],
    cwe: ['CWE-319'],
  },
  // Error handling
  {
    id: 'API-009',
    name: 'Missing Error Response Schema',
    category: 'error-handling',
    severity: 'low',
    check: (endpoint) => {
      const responses = endpoint.responses ?? {};
      const hasErrorSchema = Object.entries(responses).some(([code, r]) => {
        const isError = code.startsWith('4') || code.startsWith('5');
        return isError && r.content;
      });
      return !hasErrorSchema;
    },
    message: 'Error responses lack schema definition',
    recommendation: 'Define error response schemas to ensure consistent error handling',
    owasp: ['A09:2021'],
    cwe: ['CWE-209'],
  },
  // Deprecated API
  {
    id: 'API-010',
    name: 'Deprecated Endpoint',
    category: 'deprecated-api',
    severity: 'info',
    check: (endpoint, spec) => {
      // Check in the spec if operation is marked deprecated
      const paths = spec.paths ?? {};
      const pathItem = paths[endpoint.path];
      if (!pathItem) return false;
      
      const method = endpoint.method.toLowerCase() as keyof PathItem;
      const operation = pathItem[method] as OperationObject | undefined;
      return operation?.deprecated === true;
    },
    message: 'Endpoint is marked as deprecated',
    recommendation: 'Plan migration to the replacement API; document deprecation timeline',
    owasp: ['A09:2021'],
    cwe: ['CWE-1104'],
  },
  // CORS
  {
    id: 'API-011',
    name: 'Missing CORS Configuration',
    category: 'cors',
    severity: 'medium',
    check: (endpoint, spec) => {
      // If there's no OPTIONS handler for paths, CORS might not be configured
      const paths = spec.paths ?? {};
      const pathItem = paths[endpoint.path];
      if (!pathItem) return false;
      return !pathItem.options;
    },
    message: 'No OPTIONS method defined for CORS preflight',
    recommendation: 'Configure CORS headers and OPTIONS handler appropriately',
    owasp: ['A05:2021'],
    cwe: ['CWE-942'],
  },
  // Misconfiguration
  {
    id: 'API-012',
    name: 'Missing Content-Type Validation',
    category: 'misconfiguration',
    severity: 'medium',
    check: (endpoint) => {
      if (!endpoint.requestBody) return false;
      const content = endpoint.requestBody.content ?? {};
      // Check if only specific content types are accepted
      return Object.keys(content).includes('*/*');
    },
    message: 'Endpoint accepts any content type',
    recommendation: 'Restrict accepted content types to prevent content type confusion attacks',
    owasp: ['A05:2021'],
    cwe: ['CWE-436'],
  },
];

/**
 * API Security Analyzer
 * @trace DES-SEC3-API-001
 */
export class APISecurityAnalyzer {
  private options: Required<APISecurityOptions>;
  private rules: typeof BUILTIN_RULES;

  constructor(options: APISecurityOptions = {}) {
    this.options = {
      checkAuth: options.checkAuth ?? true,
      checkInjection: options.checkInjection ?? true,
      checkDataExposure: options.checkDataExposure ?? true,
      checkRateLimiting: options.checkRateLimiting ?? true,
      checkCORS: options.checkCORS ?? true,
      skipPaths: options.skipPaths ?? [],
      customRules: options.customRules ?? [],
    };

    this.rules = [...BUILTIN_RULES];
  }

  /**
   * Analyze OpenAPI specification
   * @trace REQ-SEC3-API-001
   */
  async analyze(spec: OpenAPISpec | string): Promise<APISecurityResult> {
    const parsedSpec: OpenAPISpec = typeof spec === 'string' ? JSON.parse(spec) : spec;
    
    const endpoints = this.extractEndpoints(parsedSpec);
    const issues: APISecurityIssue[] = [];

    // Filter endpoints
    const filteredEndpoints = endpoints.filter(
      ep => !this.options.skipPaths.some(p => ep.path.startsWith(p))
    );

    // Run rules on each endpoint
    for (const endpoint of filteredEndpoints) {
      for (const rule of this.rules) {
        // Skip rules based on options
        if (!this.shouldRunRule(rule.category)) continue;

        try {
          if (rule.check(endpoint, parsedSpec)) {
            issues.push({
              id: `${rule.id}-${endpoint.method}-${endpoint.path.replace(/\//g, '-')}`,
              severity: rule.severity,
              category: rule.category,
              endpoint: endpoint.path,
              method: endpoint.method,
              title: rule.name,
              description: rule.message,
              recommendation: rule.recommendation,
              owasp: rule.owasp,
              cwe: rule.cwe,
            });
          }
        } catch {
          // Ignore rule errors
        }
      }
    }

    // Run custom rules
    for (const customRule of this.options.customRules) {
      for (const endpoint of filteredEndpoints) {
        try {
          if (customRule.check(endpoint, parsedSpec)) {
            issues.push({
              id: `${customRule.id}-${endpoint.method}-${endpoint.path.replace(/\//g, '-')}`,
              severity: customRule.severity,
              category: customRule.category,
              endpoint: endpoint.path,
              method: endpoint.method,
              title: customRule.name,
              description: customRule.message,
              recommendation: customRule.recommendation,
            });
          }
        } catch {
          // Ignore rule errors
        }
      }
    }

    const coverage = this.calculateCoverage(filteredEndpoints, parsedSpec);
    const score = this.calculateScore(issues, coverage);

    return {
      timestamp: new Date(),
      specVersion: parsedSpec.openapi ?? parsedSpec.swagger,
      title: parsedSpec.info?.title,
      endpoints: filteredEndpoints.length,
      issues,
      coverage,
      score,
      summary: this.generateSummary(issues),
    };
  }

  /**
   * Analyze from file path
   */
  async analyzeFile(filePath: string): Promise<APISecurityResult> {
    const fs = await import('node:fs');
    const content = fs.readFileSync(filePath, 'utf-8');
    
    // Try JSON first, then YAML
    let spec: OpenAPISpec;
    try {
      spec = JSON.parse(content);
    } catch {
      // Try basic YAML parsing (simplified)
      spec = this.parseSimpleYaml(content);
    }
    
    return this.analyze(spec);
  }

  /**
   * Extract endpoints from spec
   */
  private extractEndpoints(spec: OpenAPISpec): APIEndpoint[] {
    const endpoints: APIEndpoint[] = [];
    const paths = spec.paths ?? {};

    for (const [path, pathItem] of Object.entries(paths)) {
      const methods = ['get', 'post', 'put', 'patch', 'delete', 'options', 'head'] as const;
      
      for (const method of methods) {
        const operation = pathItem[method] as OperationObject | undefined;
        if (!operation) continue;

        endpoints.push({
          path,
          method: method.toUpperCase() as APIEndpoint['method'],
          operationId: operation.operationId,
          summary: operation.summary,
          tags: operation.tags,
          parameters: [...(pathItem.parameters ?? []), ...(operation.parameters ?? [])],
          requestBody: operation.requestBody,
          responses: operation.responses,
          security: operation.security,
        });
      }
    }

    return endpoints;
  }

  /**
   * Check if rule should run based on options
   */
  private shouldRunRule(category: APISecurityCategory): boolean {
    switch (category) {
      case 'authentication':
      case 'authorization':
        return this.options.checkAuth;
      case 'injection':
      case 'input-validation':
        return this.options.checkInjection;
      case 'data-exposure':
        return this.options.checkDataExposure;
      case 'rate-limiting':
        return this.options.checkRateLimiting;
      case 'cors':
        return this.options.checkCORS;
      default:
        return true;
    }
  }

  /**
   * Calculate security coverage
   */
  private calculateCoverage(
    endpoints: APIEndpoint[],
    spec: OpenAPISpec
  ): SecurityCoverage {
    let withAuth = 0;
    let withValidation = 0;
    let withRateLimiting = 0;

    const globalAuth = spec.security && spec.security.length > 0;

    for (const endpoint of endpoints) {
      const hasAuth = globalAuth || (endpoint.security && endpoint.security.length > 0);
      if (hasAuth) withAuth++;

      const hasValidation = endpoint.parameters?.some(p => 
        p.schema?.pattern || p.schema?.maxLength || p.schema?.enum
      );
      if (hasValidation) withValidation++;

      // Check for rate limit documentation
      const hasRateLimit = Object.values(endpoint.responses ?? {}).some(r =>
        r.description?.toLowerCase().includes('rate')
      );
      if (hasRateLimit) withRateLimiting++;
    }

    const total = endpoints.length;
    return {
      endpointsWithAuth: withAuth,
      endpointsWithoutAuth: total - withAuth,
      endpointsWithValidation: withValidation,
      endpointsWithRateLimiting: withRateLimiting,
      totalEndpoints: total,
      authCoverage: total > 0 ? Math.round((withAuth / total) * 100) : 100,
      validationCoverage: total > 0 ? Math.round((withValidation / total) * 100) : 100,
    };
  }

  /**
   * Calculate security score
   */
  private calculateScore(
    issues: APISecurityIssue[],
    coverage: SecurityCoverage
  ): number {
    let score = 100;

    // Deduct for issues
    for (const issue of issues) {
      switch (issue.severity) {
        case 'critical':
          score -= 15;
          break;
        case 'high':
          score -= 10;
          break;
        case 'medium':
          score -= 5;
          break;
        case 'low':
          score -= 2;
          break;
      }
    }

    // Deduct for poor coverage
    if (coverage.authCoverage < 100) {
      score -= Math.round((100 - coverage.authCoverage) / 10);
    }
    if (coverage.validationCoverage < 50) {
      score -= 10;
    }

    return Math.max(0, Math.min(100, score));
  }

  /**
   * Generate summary
   */
  private generateSummary(issues: APISecurityIssue[]): APISecuritySummary {
    const counts = { critical: 0, high: 0, medium: 0, low: 0, info: 0 };
    const categoryCount: Record<string, number> = {};
    const recommendations = new Set<string>();

    for (const issue of issues) {
      if (issue.severity in counts) {
        counts[issue.severity as keyof typeof counts]++;
      }

      categoryCount[issue.category] = (categoryCount[issue.category] ?? 0) + 1;
      recommendations.add(issue.recommendation);
    }

    const topCategories = Object.entries(categoryCount)
      .sort(([, a], [, b]) => b - a)
      .slice(0, 5)
      .map(([category, count]) => ({ category: category as APISecurityCategory, count }));

    return {
      criticalIssues: counts.critical,
      highIssues: counts.high,
      mediumIssues: counts.medium,
      lowIssues: counts.low + counts.info,
      topCategories,
      recommendations: Array.from(recommendations).slice(0, 5),
    };
  }

  /**
   * Simple YAML parser (for basic OpenAPI specs)
   */
  private parseSimpleYaml(content: string): OpenAPISpec {
    // This is a very simplified parser - in production, use js-yaml
    const spec: OpenAPISpec = {};
    
    const lines = content.split('\n');
    let currentPath = '';
    let currentMethod = '';

    for (const line of lines) {
      const trimmed = line.trim();
      
      // Skip comments and empty lines
      if (trimmed.startsWith('#') || !trimmed) continue;

      // Detect openapi version
      if (trimmed.startsWith('openapi:')) {
        spec.openapi = trimmed.split(':')[1]?.trim().replace(/['"]/g, '');
      }
      
      // Detect swagger version
      if (trimmed.startsWith('swagger:')) {
        spec.swagger = trimmed.split(':')[1]?.trim().replace(/['"]/g, '');
      }

      // Detect paths
      if (trimmed.match(/^\/[^:]*:/)) {
        currentPath = trimmed.replace(':', '');
        if (!spec.paths) spec.paths = {};
        spec.paths[currentPath] = {};
      }

      // Detect methods under paths
      if (currentPath && ['get:', 'post:', 'put:', 'patch:', 'delete:'].includes(trimmed)) {
        currentMethod = trimmed.replace(':', '');
        if (spec.paths?.[currentPath]) {
          (spec.paths[currentPath] as any)[currentMethod] = {};
        }
      }
    }

    return spec;
  }

  /**
   * Convert issues to vulnerabilities
   */
  toVulnerabilities(result: APISecurityResult): Vulnerability[] {
    return result.issues.map(issue => ({
      id: issue.id,
      type: 'configuration' as const,
      severity: issue.severity,
      cwes: issue.cwe ?? [],
      owasp: (issue.owasp ?? []) as OWASPCategory[],
      location: {
        file: 'openapi.json',
        startLine: 1,
        endLine: 1,
        startColumn: 0,
        endColumn: 0,
      },
      description: `[${issue.method} ${issue.endpoint}] ${issue.title}: ${issue.description}`,
      recommendation: issue.recommendation,
      confidence: 0.9,
      ruleId: issue.id,
      codeSnippet: `${issue.method} ${issue.endpoint}`,
      detectedAt: new Date(),
    }));
  }
}

/**
 * Create API security analyzer instance
 */
export function createAPISecurityAnalyzer(options?: APISecurityOptions): APISecurityAnalyzer {
  return new APISecurityAnalyzer(options);
}
