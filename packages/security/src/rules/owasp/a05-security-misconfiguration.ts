/**
 * @fileoverview OWASP A05:2021 - Security Misconfiguration Rule
 * @module @nahisaho/musubix-security/rules/owasp/a05-security-misconfiguration
 * @trace TSK-RULE-003
 * 
 * Detects:
 * - Default credentials
 * - Verbose error messages
 * - Unnecessary features enabled
 * - Missing security headers
 * - Development settings in production
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

/**
 * OWASP A05 - Security Misconfiguration
 */
export const owaspA05SecurityMisconfiguration: SecurityRule = {
  id: 'owasp-a05-security-misconfiguration',
  name: 'OWASP A05:2021 - Security Misconfiguration',
  description: 'Detects security misconfigurations including default credentials, verbose errors, and insecure settings',
  defaultSeverity: 'high',
  detectionMethod: 'pattern-match',
  tags: ['owasp', 'configuration', 'defaults', 'headers', 'security'],
  owasp: ['A05:2021'],
  cwe: ['2', '11', '13', '15', '16', '260', '315', '520', '526', '537'],
  references: [
    { title: 'OWASP A05:2021 - Security Misconfiguration', url: 'https://owasp.org/Top10/A05_2021-Security_Misconfiguration/' },
    { title: 'CWE-16: Configuration', url: 'https://cwe.mitre.org/data/definitions/16.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const sourceFile = context.sourceFile;
    if (!sourceFile) return findings;

    // Check for default credentials
    checkDefaultCredentials(context, findings);
    
    // Check for verbose errors
    checkVerboseErrors(context, findings);
    
    // Check for unnecessary features
    checkUnnecessaryFeatures(context, findings);
    
    // Check for missing security headers
    checkMissingHeaders(context, findings);
    
    // Check for development settings
    checkDevSettings(context, findings);
    
    // Check for exposed environment
    checkExposedEnvironment(context, findings);

    return findings;
  },
};

/**
 * Check for default or hardcoded credentials
 */
function checkDefaultCredentials(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const defaultCredPatterns = [
    // Default passwords
    { pattern: /password\s*[:=]\s*['"`](?:password|admin|123456|root|default|test|demo)['"`]/gi, type: 'default password' },
    // Default usernames
    { pattern: /(?:username|user)\s*[:=]\s*['"`](?:admin|root|test|user|demo)['"`]/gi, type: 'default username' },
    // Default API keys (placeholder patterns)
    { pattern: /(?:api[_-]?key|apikey)\s*[:=]\s*['"`](?:xxx|test|demo|your[_-]?api[_-]?key)['"`]/gi, type: 'placeholder API key' },
    // Default tokens
    { pattern: /(?:token|secret)\s*[:=]\s*['"`](?:changeme|secret|default|test)['"`]/gi, type: 'default token' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    // Skip comments
    if (line.trim().startsWith('//') || line.trim().startsWith('*')) continue;
    
    for (const { pattern, type } of defaultCredPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a05-cred-${findings.length + 1}`,
          ruleId: 'owasp-a05-security-misconfiguration',
          severity: 'critical',
          message: `Default or hardcoded ${type} detected`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          suggestion: {
            description: 'Use environment variables for credentials',
            example: `// Use environment variables:
const password = process.env.DB_PASSWORD;
const apiKey = process.env.API_KEY;`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for verbose error messages
 */
function checkVerboseErrors(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const verboseErrorPatterns = [
    // Stack trace exposure
    { pattern: /(?:res\.send|res\.json)\s*\([^)]*(?:err\.stack|error\.stack)/gi, type: 'Stack trace in response' },
    // Full error object
    { pattern: /(?:res\.send|res\.json)\s*\(\s*(?:err|error)\s*\)/gi, type: 'Full error object in response' },
    // Internal error details
    { pattern: /(?:res\.send|res\.json)\s*\([^)]*(?:sql|query|database)/gi, type: 'Database details in response' },
    // Debug info in production
    { pattern: /console\.(?:log|error)\s*\([^)]*(?:password|secret|key|token)/gi, type: 'Sensitive data in console' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, type } of verboseErrorPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        // Check if there's environment check
        const surroundingCode = lines.slice(Math.max(0, lineNum - 5), lineNum + 1).join('\n');
        
        if (!hasProductionCheck(surroundingCode)) {
          findings.push({
            id: `owasp-a05-error-${findings.length + 1}`,
            ruleId: 'owasp-a05-security-misconfiguration',
            severity: 'medium',
            message: `Verbose error information: ${type}`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            suggestion: {
              description: 'Send generic errors in production',
              example: `// Send generic errors in production:
app.use((err, req, res, next) => {
  console.error(err); // Log internally
  const message = process.env.NODE_ENV === 'production'
    ? 'Internal Server Error'
    : err.message;
  res.status(500).json({ error: message });
});`,
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check for unnecessary features enabled
 */
function checkUnnecessaryFeatures(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const unnecessaryFeaturePatterns = [
    // X-Powered-By header (should be disabled)
    { pattern: /x-powered-by/gi, issue: 'X-Powered-By header exposed' },
    // Directory listing
    { pattern: /serveIndex|directory\s*listing|autoindex/gi, issue: 'Directory listing may be enabled' },
    // TRACE method (rarely needed)
    { pattern: /app\.trace\s*\(/gi, issue: 'TRACE HTTP method enabled' },
    // Debug endpoints
    { pattern: /(?:\/debug|\/trace|\/dump|\/phpinfo)/gi, issue: 'Debug endpoint detected' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, issue } of unnecessaryFeaturePatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a05-feature-${findings.length + 1}`,
          ruleId: 'owasp-a05-security-misconfiguration',
          severity: 'low',
          message: `Unnecessary feature: ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          suggestion: {
            description: 'Disable unnecessary features',
            example: `// Disable X-Powered-By:
app.disable('x-powered-by');
// Or use Helmet which does this automatically`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for missing security headers
 */
function checkMissingHeaders(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  
  // List of important security headers
  const securityHeaders = [
    'Content-Security-Policy',
    'X-Content-Type-Options',
    'X-Frame-Options',
    'Strict-Transport-Security',
    'X-XSS-Protection',
  ];
  
  // Check if helmet is used (sets all headers)
  if (sourceCode.includes('helmet')) return;
  
  // Check if it's a server file
  const isServerFile = /express|createServer|fastify|koa/i.test(sourceCode);
  
  if (isServerFile) {
    const missingHeaders = securityHeaders.filter(header => 
      !new RegExp(header, 'i').test(sourceCode)
    );
    
    if (missingHeaders.length > 0) {
      findings.push({
        id: `owasp-a05-header-${findings.length + 1}`,
        ruleId: 'owasp-a05-security-misconfiguration',
        severity: 'medium',
        message: `Missing security headers: ${missingHeaders.join(', ')}`,
        location: {
          file: context.filePath,
          startLine: 1,
          endLine: 1,
          startColumn: 0,
          endColumn: 0,
        },
        suggestion: {
          description: 'Use Helmet for comprehensive security headers',
          example: `// Use Helmet for comprehensive security headers:
const helmet = require('helmet');
app.use(helmet());
// Or set individual headers:
app.use((req, res, next) => {
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('X-Frame-Options', 'DENY');
  next();
});`,
        },
      });
    }
  }
}

/**
 * Check for development settings in production code
 */
function checkDevSettings(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const devSettingsPatterns = [
    // localhost in production
    { pattern: /['"`](?:https?:\/\/)?localhost(?::\d+)?(?:\/[^'"`]*)?['"`]/gi, issue: 'localhost URL' },
    { pattern: /['"`](?:https?:\/\/)?127\.0\.0\.1(?::\d+)?(?:\/[^'"`]*)?['"`]/gi, issue: '127.0.0.1 URL' },
    // Development databases
    { pattern: /mongodb:\/\/localhost/gi, issue: 'localhost MongoDB' },
    { pattern: /redis:\/\/localhost/gi, issue: 'localhost Redis' },
    // Debug flags
    { pattern: /(?:DEBUG|VERBOSE|DEV_MODE)\s*[:=]\s*(?:true|1|['"`]1['"`])/gi, issue: 'Debug flag enabled' },
    // TODO/FIXME for security
    { pattern: /(?:TODO|FIXME)[^*\n]*(?:security|auth|password|token)/gi, issue: 'Security TODO/FIXME' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, issue } of devSettingsPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        // Check if it's conditional
        const surroundingCode = lines.slice(Math.max(0, lineNum - 2), lineNum + 2).join('\n');
        
        if (!isConditionalDevCode(surroundingCode)) {
          findings.push({
            id: `owasp-a05-dev-${findings.length + 1}`,
            ruleId: 'owasp-a05-security-misconfiguration',
            severity: 'medium',
            message: `Development setting in code: ${issue}`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            suggestion: {
              description: 'Use environment variables',
              example: `// Use environment variables:
const dbUrl = process.env.DATABASE_URL || 'mongodb://localhost/dev';
// Or use conditional logic:
const apiUrl = process.env.NODE_ENV === 'production'
  ? 'https://api.production.com'
  : 'http://localhost:3000';`,
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check for exposed environment variables
 */
function checkExposedEnvironment(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const exposedEnvPatterns = [
    // Sending all environment variables
    { pattern: /res\.(?:send|json)\s*\([^)]*process\.env\s*\)/gi, issue: 'Full process.env in response' },
    // Logging all environment
    { pattern: /console\.log\s*\([^)]*process\.env\s*\)/gi, issue: 'Full process.env in console' },
    // Config dump
    { pattern: /JSON\.stringify\s*\([^)]*process\.env/gi, issue: 'process.env stringified' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, issue } of exposedEnvPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a05-env-${findings.length + 1}`,
          ruleId: 'owasp-a05-security-misconfiguration',
          severity: 'critical',
          message: `Exposed environment: ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          suggestion: {
            description: 'Never expose full environment',
            example: `// Never expose full environment:
// Instead, expose only safe values
const safeConfig = {
  nodeEnv: process.env.NODE_ENV,
  appVersion: process.env.APP_VERSION
};
res.json({ config: safeConfig });`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check if code has production environment check
 */
function hasProductionCheck(code: string): boolean {
  const prodCheckPatterns = [
    /process\.env\.NODE_ENV/i,
    /production/i,
    /development/i,
    /isProduction/i,
    /isProd/i,
  ];
  
  return prodCheckPatterns.some(p => p.test(code));
}

/**
 * Check if code is conditional development code
 */
function isConditionalDevCode(code: string): boolean {
  const conditionalPatterns = [
    /if\s*\([^)]*(?:NODE_ENV|development|production)/i,
    /process\.env\.\w+\s*\|\|/i,
    /\?\s*['"`]http/i,
  ];
  
  return conditionalPatterns.some(p => p.test(code));
}

export default owaspA05SecurityMisconfiguration;
