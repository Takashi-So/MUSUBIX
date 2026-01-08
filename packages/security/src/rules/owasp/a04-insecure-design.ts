/**
 * @fileoverview OWASP A04:2021 - Insecure Design Rule
 * @module @nahisaho/musubix-security/rules/owasp/a04-insecure-design
 * @trace TSK-RULE-003
 * 
 * Detects:
 * - Missing rate limiting
 * - Missing input validation
 * - Missing output encoding
 * - Insecure defaults
 * - Business logic flaws
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

/**
 * OWASP A04 - Insecure Design
 */
export const owaspA04InsecureDesign: SecurityRule = {
  id: 'owasp-a04-insecure-design',
  name: 'OWASP A04:2021 - Insecure Design',
  description: 'Detects design-level security flaws such as missing rate limiting, validation, and encoding',
  defaultSeverity: 'high',
  detectionMethod: 'pattern-match',
  tags: ['owasp', 'design', 'rate-limiting', 'validation', 'security'],
  owasp: ['A04:2021'],
  cwe: ['73', '183', '209', '256', '501', '522', '602', '656', '799', '840'],
  references: [
    { title: 'OWASP A04:2021 - Insecure Design', url: 'https://owasp.org/Top10/A04_2021-Insecure_Design/' },
    { title: 'CWE-501: Trust Boundary Violation', url: 'https://cwe.mitre.org/data/definitions/501.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const sourceFile = context.sourceFile;
    if (!sourceFile) return findings;

    // Check for missing rate limiting
    checkMissingRateLimiting(context, findings);
    
    // Check for missing input validation
    checkMissingInputValidation(context, findings);
    
    // Check for missing output encoding
    checkMissingOutputEncoding(context, findings);
    
    // Check for insecure defaults
    checkInsecureDefaults(context, findings);
    
    // Check for missing security headers
    checkMissingSecurityHeaders(context, findings);
    
    // Check for business logic issues
    checkBusinessLogicFlaws(context, findings);

    return findings;
  },
};

/**
 * Check for missing rate limiting on sensitive endpoints
 */
function checkMissingRateLimiting(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  
  // Check if rate limiting is imported/used
  const hasRateLimiting = /rateLimit|express-rate-limit|rate-limiter|throttle/i.test(sourceCode);
  
  // Sensitive endpoints that should have rate limiting
  const sensitiveEndpointPatterns = [
    /\.(post|put)\s*\(\s*['"`]\/(?:api\/)?(?:login|signin|auth)/gi,
    /\.(post|put)\s*\(\s*['"`]\/(?:api\/)?(?:register|signup)/gi,
    /\.(post|put)\s*\(\s*['"`]\/(?:api\/)?(?:reset-password|forgot-password)/gi,
    /\.(post|put)\s*\(\s*['"`]\/(?:api\/)?(?:otp|verify|code)/gi,
  ];
  
  if (!hasRateLimiting) {
    const lines = sourceCode.split('\n');
    
    for (let lineNum = 0; lineNum < lines.length; lineNum++) {
      const line = lines[lineNum];
      
      for (const pattern of sensitiveEndpointPatterns) {
        pattern.lastIndex = 0;
        if (pattern.test(line)) {
          findings.push({
            id: `owasp-a04-rate-${findings.length + 1}`,
            ruleId: 'owasp-a04-insecure-design',
            severity: 'high',
            message: 'Sensitive endpoint without rate limiting - vulnerable to brute force attacks',
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            suggestion: {
              description: 'Add rate limiting to sensitive endpoints',
              example: `// Add rate limiting middleware:
const rateLimit = require('express-rate-limit');
const authLimiter = rateLimit({
  windowMs: 15 * 60 * 1000,
  max: 5,
  message: 'Too many attempts, please try again later'
});
app.post('/login', authLimiter, loginHandler);`,
            },
          });
          break;
        }
      }
    }
  }
}

/**
 * Check for missing input validation
 */
function checkMissingInputValidation(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  // Check for direct use of req.body/query/params without validation
  const directUsePatterns = [
    // Direct assignment from request
    { pattern: /(?:const|let|var)\s+\w+\s*=\s*req\.body\s*;/gi, type: 'body' },
    { pattern: /(?:const|let|var)\s+\w+\s*=\s*req\.query\s*;/gi, type: 'query' },
    { pattern: /(?:const|let|var)\s+\w+\s*=\s*req\.params\s*;/gi, type: 'params' },
    // Destructuring without validation
    { pattern: /(?:const|let|var)\s+\{[^}]+\}\s*=\s*req\.body\s*;?\s*(?!.*validate)/gi, type: 'body destructuring' },
  ];
  
  // Check if validation library is present
  const hasValidation = /(?:joi|yup|zod|express-validator|class-validator|ajv)/i.test(sourceCode);
  
  if (!hasValidation) {
    for (let lineNum = 0; lineNum < lines.length; lineNum++) {
      const line = lines[lineNum];
      
      for (const { pattern, type } of directUsePatterns) {
        pattern.lastIndex = 0;
        if (pattern.test(line)) {
          // Check surrounding context for validation
          const surroundingCode = lines.slice(lineNum, Math.min(lines.length, lineNum + 10)).join('\n');
          
          if (!hasInputValidation(surroundingCode)) {
            findings.push({
              id: `owasp-a04-validation-${findings.length + 1}`,
              ruleId: 'owasp-a04-insecure-design',
              severity: 'medium',
              message: `Request ${type} used without input validation`,
              location: {
                file: context.filePath,
                startLine: lineNum + 1,
                endLine: lineNum + 1,
                startColumn: 0,
                endColumn: line.length,
              },
              suggestion: {
                description: 'Use a validation library',
                example: `// Use a validation library:
const { z } = require('zod');
const schema = z.object({
  email: z.string().email(),
  password: z.string().min(8)
});
const validated = schema.parse(req.body);`,
              },
            });
          }
          break;
        }
      }
    }
  }
}

/**
 * Check for missing output encoding
 */
function checkMissingOutputEncoding(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const outputPatterns = [
    // res.send with user data
    { pattern: /res\.send\s*\([^)]*(?:req\.body|req\.query|req\.params|user\.|data\.)/gi, type: 'res.send' },
    // Setting HTML directly
    { pattern: /\.html\s*\([^)]*(?:req\.|user\.|data\.)/gi, type: 'HTML response' },
    // Template rendering without sanitization
    { pattern: /res\.render\s*\([^)]*(?:req\.|user\.|data\.)/gi, type: 'template render' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, type } of outputPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        // Check if there's encoding/sanitization
        if (!hasOutputEncoding(line)) {
          findings.push({
            id: `owasp-a04-encoding-${findings.length + 1}`,
            ruleId: 'owasp-a04-insecure-design',
            severity: 'medium',
            message: `${type} with user data may need output encoding`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            suggestion: {
              description: 'Encode HTML entities in output',
              example: `// Encode HTML entities:
const encode = require('he');
res.send(encode.encode(userInput));
// Or use a template engine with auto-escaping`,
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check for insecure defaults
 */
function checkInsecureDefaults(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const insecureDefaultPatterns = [
    // Debug mode enabled
    { pattern: /debug\s*[:=]\s*true/gi, issue: 'Debug mode enabled', severity: 'medium' as const },
    // Trust proxy without validation
    { pattern: /trust\s*proxy\s*[:=]\s*true/gi, issue: 'Trust proxy enabled globally', severity: 'low' as const },
    // Session without secure flag
    { pattern: /session\s*\(\s*\{[^}]*(?!secure\s*:\s*true)/gi, issue: 'Session without secure flag', severity: 'medium' as const },
    // Cookie without httpOnly
    { pattern: /cookie\s*[:=]\s*\{[^}]*(?!httpOnly)/gi, issue: 'Cookie without httpOnly flag', severity: 'medium' as const },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, issue, severity } of insecureDefaultPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a04-default-${findings.length + 1}`,
          ruleId: 'owasp-a04-insecure-design',
          severity,
          message: `Insecure default: ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          suggestion: {
            description: 'Use secure defaults',
            example: `// Use secure defaults:
app.use(session({
  secret: process.env.SESSION_SECRET,
  cookie: {
    secure: true,
    httpOnly: true,
    sameSite: 'strict'
  }
}));`,
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
function checkMissingSecurityHeaders(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  
  // Check if helmet or manual security headers are set
  const hasSecurityHeaders = /helmet|X-Content-Type-Options|X-Frame-Options|Content-Security-Policy|Strict-Transport-Security/i.test(sourceCode);
  
  // Check if it's an Express app
  const isExpressApp = /express\(\)|createServer|app\.use|app\.get|app\.post/i.test(sourceCode);
  
  if (isExpressApp && !hasSecurityHeaders) {
    findings.push({
      id: `owasp-a04-headers-${findings.length + 1}`,
      ruleId: 'owasp-a04-insecure-design',
      severity: 'medium',
      message: 'Express app without security headers (consider using Helmet)',
      location: {
        file: context.filePath,
        startLine: 1,
        endLine: 1,
        startColumn: 0,
        endColumn: 0,
      },
      suggestion: {
        description: 'Add security headers with Helmet',
        example: `// Add Helmet:
const helmet = require('helmet');
app.use(helmet());`,
      },
    });
  }
  
  // Check for CSRF protection
  const hasCsrfProtection = /csrf|csurf|csrfToken/i.test(sourceCode);
  const hasFormPost = /\.(post|put|patch)\s*\(/gi.test(sourceCode);
  
  if (isExpressApp && hasFormPost && !hasCsrfProtection) {
    findings.push({
      id: `owasp-a04-csrf-${findings.length + 1}`,
      ruleId: 'owasp-a04-insecure-design',
      severity: 'medium',
      message: 'POST/PUT endpoints without CSRF protection',
      location: {
        file: context.filePath,
        startLine: 1,
        endLine: 1,
        startColumn: 0,
        endColumn: 0,
      },
      suggestion: {
        description: 'Add CSRF protection',
        example: `// Add CSRF protection:
const csrf = require('csurf');
app.use(csrf({ cookie: true }));`,
      },
    });
  }
}

/**
 * Check for business logic flaws
 */
function checkBusinessLogicFlaws(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const businessLogicPatterns = [
    // Price/amount from client without validation
    { pattern: /(?:price|amount|total|cost)\s*[:=]\s*(?:req\.body|req\.query)/gi, issue: 'Price/amount from client input', severity: 'high' as const },
    // Discount without limit check
    { pattern: /discount\s*[:=]\s*(?:req\.body|req\.query)[^;]*(?!.*(?:max|limit|check))/gi, issue: 'Discount without validation', severity: 'medium' as const },
    // Quantity without bounds
    { pattern: /quantity\s*[:=]\s*(?:req\.body|req\.query)[^;]*(?!.*(?:max|min|limit))/gi, issue: 'Quantity without bounds checking', severity: 'medium' as const },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, issue, severity } of businessLogicPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        // Check surrounding code for validation
        const surroundingCode = lines.slice(lineNum, Math.min(lines.length, lineNum + 5)).join('\n');
        
        if (!hasBusinessValidation(surroundingCode)) {
          findings.push({
            id: `owasp-a04-logic-${findings.length + 1}`,
            ruleId: 'owasp-a04-insecure-design',
            severity,
            message: `Potential business logic flaw: ${issue}`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            suggestion: {
              description: 'Add bounds checking and validation',
              example: `// Add bounds checking:
const quantity = Math.min(Math.max(parseInt(req.body.quantity) || 0, 1), 100);
// Always calculate prices server-side
const price = await getProductPrice(productId);`,
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check if code has input validation
 */
function hasInputValidation(code: string): boolean {
  const validationPatterns = [
    /validate/i,
    /schema/i,
    /parse/i,
    /sanitize/i,
    /check/i,
    /assert/i,
    /joi\./i,
    /yup\./i,
    /zod\./i,
  ];
  
  return validationPatterns.some(p => p.test(code));
}

/**
 * Check if output has encoding
 */
function hasOutputEncoding(code: string): boolean {
  const encodingPatterns = [
    /encode/i,
    /escape/i,
    /sanitize/i,
    /\.json\s*\(/i,
    /DOMPurify/i,
  ];
  
  return encodingPatterns.some(p => p.test(code));
}

/**
 * Check if code has business validation
 */
function hasBusinessValidation(code: string): boolean {
  const validationPatterns = [
    /Math\.(?:min|max)/i,
    /Number\.(?:isFinite|isInteger)/i,
    />=?\s*\d/,
    /<=?\s*\d/,
    /validate/i,
    /check/i,
    /throw/i,
  ];
  
  return validationPatterns.some(p => p.test(code));
}

export default owaspA04InsecureDesign;
