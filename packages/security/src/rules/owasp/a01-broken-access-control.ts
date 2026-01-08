/**
 * @fileoverview OWASP A01:2021 - Broken Access Control Rule
 * @module @nahisaho/musubix-security/rules/owasp/a01-broken-access-control
 * @trace TSK-RULE-003
 * 
 * Detects:
 * - Missing authorization checks
 * - Direct object references without validation
 * - Path traversal vulnerabilities
 * - CORS misconfigurations
 * - Privilege escalation patterns
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

/**
 * OWASP A01 - Broken Access Control
 */
export const owaspA01BrokenAccessControl: SecurityRule = {
  id: 'owasp-a01-broken-access-control',
  name: 'OWASP A01:2021 - Broken Access Control',
  description: 'Detects missing or improper access control implementations that could allow unauthorized access to resources',
  defaultSeverity: 'critical',
  detectionMethod: 'combined',
  tags: ['owasp', 'access-control', 'authorization', 'security'],
  owasp: ['A01:2021'],
  cwe: ['284', '285', '639', '862', '863'],
  references: [
    { title: 'OWASP A01:2021 - Broken Access Control', url: 'https://owasp.org/Top10/A01_2021-Broken_Access_Control/' },
    { title: 'CWE-284: Improper Access Control', url: 'https://cwe.mitre.org/data/definitions/284.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const sourceFile = context.sourceFile;
    if (!sourceFile) return findings;

    // Check for route handlers without auth middleware
    checkMissingAuthMiddleware(context, findings);
    
    // Check for direct object references
    checkDirectObjectReferences(context, findings);
    
    // Check for CORS misconfigurations
    checkCorsMisconfigurations(context, findings);
    
    // Check for path traversal patterns
    checkPathTraversal(context, findings);
    
    // Check for admin/privileged operations without checks
    checkPrivilegedOperations(context, findings);

    return findings;
  },
};

/**
 * Check for route handlers that lack authentication middleware
 */
function checkMissingAuthMiddleware(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  
  // Pattern: Express-style routes without auth middleware
  const routePatterns = [
    /app\.(get|post|put|delete|patch)\s*\(\s*(['"`][^'"`]*['"`])\s*,\s*(?!.*auth)/gi,
    /router\.(get|post|put|delete|patch)\s*\(\s*(['"`][^'"`]*['"`])\s*,\s*(?!.*auth)/gi,
  ];
  
  // Sensitive endpoint patterns
  const sensitiveEndpoints = [
    /\/admin/i,
    /\/api\/users/i,
    /\/api\/settings/i,
    /\/api\/config/i,
    /\/api\/private/i,
    /\/delete/i,
    /\/edit/i,
    /\/update/i,
  ];
  
  for (const pattern of routePatterns) {
    let match;
    while ((match = pattern.exec(sourceCode)) !== null) {
      const endpoint = match[2];
      
      // Check if it's a sensitive endpoint
      if (sensitiveEndpoints.some(p => p.test(endpoint))) {
        const lines = sourceCode.substring(0, match.index).split('\n');
        const line = lines.length;
        
        findings.push({
          id: `owasp-a01-${findings.length + 1}`,
          ruleId: 'owasp-a01-broken-access-control',
          severity: 'high',
          message: `Sensitive endpoint ${endpoint} may lack authentication middleware`,
          location: {
            file: context.filePath,
            startLine: line,
            endLine: line,
            startColumn: 0,
            endColumn: match[0].length,
          },
          suggestion: {
            description: 'Add authentication middleware before the route handler',
            example: `// Add auth middleware: app.${match[1]}(${endpoint}, authMiddleware, handler)`,
          },
        });
      }
    }
  }
}

/**
 * Check for insecure direct object references (IDOR)
 */
function checkDirectObjectReferences(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  // Patterns indicating IDOR vulnerabilities
  const idorPatterns = [
    // Direct use of user-provided ID without ownership check
    /(?:req\.params|req\.query|req\.body)\s*\.\s*(?:id|userId|user_id)/gi,
    // Direct database queries with user input
    /findById\s*\(\s*(?:req\.params|req\.query|req\.body)/gi,
    /where\s*:\s*\{\s*id\s*:\s*(?:req\.params|req\.query)/gi,
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const pattern of idorPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        // Check if there's no ownership/authorization check nearby
        const surroundingCode = lines.slice(Math.max(0, lineNum - 5), lineNum + 5).join('\n');
        
        if (!hasAuthorizationCheck(surroundingCode)) {
          findings.push({
            id: `owasp-a01-idor-${findings.length + 1}`,
            ruleId: 'owasp-a01-broken-access-control',
            severity: 'high',
            message: 'Potential Insecure Direct Object Reference (IDOR) - user-provided ID used without ownership verification',
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            suggestion: {
              description: 'Verify resource ownership before allowing access',
              example: '// Add ownership check: if (resource.userId !== req.user.id) return res.status(403).json({ error: "Forbidden" })',
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check for CORS misconfigurations
 */
function checkCorsMisconfigurations(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const corsPatterns = [
    // Wildcard origin
    { pattern: /['"`]\*['"`]/g, message: 'CORS allows all origins (*)' },
    // Reflecting origin without validation
    { pattern: /origin\s*:\s*(?:req\.headers\.origin|true)/gi, message: 'CORS reflects any origin' },
    // credentials with wildcard
    { pattern: /credentials\s*:\s*true.*origin\s*:\s*['"`]\*['"`]/gi, message: 'CORS allows credentials with wildcard origin' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, message } of corsPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a01-cors-${findings.length + 1}`,
          ruleId: 'owasp-a01-broken-access-control',
          severity: 'medium',
          message: `CORS misconfiguration: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          suggestion: {
            description: 'Restrict CORS to specific trusted origins',
            example: "// Use specific origins: origin: ['https://trusted-domain.com']",
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for path traversal vulnerabilities
 */
function checkPathTraversal(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  // Patterns for potential path traversal
  const pathPatterns = [
    /path\.join\s*\([^)]*(?:req\.params|req\.query|req\.body)/gi,
    /fs\.(?:readFile|readdir|writeFile|unlink|stat)\s*\([^)]*(?:req\.params|req\.query)/gi,
    /res\.sendFile\s*\([^)]*(?:req\.params|req\.query)/gi,
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const pattern of pathPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        // Check if there's path normalization
        if (!line.includes('normalize') && !line.includes('realpath') && !line.includes('sanitize')) {
          findings.push({
            id: `owasp-a01-path-${findings.length + 1}`,
            ruleId: 'owasp-a01-broken-access-control',
            severity: 'high',
            message: 'Potential path traversal vulnerability - user input used in file path without sanitization',
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            suggestion: {
              description: 'Sanitize and validate file paths to prevent directory traversal',
              example: `// Use path.normalize() and verify path doesn't escape base directory
const safePath = path.normalize(userInput).replace(/^(\\.\\.\\/)+/, '');
if (!safePath.startsWith(baseDir)) throw new Error('Invalid path');`,
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check for privileged operations without authorization checks
 */
function checkPrivilegedOperations(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  // Privileged operation patterns
  const privilegedPatterns = [
    { pattern: /\.destroy\s*\(/gi, operation: 'delete' },
    { pattern: /\.delete\s*\(/gi, operation: 'delete' },
    { pattern: /\.remove\s*\(/gi, operation: 'delete' },
    { pattern: /role\s*[:=]\s*['"`]admin['"`]/gi, operation: 'role assignment' },
    { pattern: /isAdmin\s*[:=]\s*true/gi, operation: 'admin flag' },
    { pattern: /\.executeRaw\s*\(/gi, operation: 'raw SQL execution' },
    { pattern: /eval\s*\(/gi, operation: 'code evaluation' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, operation } of privilegedPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        // Check surrounding context for authorization
        const surroundingCode = lines.slice(Math.max(0, lineNum - 10), lineNum + 1).join('\n');
        
        if (!hasAuthorizationCheck(surroundingCode)) {
          findings.push({
            id: `owasp-a01-priv-${findings.length + 1}`,
            ruleId: 'owasp-a01-broken-access-control',
            severity: 'high',
            message: `Privileged operation (${operation}) without visible authorization check`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            suggestion: {
              description: 'Add authorization check before privileged operations',
              example: '// Add: if (!user.hasPermission("admin")) throw new ForbiddenError();',
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check if code contains authorization checks
 */
function hasAuthorizationCheck(code: string): boolean {
  const authPatterns = [
    /isAuth/i,
    /isAdmin/i,
    /authorize/i,
    /hasPermission/i,
    /hasRole/i,
    /checkAuth/i,
    /requireAuth/i,
    /guard/i,
    /canAccess/i,
    /userId\s*===\s*req\.user/i,
    /req\.user\.id\s*===\s*/i,
    /\.where\s*\([^)]*userId/i,
  ];
  
  return authPatterns.some(p => p.test(code));
}

export default owaspA01BrokenAccessControl;
