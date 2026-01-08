/**
 * @fileoverview OWASP A09:2021 - Security Logging and Monitoring Failures
 * @module @nahisaho/musubix-security/rules/owasp/a09
 * @trace REQ-SEC-OWASP-009
 */

import type { SecurityRule, RuleContext, RuleFinding, RuleReference } from '../types.js';

/**
 * OWASP A09:2021 - Security Logging and Monitoring Failures
 *
 * Detects:
 * - Missing security event logging
 * - Sensitive data in logs
 * - Insufficient log detail
 * - Missing log integrity protection
 */
export const owaspA09LoggingFailures: SecurityRule = {
  id: 'owasp-a09-logging-failures',
  name: 'OWASP A09:2021 - Security Logging and Monitoring Failures',
  description: 'Detects insufficient logging and monitoring for security events',
  defaultSeverity: 'medium',
  category: 'logging',
  owasp: ['A09:2021'],
  cwe: ['117', '223', '532', '778'],
  references: [
    {
      title: 'OWASP A09:2021',
      url: 'https://owasp.org/Top10/A09_2021-Security_Logging_and_Monitoring_Failures/',
    },
    {
      title: 'CWE-778: Insufficient Logging',
      url: 'https://cwe.mitre.org/data/definitions/778.html',
    },
  ] as RuleReference[],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];

    checkMissingSecurityLogging(context, findings);
    checkSensitiveDataInLogs(context, findings);
    checkLogInjection(context, findings);
    checkInsufficientLogContext(context, findings);
    checkMissingErrorLogging(context, findings);

    return findings;
  },
};

/**
 * Check for missing security event logging
 */
function checkMissingSecurityLogging(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  // Security events that should be logged
  const securityEvents = [
    { pattern: /(?:login|signin|authenticate)\s*(?:async\s*)?\(/i, event: 'authentication', needsLog: true },
    { pattern: /(?:logout|signout)\s*(?:async\s*)?\(/i, event: 'logout', needsLog: true },
    { pattern: /(?:password|credential).*(?:change|update|reset)/i, event: 'credential change', needsLog: true },
    { pattern: /(?:permission|role|access).*(?:grant|revoke|change)/i, event: 'authorization change', needsLog: true },
    { pattern: /(?:admin|administrative).*(?:action|operation)/i, event: 'admin action', needsLog: true },
    { pattern: /(?:delete|remove).*(?:user|account)/i, event: 'account deletion', needsLog: true },
  ];

  // Function to check if logging exists nearby
  const hasLoggingNearby = (startLine: number): boolean => {
    const searchRange = 15; // lines to search
    const surroundingCode = lines.slice(
      Math.max(0, startLine - 2),
      Math.min(lines.length, startLine + searchRange)
    ).join('\n');

    return /(?:logger|log|audit|winston|pino|bunyan)\.(?:info|warn|error|log|audit)/i.test(surroundingCode);
  };

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, event, needsLog } of securityEvents) {
      if (pattern.test(line) && needsLog) {
        if (!hasLoggingNearby(lineNum)) {
          findings.push({
            id: `owasp-a09-missing-${findings.length + 1}`,
            ruleId: 'owasp-a09-logging-failures',
            severity: 'medium',
            message: `Missing security logging for ${event} event`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            cwe: ['778'],
            suggestion: {
              description: `Add audit logging for ${event} events`,
              example: `// Add security audit logging:
logger.info('security.${event.replace(/\s+/g, '_')}', {
  userId: user.id,
  action: '${event}',
  timestamp: new Date().toISOString(),
  ipAddress: req.ip,
  userAgent: req.headers['user-agent']
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
 * Check for sensitive data in logs
 */
function checkSensitiveDataInLogs(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const sensitiveLogPatterns = [
    // Password in log
    { pattern: /(?:console|logger|log|winston|pino)\.(?:log|info|debug|warn|error)\s*\([^)]*password/i, data: 'password' },
    // Token in log
    { pattern: /(?:console|logger|log)\.(?:log|info|debug|warn|error)\s*\([^)]*(?:token|jwt|bearer)/i, data: 'authentication token' },
    // Credit card
    { pattern: /(?:console|logger|log)\.(?:log|info|debug|warn|error)\s*\([^)]*(?:credit.*card|card.*number|cvv)/i, data: 'credit card information' },
    // SSN
    { pattern: /(?:console|logger|log)\.(?:log|info|debug|warn|error)\s*\([^)]*(?:ssn|social.*security)/i, data: 'SSN' },
    // API key
    { pattern: /(?:console|logger|log)\.(?:log|info|debug|warn|error)\s*\([^)]*(?:api.*key|secret.*key|private.*key)/i, data: 'API key' },
    // Full request body (might contain sensitive data)
    { pattern: /(?:console|logger|log)\.(?:log|info|debug)\s*\([^)]*req\.body\s*\)/i, data: 'full request body' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, data } of sensitiveLogPatterns) {
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a09-sensitive-${findings.length + 1}`,
          ruleId: 'owasp-a09-logging-failures',
          severity: 'high',
          message: `Sensitive data in logs: ${data}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['532'],
          suggestion: {
            description: 'Redact sensitive data before logging',
            example: `// Redact sensitive data:
const redact = (obj) => {
  const sensitive = ['password', 'token', 'ssn', 'creditCard'];
  const redacted = { ...obj };
  for (const key of sensitive) {
    if (redacted[key]) redacted[key] = '[REDACTED]';
  }
  return redacted;
};

logger.info('Request:', redact(req.body));`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for log injection vulnerabilities
 */
function checkLogInjection(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const logInjectionPatterns = [
    // Direct user input in log message
    { pattern: /(?:console|logger|log)\.(?:log|info|debug|warn|error)\s*\(\s*req\.(?:body|query|params)\./i, issue: 'User input directly in log message' },
    // Template literal with user input
    { pattern: /(?:console|logger|log)\.(?:log|info|debug|warn|error)\s*\(\s*`[^`]*\$\{req\./i, issue: 'User input in log template literal' },
    // String concatenation with user input
    { pattern: /(?:console|logger|log)\.(?:log|info|debug|warn|error)\s*\([^)]*\+\s*req\./i, issue: 'User input concatenated in log' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, issue } of logInjectionPatterns) {
      if (pattern.test(line)) {
        // Check if input is sanitized
        const surroundingCode = lines.slice(Math.max(0, lineNum - 3), lineNum + 1).join('\n');
        const hasSanitization = /(?:sanitize|escape|encode|clean|filter)/i.test(surroundingCode);

        if (!hasSanitization) {
          findings.push({
            id: `owasp-a09-injection-${findings.length + 1}`,
            ruleId: 'owasp-a09-logging-failures',
            severity: 'medium',
            message: `Log injection vulnerability: ${issue}`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            cwe: ['117'],
            suggestion: {
              description: 'Sanitize user input before logging',
              example: `// Sanitize user input for logging:
const sanitizeForLog = (input) => {
  if (typeof input !== 'string') return String(input);
  return input
    .replace(/\\n/g, '\\\\n')
    .replace(/\\r/g, '\\\\r')
    .substring(0, 1000); // Limit length
};

logger.info('User action', { input: sanitizeForLog(req.body.input) });`,
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check for insufficient log context
 */
function checkInsufficientLogContext(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  // Look for security-related functions without proper context logging
  const securityFunctions = [
    /async function.*(?:auth|login|verify)/i,
    /const\s+\w+\s*=\s*async\s*\([^)]*\)\s*=>\s*\{.*(?:auth|login|verify)/i,
  ];

  let inSecurityFunction = false;
  let functionStartLine = 0;
  let braceCount = 0;

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    // Track function boundaries
    for (const pattern of securityFunctions) {
      if (pattern.test(line)) {
        inSecurityFunction = true;
        functionStartLine = lineNum;
        braceCount = 0;
        break;
      }
    }

    if (inSecurityFunction) {
      braceCount += (line.match(/\{/g) || []).length;
      braceCount -= (line.match(/\}/g) || []).length;

      if (braceCount <= 0 && lineNum > functionStartLine) {
        // End of function - check for proper logging
        const functionCode = lines.slice(functionStartLine, lineNum + 1).join('\n');

        const hasContextLogging = /logger\.(?:info|warn|error)\s*\([^)]*(?:userId|user\.id|ipAddress|req\.ip)/i.test(functionCode);

        if (!hasContextLogging) {
          findings.push({
            id: `owasp-a09-context-${findings.length + 1}`,
            ruleId: 'owasp-a09-logging-failures',
            severity: 'low',
            message: 'Security function lacks contextual logging (userId, IP, etc.)',
            location: {
              file: context.filePath,
              startLine: functionStartLine + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            cwe: ['223'],
            suggestion: {
              description: 'Add contextual information to security logs',
              example: `// Include relevant context in security logs:
logger.info('Authentication attempt', {
  userId: user?.id,
  email: user?.email,
  ipAddress: req.ip,
  userAgent: req.headers['user-agent'],
  timestamp: new Date().toISOString(),
  success: true
});`,
            },
          });
        }

        inSecurityFunction = false;
      }
    }
  }
}

/**
 * Check for missing error logging
 */
function checkMissingErrorLogging(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  // Check catch blocks without logging
  let inCatchBlock = false;
  let catchStartLine = 0;
  let catchBraceCount = 0;

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    if (/catch\s*\(/i.test(line)) {
      inCatchBlock = true;
      catchStartLine = lineNum;
      catchBraceCount = 0;
    }

    if (inCatchBlock) {
      catchBraceCount += (line.match(/\{/g) || []).length;
      catchBraceCount -= (line.match(/\}/g) || []).length;

      if (catchBraceCount <= 0 && lineNum > catchStartLine) {
        const catchCode = lines.slice(catchStartLine, lineNum + 1).join('\n');

        // Check if error is logged
        const hasErrorLogging = /(?:console|logger|log)\.(?:error|warn)\s*\(/i.test(catchCode);
        const isEmptyCatch = catchCode.replace(/[{}]/g, '').trim().length < 20;
        const hasRethrow = /throw\s+/i.test(catchCode);

        if (!hasErrorLogging && !isEmptyCatch && !hasRethrow) {
          findings.push({
            id: `owasp-a09-error-${findings.length + 1}`,
            ruleId: 'owasp-a09-logging-failures',
            severity: 'low',
            message: 'Error caught without logging',
            location: {
              file: context.filePath,
              startLine: catchStartLine + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            cwe: ['223'],
            suggestion: {
              description: 'Log errors for debugging and monitoring',
              example: `// Log errors with context:
try {
  // ... operation
} catch (error) {
  logger.error('Operation failed', {
    error: error.message,
    stack: error.stack,
    context: { /* relevant data */ }
  });
  throw error; // or handle appropriately
}`,
            },
          });
        }

        inCatchBlock = false;
      }
    }
  }
}

export default owaspA09LoggingFailures;
