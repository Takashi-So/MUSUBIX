/**
 * @fileoverview OWASP A07:2021 - Identification and Authentication Failures
 * @module @nahisaho/musubix-security/rules/owasp/a07
 * @trace REQ-SEC-OWASP-007
 */

import type { SecurityRule, RuleContext, RuleFinding, RuleReference } from '../types.js';

/**
 * OWASP A07:2021 - Identification and Authentication Failures
 *
 * Detects:
 * - Weak password requirements
 * - Missing brute-force protection
 * - Insecure session management
 * - Credential exposure
 * - Missing MFA considerations
 */
export const owaspA07AuthFailures: SecurityRule = {
  id: 'owasp-a07-auth-failures',
  name: 'OWASP A07:2021 - Identification and Authentication Failures',
  description: 'Detects weak authentication patterns and credential management issues',
  defaultSeverity: 'critical',
  category: 'authentication',
  owasp: ['A07:2021'],
  cwe: ['287', '288', '307', '384', '521', '613', '620', '640', '798'],
  references: [
    {
      title: 'OWASP A07:2021',
      url: 'https://owasp.org/Top10/A07_2021-Identification_and_Authentication_Failures/',
    },
    {
      title: 'CWE-287: Improper Authentication',
      url: 'https://cwe.mitre.org/data/definitions/287.html',
    },
  ] as RuleReference[],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];

    checkWeakPasswordPolicy(context, findings);
    checkInsecureSession(context, findings);
    checkCredentialExposure(context, findings);
    checkMissingBruteForceProtection(context, findings);
    checkInsecureTokenHandling(context, findings);

    return findings;
  },
};

/**
 * Check for weak password policies
 */
function checkWeakPasswordPolicy(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const weakPolicies = [
    // Minimum length too short
    { pattern: /(?:minLength|min_length|minimum.*length)\s*[:=]\s*([1-7])\b/i, issue: 'Password minimum length too short (should be >= 8)' },
    // No complexity requirements
    { pattern: /password.*required\s*[:=]\s*(?:false|0)/i, issue: 'Password validation disabled' },
    // Only checking length
    { pattern: /password\.length\s*>=?\s*[1-5]\b/i, issue: 'Weak password length check' },
    // Plain text password comparison
    { pattern: /password\s*===?\s*(?:req\.body\.|params\.|user\.)/i, issue: 'Plain text password comparison' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, issue } of weakPolicies) {
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a07-password-${findings.length + 1}`,
          ruleId: 'owasp-a07-auth-failures',
          severity: 'high',
          message: `Weak password policy: ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['521'],
          suggestion: {
            description: 'Enforce strong password policy',
            example: `// Use strong password validation:
const passwordSchema = {
  minLength: 12,
  requireUppercase: true,
  requireLowercase: true,
  requireNumbers: true,
  requireSpecialChars: true
};`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for insecure session management
 */
function checkInsecureSession(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const sessionPatterns = [
    // Insecure cookie settings
    { pattern: /secure\s*:\s*false/i, issue: 'Insecure cookie (missing secure flag)' },
    { pattern: /httpOnly\s*:\s*false/i, issue: 'Cookie vulnerable to XSS (httpOnly disabled)' },
    { pattern: /sameSite\s*:\s*['"`]none['"`]/i, issue: 'SameSite=None without proper security' },
    // Long session expiry
    { pattern: /(?:maxAge|expires)\s*[:=]\s*(?:31536000000|365\s*\*\s*24)/i, issue: 'Excessively long session duration (1 year)' },
    // Session fixation risk
    { pattern: /req\.session\s*=\s*req\.(?:body|query|params)/i, issue: 'Potential session fixation vulnerability' },
    // No session regeneration after login
    { pattern: /(?:login|authenticate).*\{[^}]*(?!regenerate|destroy)/i, issue: 'Missing session regeneration after authentication' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, issue } of sessionPatterns) {
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a07-session-${findings.length + 1}`,
          ruleId: 'owasp-a07-auth-failures',
          severity: 'high',
          message: `Insecure session management: ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['384', '613'],
          suggestion: {
            description: 'Use secure session configuration',
            example: `// Secure session configuration:
app.use(session({
  secret: process.env.SESSION_SECRET,
  cookie: {
    secure: true,
    httpOnly: true,
    sameSite: 'strict',
    maxAge: 3600000 // 1 hour
  },
  resave: false,
  saveUninitialized: false
}));`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for credential exposure
 */
function checkCredentialExposure(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const exposurePatterns = [
    // Password in logs
    { pattern: /console\.(?:log|info|debug|warn|error)\s*\([^)]*(?:password|secret|token|key)/i, issue: 'Credential logged to console' },
    { pattern: /logger\.(?:log|info|debug|warn|error)\s*\([^)]*(?:password|secret|token|key)/i, issue: 'Credential logged' },
    // Password in URL
    { pattern: /(?:href|url|redirect)\s*[:=].*[?&]password=/i, issue: 'Password in URL parameter' },
    // Password in error message
    { pattern: /(?:throw|Error)\s*\([^)]*password/i, issue: 'Password in error message' },
    // Credential in response
    { pattern: /res\.(?:json|send)\s*\([^)]*password/i, issue: 'Password in response body' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, issue } of exposurePatterns) {
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a07-exposure-${findings.length + 1}`,
          ruleId: 'owasp-a07-auth-failures',
          severity: 'critical',
          message: `Credential exposure risk: ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['312', '319', '532'],
          suggestion: {
            description: 'Never expose credentials in logs, URLs, or responses',
            example: `// Redact sensitive data:
const safeUser = { ...user, password: '[REDACTED]' };
console.log('User:', safeUser);`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for missing brute-force protection
 */
function checkMissingBruteForceProtection(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;

  // Check if this looks like a login handler
  const hasLoginEndpoint = /(?:post|handle)\s*\(\s*['"`]\/(?:api\/)?(?:login|signin|authenticate)['"`]/i.test(sourceCode);
  const hasRateLimiting = /(?:rateLimit|express-rate-limit|rate-limiter|limiter)/i.test(sourceCode);
  const hasAccountLockout = /(?:lockout|attempt.*count|failed.*attempts|max.*attempts)/i.test(sourceCode);

  if (hasLoginEndpoint && !hasRateLimiting && !hasAccountLockout) {
    const lines = sourceCode.split('\n');
    let loginLine = 0;

    for (let i = 0; i < lines.length; i++) {
      if (/(?:post|handle)\s*\(\s*['"`]\/(?:api\/)?(?:login|signin|authenticate)['"`]/i.test(lines[i])) {
        loginLine = i;
        break;
      }
    }

    findings.push({
      id: `owasp-a07-bruteforce-${findings.length + 1}`,
      ruleId: 'owasp-a07-auth-failures',
      severity: 'high',
      message: 'Login endpoint without brute-force protection',
      location: {
        file: context.filePath,
        startLine: loginLine + 1,
        endLine: loginLine + 1,
        startColumn: 0,
        endColumn: lines[loginLine]?.length || 0,
      },
      cwe: ['307'],
      suggestion: {
        description: 'Add rate limiting and account lockout',
        example: `// Use express-rate-limit:
const loginLimiter = rateLimit({
  windowMs: 15 * 60 * 1000, // 15 minutes
  max: 5, // 5 attempts
  skipSuccessfulRequests: true
});

app.post('/login', loginLimiter, async (req, res) => {
  // Also implement account lockout after N failed attempts
});`,
      },
    });
  }
}

/**
 * Check for insecure token handling
 */
function checkInsecureTokenHandling(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const tokenPatterns = [
    // JWT without verification
    { pattern: /jwt\.decode\s*\(/i, issue: 'JWT decoded without signature verification' },
    // JWT with 'none' algorithm
    { pattern: /algorithm\s*[:=]\s*['"`]none['"`]/i, issue: 'JWT with "none" algorithm' },
    // Token in localStorage
    { pattern: /localStorage\.setItem\s*\([^)]*(?:token|jwt|auth)/i, issue: 'Sensitive token stored in localStorage (XSS risk)' },
    // Token in query string
    { pattern: /[?&]token=/i, issue: 'Token passed in URL query string' },
    // Long-lived tokens
    { pattern: /expiresIn\s*[:=]\s*['"`](?:30d|365d|1y)['"`]/i, issue: 'Excessively long token expiration' },
    // Missing token expiration
    { pattern: /jwt\.sign\s*\([^)]*(?!expiresIn)/i, issue: 'JWT without expiration' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, issue } of tokenPatterns) {
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a07-token-${findings.length + 1}`,
          ruleId: 'owasp-a07-auth-failures',
          severity: 'high',
          message: `Insecure token handling: ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['287', '311'],
          suggestion: {
            description: 'Use secure token practices',
            example: `// Secure JWT handling:
const token = jwt.sign(payload, secret, {
  algorithm: 'RS256',
  expiresIn: '15m' // Short-lived access token
});

// Always verify tokens:
const decoded = jwt.verify(token, publicKey);

// Store tokens in httpOnly cookies, not localStorage`,
          },
        });
        break;
      }
    }
  }
}

export default owaspA07AuthFailures;
