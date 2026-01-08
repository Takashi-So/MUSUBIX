/**
 * @fileoverview OWASP A02:2021 - Cryptographic Failures Rule
 * @module @nahisaho/musubix-security/rules/owasp/a02-cryptographic-failures
 * @trace TSK-RULE-003
 * 
 * Detects:
 * - Weak hash algorithms (MD5, SHA1)
 * - Weak encryption algorithms (DES, RC4, ECB mode)
 * - Hardcoded cryptographic keys
 * - Insecure random number generation
 * - Missing TLS/SSL or weak configuration
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

/**
 * OWASP A02 - Cryptographic Failures
 */
export const owaspA02CryptographicFailures: SecurityRule = {
  id: 'owasp-a02-cryptographic-failures',
  name: 'OWASP A02:2021 - Cryptographic Failures',
  description: 'Detects weak cryptographic implementations, insecure algorithms, and improper key management',
  defaultSeverity: 'critical',
  detectionMethod: 'pattern-match',
  tags: ['owasp', 'cryptography', 'encryption', 'hashing', 'security'],
  owasp: ['A02:2021'],
  cwe: ['261', '310', '326', '327', '328', '330', '338', '759', '760'],
  references: [
    { title: 'OWASP A02:2021 - Cryptographic Failures', url: 'https://owasp.org/Top10/A02_2021-Cryptographic_Failures/' },
    { title: 'CWE-310: Cryptographic Issues', url: 'https://cwe.mitre.org/data/definitions/310.html' },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const sourceFile = context.sourceFile;
    if (!sourceFile) return findings;

    // Check for weak hash algorithms
    checkWeakHashAlgorithms(context, findings);
    
    // Check for weak encryption algorithms
    checkWeakEncryption(context, findings);
    
    // Check for hardcoded keys
    checkHardcodedKeys(context, findings);
    
    // Check for insecure random
    checkInsecureRandom(context, findings);
    
    // Check for insecure TLS configuration
    checkInsecureTLS(context, findings);
    
    // Check for sensitive data exposure
    checkSensitiveDataExposure(context, findings);

    return findings;
  },
};

/**
 * Check for weak hash algorithms
 */
function checkWeakHashAlgorithms(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const weakHashPatterns = [
    { pattern: /createHash\s*\(\s*['"`]md5['"`]\s*\)/gi, algo: 'MD5', severity: 'high' as const },
    { pattern: /createHash\s*\(\s*['"`]sha1['"`]\s*\)/gi, algo: 'SHA1', severity: 'medium' as const },
    { pattern: /md5\s*\(/gi, algo: 'MD5', severity: 'high' as const },
    { pattern: /sha1\s*\(/gi, algo: 'SHA1', severity: 'medium' as const },
    { pattern: /['"`]MD5['"`]/gi, algo: 'MD5', severity: 'high' as const },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, algo, severity } of weakHashPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a02-hash-${findings.length + 1}`,
          ruleId: 'owasp-a02-cryptographic-failures',
          severity,
          message: `Weak hash algorithm ${algo} detected - vulnerable to collision attacks`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          suggestion: {
            description: 'Use a strong hash algorithm',
            example: `// For passwords: use bcrypt, scrypt, or Argon2
// For integrity: use SHA-256 or SHA-3
const hash = crypto.createHash('sha256').update(data).digest('hex');`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for weak encryption algorithms
 */
function checkWeakEncryption(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const weakCryptoPatterns = [
    { pattern: /['"`]des['"`]/gi, algo: 'DES', severity: 'critical' as const },
    { pattern: /['"`]3des['"`]/gi, algo: '3DES', severity: 'high' as const },
    { pattern: /['"`]rc4['"`]/gi, algo: 'RC4', severity: 'critical' as const },
    { pattern: /['"`]aes-\d+-ecb['"`]/gi, algo: 'AES-ECB', severity: 'high' as const },
    { pattern: /['"`]blowfish['"`]/gi, algo: 'Blowfish', severity: 'medium' as const },
    { pattern: /createCipher\s*\(/gi, algo: 'deprecated createCipher', severity: 'high' as const },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, algo, severity } of weakCryptoPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a02-crypto-${findings.length + 1}`,
          ruleId: 'owasp-a02-cryptographic-failures',
          severity,
          message: `Weak or deprecated encryption algorithm ${algo} detected`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          suggestion: {
            description: 'Use strong encryption algorithms',
            example: `// Use AES-256-GCM for authenticated encryption
const cipher = crypto.createCipheriv('aes-256-gcm', key, iv);`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for hardcoded cryptographic keys
 */
function checkHardcodedKeys(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const keyPatterns = [
    // Hardcoded key assignments
    { pattern: /(?:const|let|var)\s+(?:secret|key|password|apiKey|api_key|privateKey|private_key)\s*=\s*['"`][^'"`]+['"`]/gi, type: 'hardcoded key' },
    // Key in crypto operations
    { pattern: /(?:createCipheriv|createDecipheriv|createHmac)\s*\([^,]+,\s*['"`][^'"`]+['"`]/gi, type: 'hardcoded crypto key' },
    // JWT secret
    { pattern: /jwt\.sign\s*\([^,]+,\s*['"`][^'"`]+['"`]/gi, type: 'hardcoded JWT secret' },
    // Base64 encoded key (typical pattern)
    { pattern: /['"`][A-Za-z0-9+/=]{32,}['"`]/g, type: 'potential base64 key' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    // Skip comments and string-heavy lines that are likely not keys
    if (line.trim().startsWith('//') || line.trim().startsWith('*')) continue;
    
    for (const { pattern, type } of keyPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a02-key-${findings.length + 1}`,
          ruleId: 'owasp-a02-cryptographic-failures',
          severity: 'critical',
          message: `Potential ${type} detected - never hardcode cryptographic keys`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          suggestion: {
            description: 'Use environment variables or a secrets manager',
            example: `// Use environment variables:
const secret = process.env.JWT_SECRET;
// Or use a secrets manager like AWS Secrets Manager, HashiCorp Vault`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for insecure random number generation
 */
function checkInsecureRandom(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const insecureRandomPatterns = [
    { pattern: /Math\.random\s*\(\s*\)/gi, type: 'Math.random()' },
    { pattern: /Date\.now\s*\(\s*\)/gi, type: 'Date.now() as seed' },
    { pattern: /new\s+Date\s*\(\s*\)\.getTime\s*\(\s*\)/gi, type: 'timestamp as seed' },
  ];
  
  // Check if used in security context
  const securityContextPatterns = [
    /token/i,
    /secret/i,
    /password/i,
    /key/i,
    /salt/i,
    /nonce/i,
    /iv/i,
    /session/i,
    /auth/i,
    /csrf/i,
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, type } of insecureRandomPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        // Check if it's in a security context
        const surroundingCode = lines.slice(Math.max(0, lineNum - 3), lineNum + 3).join('\n');
        
        if (securityContextPatterns.some(p => p.test(surroundingCode))) {
          findings.push({
            id: `owasp-a02-random-${findings.length + 1}`,
            ruleId: 'owasp-a02-cryptographic-failures',
            severity: 'high',
            message: `Insecure random generator ${type} used in security context`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            suggestion: {
              description: 'Use cryptographically secure random',
              example: `// Use crypto.randomBytes() or crypto.randomUUID()
const token = crypto.randomBytes(32).toString('hex');
const uuid = crypto.randomUUID();`,
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check for insecure TLS/SSL configuration
 */
function checkInsecureTLS(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const insecureTLSPatterns = [
    { pattern: /rejectUnauthorized\s*:\s*false/gi, issue: 'TLS certificate validation disabled' },
    { pattern: /secureProtocol\s*:\s*['"`]SSLv3['"`]/gi, issue: 'SSLv3 protocol (vulnerable)' },
    { pattern: /secureProtocol\s*:\s*['"`]TLSv1_method['"`]/gi, issue: 'TLS 1.0 protocol (deprecated)' },
    { pattern: /minVersion\s*:\s*['"`]TLSv1['"`]/gi, issue: 'TLS 1.0 minimum (deprecated)' },
    { pattern: /NODE_TLS_REJECT_UNAUTHORIZED\s*=\s*['"`]0['"`]/gi, issue: 'Global TLS rejection disabled' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, issue } of insecureTLSPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a02-tls-${findings.length + 1}`,
          ruleId: 'owasp-a02-cryptographic-failures',
          severity: 'critical',
          message: `Insecure TLS configuration: ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          suggestion: {
            description: 'Use secure TLS configuration',
            example: `// Use TLS 1.2+ with certificate validation
const options = {
  minVersion: 'TLSv1.2',
  rejectUnauthorized: true
};`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for sensitive data exposure
 */
function checkSensitiveDataExposure(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');
  
  const sensitiveDataPatterns = [
    // Logging sensitive data
    { pattern: /console\.log\s*\([^)]*(?:password|secret|token|key|credential)/gi, issue: 'Logging sensitive data' },
    // Storing password in plain text
    { pattern: /password\s*[:=]\s*(?:req\.body|req\.query)\.password(?!\s*&&|\s*\?)/gi, issue: 'Password not hashed before storage' },
    // Sensitive data in URL
    { pattern: /['"`][^'"`]*\?[^'"`]*(?:password|token|key)=/gi, issue: 'Sensitive data in URL query string' },
  ];
  
  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];
    
    for (const { pattern, issue } of sensitiveDataPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a02-exposure-${findings.length + 1}`,
          ruleId: 'owasp-a02-cryptographic-failures',
          severity: 'high',
          message: `Potential sensitive data exposure: ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          suggestion: {
            description: 'Protect sensitive data',
            example: `// Encrypt sensitive data:
const encrypted = await encrypt(sensitiveData);
// Never log passwords or tokens
// Use POST body instead of URL for sensitive data`,
          },
        });
        break;
      }
    }
  }
}

export default owaspA02CryptographicFailures;
