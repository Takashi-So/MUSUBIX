/**
 * Security Scanner (Lightweight / Embedded)
 *
 * Detects secrets, OWASP vulnerabilities, and sensitive data in code.
 * Provides redaction policies to prevent sensitive data leakage.
 *
 * NOTE: This is the lightweight, zero-dependency scanner embedded in @nahisaho/musubix-core
 * for use within the symbolic reasoning pipeline. It uses simple regex-based detection
 * suitable for quick inline scanning of code snippets during analysis.
 *
 * For full-featured, standalone security analysis (AST-based detection, taint analysis,
 * file system scanning, SHA-256 hashing, OWASP rule engine with ts-morph), use the
 * dedicated @nahisaho/musubix-security package instead:
 *   - Secret detection: packages/security/src/analysis/secret-detector.ts
 *   - Vulnerability scanning: packages/security/src/analysis/vulnerability-scanner.ts
 *   - OWASP rules: packages/security/src/rules/owasp/
 *   - Security analytics: packages/security/src/intelligence/security-analytics.ts
 *
 * The two implementations are intentionally separate to preserve core's zero-dependency
 * isolation (Article I: Library-First) while allowing the security package to leverage
 * heavier dependencies (tree-sitter, ts-morph) for deeper analysis.
 *
 * @packageDocumentation
 * @module symbolic/security
 *
 * @see REQ-NFR-005 - Security Requirements
 * @see DES-SYMB-001 §6.5 - SecuritySandbox + SecretScanner
 * @see TSK-SYMB-013
 */

import type { Explanation, Evidence } from './types.js';

// ============================================================
// Security Types
// ============================================================

/**
 * Secret type categories
 */
export type SecretType =
  | 'api_key'
  | 'password'
  | 'private_key'
  | 'token'
  | 'credential'
  | 'connection_string'
  | 'jwt'
  | 'oauth'
  | 'certificate'
  | 'ssh_key'
  | 'aws_key'
  | 'azure_key'
  | 'gcp_key'
  | 'generic_secret';

/**
 * OWASP vulnerability categories
 */
export type OwaspCategory =
  | 'A01_broken_access_control'
  | 'A02_cryptographic_failures'
  | 'A03_injection'
  | 'A04_insecure_design'
  | 'A05_security_misconfiguration'
  | 'A06_vulnerable_components'
  | 'A07_auth_failures'
  | 'A08_data_integrity'
  | 'A09_logging_failures'
  | 'A10_ssrf';

/**
 * Security finding severity
 */
export type SecuritySeverity = 'critical' | 'high' | 'medium' | 'low' | 'info';

/**
 * Detected secret
 */
export interface DetectedSecret {
  /** Secret type */
  type: SecretType;
  /** Severity level */
  severity: SecuritySeverity;
  /** Description of the finding */
  description: string;
  /** Pattern that matched */
  pattern: string;
  /** Line number where found */
  lineNumber?: number;
  /** Column range */
  columnRange?: { start: number; end: number };
  /** Redacted snippet showing context */
  redactedSnippet: string;
  /** Confidence (0-1) */
  confidence: number;
  /** Recommended action */
  recommendation: string;
}

/**
 * OWASP vulnerability finding
 */
export interface OwaspFinding {
  /** OWASP category */
  category: OwaspCategory;
  /** Severity level */
  severity: SecuritySeverity;
  /** Description of the vulnerability */
  description: string;
  /** Vulnerable code pattern */
  pattern: string;
  /** Line number where found */
  lineNumber?: number;
  /** CWE reference if applicable */
  cweId?: string;
  /** Redacted vulnerable snippet */
  redactedSnippet: string;
  /** Fix suggestion */
  fixSuggestion: string;
  /** Confidence (0-1) */
  confidence: number;
}

/**
 * Security scan result
 */
export interface SecurityScanResult {
  /** Detected secrets */
  secrets: DetectedSecret[];
  /** OWASP findings */
  owaspFindings: OwaspFinding[];
  /** Overall security score (0-100, higher is better) */
  securityScore: number;
  /** Summary statistics */
  summary: {
    totalFindings: number;
    criticalCount: number;
    highCount: number;
    mediumCount: number;
    lowCount: number;
    infoCount: number;
  };
  /** Scan timestamp */
  scannedAt: string;
  /** Explanation of findings */
  explanation: Explanation;
}

/**
 * Redaction policy
 */
export type RedactionPolicy = 'full' | 'partial' | 'hash' | 'mask' | 'remove';

/**
 * Redaction options
 */
export interface RedactionOptions {
  /** Default policy */
  defaultPolicy: RedactionPolicy;
  /** Per-type policies */
  typeOverrides?: Partial<Record<SecretType, RedactionPolicy>>;
  /** Mask character */
  maskChar?: string;
  /** Minimum mask length */
  minMaskLength?: number;
  /** Hash algorithm for hash policy */
  hashAlgorithm?: 'sha256' | 'sha512' | 'md5';
  /** Keep first N characters */
  keepPrefix?: number;
  /** Keep last N characters */
  keepSuffix?: number;
}

/**
 * Security scanner configuration
 */
export interface SecurityScannerConfig {
  /** Enable secret detection */
  enableSecretDetection: boolean;
  /** Enable OWASP detection */
  enableOwaspDetection: boolean;
  /** Minimum severity to report */
  minSeverity: SecuritySeverity;
  /** Minimum confidence threshold */
  minConfidence: number;
  /** Custom secret patterns */
  customSecretPatterns?: Array<{
    name: string;
    pattern: RegExp;
    type: SecretType;
    severity: SecuritySeverity;
  }>;
  /** Custom OWASP patterns */
  customOwaspPatterns?: Array<{
    name: string;
    pattern: RegExp;
    category: OwaspCategory;
    severity: SecuritySeverity;
    cweId?: string;
  }>;
  /** Redaction options */
  redaction: RedactionOptions;
}

/**
 * Default security scanner configuration
 */
export const DEFAULT_SECURITY_SCANNER_CONFIG: SecurityScannerConfig = {
  enableSecretDetection: true,
  enableOwaspDetection: true,
  minSeverity: 'low',
  minConfidence: 0.6,
  redaction: {
    defaultPolicy: 'mask',
    maskChar: '*',
    minMaskLength: 8,
    keepPrefix: 3,
    keepSuffix: 3,
  },
};

// ============================================================
// Secret Patterns
// ============================================================

/**
 * Secret detection patterns
 */
const SECRET_PATTERNS: Array<{
  name: string;
  pattern: RegExp;
  type: SecretType;
  severity: SecuritySeverity;
  confidence: number;
}> = [
  // API Keys
  {
    name: 'Generic API Key',
    pattern: /(?:api[_-]?key|apikey)\s*[=:]\s*['"]?([a-zA-Z0-9_\-]{20,})['"]?/gi,
    type: 'api_key',
    severity: 'high',
    confidence: 0.9,
  },
  {
    name: 'Bearer Token',
    pattern: /[Bb]earer\s+[a-zA-Z0-9_\-\.]+/g,
    type: 'token',
    severity: 'high',
    confidence: 0.85,
  },
  // AWS
  {
    name: 'AWS Access Key',
    pattern: /AKIA[0-9A-Z]{16}/g,
    type: 'aws_key',
    severity: 'critical',
    confidence: 0.95,
  },
  {
    name: 'AWS Secret Key',
    pattern: /(?:aws[_-]?secret|secret[_-]?key)\s*[=:]\s*['"]?([a-zA-Z0-9/+=]{40})['"]?/gi,
    type: 'aws_key',
    severity: 'critical',
    confidence: 0.9,
  },
  // Azure
  {
    name: 'Azure Connection String',
    pattern: /DefaultEndpointsProtocol=https;AccountName=[^;]+;AccountKey=[^;]+;EndpointSuffix=[^;]+/gi,
    type: 'azure_key',
    severity: 'critical',
    confidence: 0.95,
  },
  {
    name: 'Azure Storage Key',
    pattern: /(?:AccountKey|SharedAccessSignature)\s*[=:]\s*['"]?([a-zA-Z0-9+/=]{44,})['"]?/gi,
    type: 'azure_key',
    severity: 'critical',
    confidence: 0.9,
  },
  // GCP
  {
    name: 'GCP API Key',
    pattern: /AIza[0-9A-Za-z_-]{35}/g,
    type: 'gcp_key',
    severity: 'high',
    confidence: 0.9,
  },
  // Passwords
  {
    name: 'Password Assignment',
    pattern: /(?:password|passwd|pwd)\s*[=:]\s*['"]([^'"]{6,})['"]?/gi,
    type: 'password',
    severity: 'critical',
    confidence: 0.85,
  },
  // Private Keys
  {
    name: 'RSA Private Key',
    pattern: /-----BEGIN RSA PRIVATE KEY-----/g,
    type: 'private_key',
    severity: 'critical',
    confidence: 0.99,
  },
  {
    name: 'SSH Private Key',
    pattern: /-----BEGIN (?:OPENSSH|EC|DSA) PRIVATE KEY-----/g,
    type: 'ssh_key',
    severity: 'critical',
    confidence: 0.99,
  },
  // JWT
  {
    name: 'JWT Token',
    pattern: /eyJ[a-zA-Z0-9_-]+\.eyJ[a-zA-Z0-9_-]+\.[a-zA-Z0-9_-]+/g,
    type: 'jwt',
    severity: 'high',
    confidence: 0.95,
  },
  // OAuth
  {
    name: 'OAuth Client Secret',
    pattern: /(?:client[_-]?secret|oauth[_-]?secret)\s*[=:]\s*['"]?([a-zA-Z0-9_\-]{20,})['"]?/gi,
    type: 'oauth',
    severity: 'high',
    confidence: 0.85,
  },
  // Generic secrets
  {
    name: 'Generic Secret',
    pattern: /(?:secret|token|auth)\s*[=:]\s*['"]([^'"]{10,})['"]?/gi,
    type: 'generic_secret',
    severity: 'medium',
    confidence: 0.7,
  },
  // Connection strings
  {
    name: 'Database Connection String',
    pattern: /(?:postgres|mysql|mongodb|redis):\/\/[^:]+:[^@]+@[^\s]+/gi,
    type: 'connection_string',
    severity: 'critical',
    confidence: 0.9,
  },
];

// ============================================================
// OWASP Patterns
// ============================================================

/**
 * OWASP vulnerability detection patterns
 */
const OWASP_PATTERNS: Array<{
  name: string;
  pattern: RegExp;
  category: OwaspCategory;
  severity: SecuritySeverity;
  cweId: string;
  fixSuggestion: string;
  confidence: number;
}> = [
  // A03: Injection
  {
    name: 'SQL Injection Risk',
    pattern: /(?:query|execute|raw|sql)\s*\(\s*(?:`|'|").*\$\{|\+\s*[a-zA-Z_]+\s*\+/gi,
    category: 'A03_injection',
    severity: 'critical',
    cweId: 'CWE-89',
    fixSuggestion: 'Use parameterized queries or prepared statements instead of string concatenation',
    confidence: 0.8,
  },
  {
    name: 'Command Injection Risk',
    pattern: /(?:exec|spawn|system|shell_exec)\s*\([^)]*\$\{|\+\s*[a-zA-Z_]+/gi,
    category: 'A03_injection',
    severity: 'critical',
    cweId: 'CWE-78',
    fixSuggestion: 'Avoid executing shell commands with user input. Use allow-lists for acceptable values',
    confidence: 0.85,
  },
  {
    name: 'XSS Risk - innerHTML',
    pattern: /\.innerHTML\s*=\s*(?!['"`])/g,
    category: 'A03_injection',
    severity: 'high',
    cweId: 'CWE-79',
    fixSuggestion: 'Use textContent instead of innerHTML, or sanitize HTML before insertion',
    confidence: 0.8,
  },
  // A02: Cryptographic Failures
  {
    name: 'Weak Hashing Algorithm',
    pattern: /(?:md5|sha1)\s*\(/gi,
    category: 'A02_cryptographic_failures',
    severity: 'medium',
    cweId: 'CWE-328',
    fixSuggestion: 'Use strong hashing algorithms like SHA-256 or bcrypt for sensitive data',
    confidence: 0.9,
  },
  {
    name: 'Hardcoded IV',
    pattern: /(?:iv|initializationVector)\s*[=:]\s*['"][a-zA-Z0-9+/=]+['"]/gi,
    category: 'A02_cryptographic_failures',
    severity: 'high',
    cweId: 'CWE-329',
    fixSuggestion: 'Generate a random IV for each encryption operation',
    confidence: 0.85,
  },
  // A05: Security Misconfiguration
  {
    name: 'Debug Mode Enabled',
    pattern: /(?:debug|DEBUG)\s*[=:]\s*(?:true|1|['"]true['"])/gi,
    category: 'A05_security_misconfiguration',
    severity: 'medium',
    cweId: 'CWE-489',
    fixSuggestion: 'Disable debug mode in production environments',
    confidence: 0.8,
  },
  {
    name: 'CORS Allow All',
    pattern: /(?:Access-Control-Allow-Origin|cors)\s*[=:]\s*['"]\*['"]/gi,
    category: 'A05_security_misconfiguration',
    severity: 'medium',
    cweId: 'CWE-942',
    fixSuggestion: 'Restrict CORS to specific trusted origins',
    confidence: 0.9,
  },
  // A07: Authentication Failures
  {
    name: 'Plaintext Password Comparison',
    pattern: /password\s*===?\s*[a-zA-Z_]+|[a-zA-Z_]+\s*===?\s*password(?!Hash)/gi,
    category: 'A07_auth_failures',
    severity: 'critical',
    cweId: 'CWE-256',
    fixSuggestion: 'Use secure password comparison functions like bcrypt.compare()',
    confidence: 0.7,
  },
  // A08: Data Integrity Failures
  {
    name: 'Insecure Deserialization',
    pattern: /(?:eval|Function)\s*\([^)]*JSON\.parse/gi,
    category: 'A08_data_integrity',
    severity: 'high',
    cweId: 'CWE-502',
    fixSuggestion: 'Avoid using eval with parsed JSON. Validate and sanitize serialized data',
    confidence: 0.85,
  },
  // A09: Logging Failures
  {
    name: 'Logging Sensitive Data',
    pattern: /(?:console\.log|logger\.\w+)\s*\([^)]*(?:password|secret|token|key|credential)/gi,
    category: 'A09_logging_failures',
    severity: 'medium',
    cweId: 'CWE-532',
    fixSuggestion: 'Remove sensitive data from logs or redact before logging',
    confidence: 0.75,
  },
  // A10: SSRF
  {
    name: 'SSRF Risk',
    pattern: /fetch\s*\(\s*(?:[a-zA-Z_]+|`[^`]*\$\{)/gi,
    category: 'A10_ssrf',
    severity: 'high',
    cweId: 'CWE-918',
    fixSuggestion: 'Validate and sanitize URLs. Use allow-lists for allowed destinations',
    confidence: 0.7,
  },
];

// ============================================================
// Security Scanner Class
// ============================================================

/**
 * Security Scanner
 *
 * Scans code for secrets and OWASP vulnerabilities,
 * providing redaction capabilities for sensitive data.
 */
export class SecurityScanner {
  private readonly config: SecurityScannerConfig;
  private readonly secretPatterns: typeof SECRET_PATTERNS;
  private readonly owaspPatterns: Array<{
    name: string;
    pattern: RegExp;
    category: OwaspCategory;
    severity: SecuritySeverity;
    cweId?: string;
    fixSuggestion: string;
    confidence: number;
  }>;

  constructor(config: Partial<SecurityScannerConfig> = {}) {
    this.config = { ...DEFAULT_SECURITY_SCANNER_CONFIG, ...config };
    this.secretPatterns = [
      ...SECRET_PATTERNS,
      ...(config.customSecretPatterns?.map((p) => ({
        ...p,
        confidence: 0.8,
      })) ?? []),
    ];
    this.owaspPatterns = [
      ...OWASP_PATTERNS,
      ...(config.customOwaspPatterns?.map((p) => ({
        ...p,
        confidence: 0.8,
        fixSuggestion: p.cweId ? `Fix ${p.cweId} issue` : 'Review and fix this security issue',
      })) ?? []),
    ];
  }

  /**
   * Scan code for secrets and vulnerabilities
   */
  scan(code: string, filename?: string): SecurityScanResult {
    const secrets = this.config.enableSecretDetection ? this.scanSecrets(code) : [];
    const owaspFindings = this.config.enableOwaspDetection ? this.scanOwasp(code) : [];

    // Filter by minimum severity
    const filteredSecrets = this.filterBySeverity(secrets);
    const filteredOwasp = this.filterBySeverity(owaspFindings);

    // Calculate security score
    const securityScore = this.calculateSecurityScore(filteredSecrets, filteredOwasp);

    // Summary statistics
    const allFindings = [...filteredSecrets, ...filteredOwasp];
    const summary = {
      totalFindings: allFindings.length,
      criticalCount: allFindings.filter((f) => f.severity === 'critical').length,
      highCount: allFindings.filter((f) => f.severity === 'high').length,
      mediumCount: allFindings.filter((f) => f.severity === 'medium').length,
      lowCount: allFindings.filter((f) => f.severity === 'low').length,
      infoCount: allFindings.filter((f) => f.severity === 'info').length,
    };

    const evidence: Evidence[] = [];
    if (filename) {
      evidence.push({
        type: 'code',
        source: filename,
        content: `Scanned ${code.length} characters`,
      });
    }

    return {
      secrets: filteredSecrets,
      owaspFindings: filteredOwasp,
      securityScore,
      summary,
      scannedAt: new Date().toISOString(),
      explanation: {
        summary: `Security scan found ${summary.totalFindings} issue(s): ${summary.criticalCount} critical, ${summary.highCount} high`,
        reasoning: [
          `Scanned for ${this.secretPatterns.length} secret patterns`,
          `Scanned for ${this.owaspPatterns.length} OWASP vulnerability patterns`,
          summary.totalFindings === 0
            ? 'No security issues detected'
            : `Found ${summary.criticalCount} critical and ${summary.highCount} high severity issues`,
        ],
        evidence,
        relatedRequirements: ['REQ-NFR-005'],
      },
    };
  }

  /**
   * Scan for secrets
   */
  private scanSecrets(code: string): DetectedSecret[] {
    const secrets: DetectedSecret[] = [];
    const lines = code.split('\n');

    for (const patternDef of this.secretPatterns) {
      if (patternDef.confidence < this.config.minConfidence) {
        continue;
      }

      // Reset regex lastIndex
      patternDef.pattern.lastIndex = 0;

      let match;
      while ((match = patternDef.pattern.exec(code)) !== null) {
        const matchStart = match.index;
        const matchText = match[0];

        // Find line number
        let lineNumber = 1;
        let charCount = 0;
        for (let i = 0; i < lines.length; i++) {
          if (charCount + lines[i].length >= matchStart) {
            lineNumber = i + 1;
            break;
          }
          charCount += lines[i].length + 1; // +1 for newline
        }

        // Redact the match
        const redactedSnippet = this.redact(matchText, patternDef.type);

        secrets.push({
          type: patternDef.type,
          severity: patternDef.severity,
          description: `${patternDef.name} detected`,
          pattern: patternDef.name,
          lineNumber,
          columnRange: {
            start: matchStart - charCount + lines[lineNumber - 1].length - lines[lineNumber - 1].length,
            end: matchStart - charCount + matchText.length,
          },
          redactedSnippet,
          confidence: patternDef.confidence,
          recommendation: `Remove or externalize this ${patternDef.type}. Use environment variables or secret management services.`,
        });
      }
    }

    return secrets;
  }

  /**
   * Scan for OWASP vulnerabilities
   */
  private scanOwasp(code: string): OwaspFinding[] {
    const findings: OwaspFinding[] = [];
    const lines = code.split('\n');

    for (const patternDef of this.owaspPatterns) {
      if (patternDef.confidence < this.config.minConfidence) {
        continue;
      }

      // Reset regex lastIndex
      patternDef.pattern.lastIndex = 0;

      let match;
      while ((match = patternDef.pattern.exec(code)) !== null) {
        const matchStart = match.index;
        const matchText = match[0];

        // Find line number
        let lineNumber = 1;
        let charCount = 0;
        for (let i = 0; i < lines.length; i++) {
          if (charCount + lines[i].length >= matchStart) {
            lineNumber = i + 1;
            break;
          }
          charCount += lines[i].length + 1;
        }

        findings.push({
          category: patternDef.category,
          severity: patternDef.severity,
          description: `${patternDef.name}: Potential ${patternDef.category.replace(/_/g, ' ')}`,
          pattern: patternDef.name,
          lineNumber,
          cweId: patternDef.cweId,
          redactedSnippet: matchText.slice(0, 50) + (matchText.length > 50 ? '...' : ''),
          fixSuggestion: patternDef.fixSuggestion,
          confidence: patternDef.confidence,
        });
      }
    }

    return findings;
  }

  /**
   * Redact sensitive value
   */
  redact(value: string, type?: SecretType): string {
    const policy = type
      ? this.config.redaction.typeOverrides?.[type] ?? this.config.redaction.defaultPolicy
      : this.config.redaction.defaultPolicy;

    const { maskChar = '*', minMaskLength = 8, keepPrefix = 3, keepSuffix = 3 } = this.config.redaction;

    switch (policy) {
      case 'full':
        return maskChar.repeat(Math.max(minMaskLength, value.length));

      case 'partial': {
        if (value.length <= keepPrefix + keepSuffix) {
          return maskChar.repeat(value.length);
        }
        const prefix = value.slice(0, keepPrefix);
        const suffix = value.slice(-keepSuffix);
        const middleLength = Math.max(minMaskLength, value.length - keepPrefix - keepSuffix);
        return prefix + maskChar.repeat(middleLength) + suffix;
      }

      case 'hash': {
        // Simple hash representation (not cryptographic)
        const hash = this.simpleHash(value);
        return `[REDACTED:${hash.slice(0, 8)}]`;
      }

      case 'mask':
      default: {
        if (value.length <= keepPrefix + keepSuffix) {
          return maskChar.repeat(value.length);
        }
        const prefix = value.slice(0, keepPrefix);
        const suffix = value.slice(-keepSuffix);
        const middleLength = value.length - keepPrefix - keepSuffix;
        return prefix + maskChar.repeat(middleLength) + suffix;
      }

      case 'remove':
        return '[REMOVED]';
    }
  }

  /**
   * Redact all secrets from code
   */
  redactAll(code: string): { redactedCode: string; redactionCount: number } {
    let redactedCode = code;
    let redactionCount = 0;

    for (const patternDef of this.secretPatterns) {
      patternDef.pattern.lastIndex = 0;

      redactedCode = redactedCode.replace(patternDef.pattern, (match) => {
        redactionCount++;
        return this.redact(match, patternDef.type);
      });
    }

    return { redactedCode, redactionCount };
  }

  /**
   * Check if code is safe to log/store
   */
  isSafeToLog(code: string): { safe: boolean; reasons: string[] } {
    const scanResult = this.scan(code);

    if (scanResult.secrets.length === 0) {
      return { safe: true, reasons: [] };
    }

    return {
      safe: false,
      reasons: scanResult.secrets.map(
        (s) => `${s.type} detected at line ${s.lineNumber}: ${s.description}`,
      ),
    };
  }

  /**
   * Filter findings by minimum severity
   */
  private filterBySeverity<T extends { severity: SecuritySeverity }>(findings: T[]): T[] {
    const severityOrder: SecuritySeverity[] = ['critical', 'high', 'medium', 'low', 'info'];
    const minIndex = severityOrder.indexOf(this.config.minSeverity);

    return findings.filter((f) => severityOrder.indexOf(f.severity) <= minIndex);
  }

  /**
   * Calculate security score
   */
  private calculateSecurityScore(
    secrets: DetectedSecret[],
    owaspFindings: OwaspFinding[],
  ): number {
    let score = 100;

    // Deduct for secrets
    for (const secret of secrets) {
      switch (secret.severity) {
        case 'critical':
          score -= 25;
          break;
        case 'high':
          score -= 15;
          break;
        case 'medium':
          score -= 8;
          break;
        case 'low':
          score -= 3;
          break;
        case 'info':
          score -= 1;
          break;
      }
    }

    // Deduct for OWASP findings
    for (const finding of owaspFindings) {
      switch (finding.severity) {
        case 'critical':
          score -= 20;
          break;
        case 'high':
          score -= 12;
          break;
        case 'medium':
          score -= 6;
          break;
        case 'low':
          score -= 2;
          break;
        case 'info':
          score -= 1;
          break;
      }
    }

    return Math.max(0, Math.min(100, score));
  }

  /**
   * Simple hash for redaction (not cryptographic)
   */
  private simpleHash(value: string): string {
    let hash = 0;
    for (let i = 0; i < value.length; i++) {
      const char = value.charCodeAt(i);
      hash = (hash << 5) - hash + char;
      hash = hash & hash;
    }
    return Math.abs(hash).toString(16).padStart(8, '0');
  }
}

// ============================================================
// Security Sandbox
// ============================================================

/**
 * Security sandbox event type
 */
export type SecurityEventType =
  | 'secret_detected'
  | 'owasp_detected'
  | 'redaction_applied'
  | 'access_denied'
  | 'validation_failed'
  | 'audit_logged';

/**
 * Security event
 */
export interface SecurityEvent {
  /** Event type */
  type: SecurityEventType;
  /** Severity */
  severity: SecuritySeverity;
  /** Event description */
  description: string;
  /** Timestamp */
  timestamp: string;
  /** Additional metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Security audit log entry
 */
export interface SecurityAuditEntry {
  /** Entry ID */
  id: string;
  /** Timestamp */
  timestamp: string;
  /** Event type */
  eventType: SecurityEventType;
  /** Severity */
  severity: SecuritySeverity;
  /** Description */
  description: string;
  /** Actor (user/system) */
  actor?: string;
  /** Resource affected */
  resource?: string;
  /** Action taken */
  action?: string;
  /** Outcome */
  outcome: 'success' | 'failure' | 'blocked';
  /** Metadata */
  metadata?: Record<string, unknown>;
  /** Previous hash for chain */
  prevHash?: string;
  /** Current entry hash */
  hash: string;
}

/**
 * Security Sandbox
 *
 * Provides security boundary for code execution and analysis,
 * preventing sensitive data leakage and logging security events.
 */
export class SecuritySandbox {
  private readonly scanner: SecurityScanner;
  private readonly auditLog: SecurityAuditEntry[] = [];
  private lastHash: string = '';

  constructor(scannerConfig?: Partial<SecurityScannerConfig>) {
    this.scanner = new SecurityScanner(scannerConfig);
  }

  /**
   * Validate code before processing
   */
  validate(code: string, context?: string): {
    valid: boolean;
    sanitized: string;
    events: SecurityEvent[];
  } {
    const events: SecurityEvent[] = [];
    const scanResult = this.scanner.scan(code, context);

    // Generate events for findings
    for (const secret of scanResult.secrets) {
      events.push({
        type: 'secret_detected',
        severity: secret.severity,
        description: secret.description,
        timestamp: new Date().toISOString(),
        metadata: {
          secretType: secret.type,
          lineNumber: secret.lineNumber,
          confidence: secret.confidence,
        },
      });
    }

    for (const finding of scanResult.owaspFindings) {
      events.push({
        type: 'owasp_detected',
        severity: finding.severity,
        description: finding.description,
        timestamp: new Date().toISOString(),
        metadata: {
          category: finding.category,
          cweId: finding.cweId,
          lineNumber: finding.lineNumber,
        },
      });
    }

    // Determine validity based on critical findings
    const hasCritical = scanResult.summary.criticalCount > 0;

    // Sanitize if needed
    let sanitized = code;
    if (scanResult.secrets.length > 0) {
      const { redactedCode, redactionCount } = this.scanner.redactAll(code);
      sanitized = redactedCode;

      events.push({
        type: 'redaction_applied',
        severity: 'info',
        description: `Applied ${redactionCount} redaction(s)`,
        timestamp: new Date().toISOString(),
        metadata: { redactionCount },
      });
    }

    // Log audit event
    this.logAuditEvent(
      hasCritical ? 'validation_failed' : 'audit_logged',
      hasCritical ? 'high' : 'info',
      `Code validation ${hasCritical ? 'failed' : 'passed'}: ${scanResult.summary.totalFindings} findings`,
      hasCritical ? 'blocked' : 'success',
      {
        context,
        secretsFound: scanResult.secrets.length,
        owaspFound: scanResult.owaspFindings.length,
      },
    );

    return {
      valid: !hasCritical,
      sanitized,
      events,
    };
  }

  /**
   * Process code safely for learning/storage
   */
  processForStorage(code: string): {
    safeCode: string;
    redactionLog: string[];
  } {
    const redactionLog: string[] = [];
    const scanResult = this.scanner.scan(code);

    // Always redact secrets before storage
    const { redactedCode, redactionCount } = this.scanner.redactAll(code);

    if (redactionCount > 0) {
      redactionLog.push(`Redacted ${redactionCount} secrets before storage`);
    }

    for (const secret of scanResult.secrets) {
      redactionLog.push(`${secret.type}: ${secret.redactedSnippet}`);
    }

    this.logAuditEvent(
      'redaction_applied',
      'info',
      `Processed code for storage: ${redactionCount} redactions`,
      'success',
      { redactionCount },
    );

    return {
      safeCode: redactedCode,
      redactionLog,
    };
  }

  /**
   * Get audit log
   */
  getAuditLog(): SecurityAuditEntry[] {
    return [...this.auditLog];
  }

  /**
   * Verify audit log integrity
   */
  verifyAuditLogIntegrity(): { valid: boolean; brokenAt?: number } {
    if (this.auditLog.length === 0) {
      return { valid: true };
    }

    let prevHash = '';
    for (let i = 0; i < this.auditLog.length; i++) {
      const entry = this.auditLog[i];

      // Check chain
      if (entry.prevHash !== prevHash) {
        return { valid: false, brokenAt: i };
      }

      // Verify hash
      const expectedHash = this.computeEntryHash(entry);
      if (entry.hash !== expectedHash) {
        return { valid: false, brokenAt: i };
      }

      prevHash = entry.hash;
    }

    return { valid: true };
  }

  /**
   * Get scanner instance for direct access
   */
  getScanner(): SecurityScanner {
    return this.scanner;
  }

  /**
   * Log audit event
   */
  private logAuditEvent(
    eventType: SecurityEventType,
    severity: SecuritySeverity,
    description: string,
    outcome: 'success' | 'failure' | 'blocked',
    metadata?: Record<string, unknown>,
  ): void {
    const entry: SecurityAuditEntry = {
      id: `SEC-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`,
      timestamp: new Date().toISOString(),
      eventType,
      severity,
      description,
      outcome,
      metadata,
      prevHash: this.lastHash,
      hash: '',
    };

    entry.hash = this.computeEntryHash(entry);
    this.lastHash = entry.hash;
    this.auditLog.push(entry);
  }

  /**
   * Compute hash for audit entry
   */
  private computeEntryHash(entry: SecurityAuditEntry): string {
    const data = `${entry.id}|${entry.timestamp}|${entry.eventType}|${entry.severity}|${entry.description}|${entry.outcome}|${entry.prevHash}`;
    let hash = 0;
    for (let i = 0; i < data.length; i++) {
      const char = data.charCodeAt(i);
      hash = (hash << 5) - hash + char;
      hash = hash & hash;
    }
    return Math.abs(hash).toString(16).padStart(16, '0');
  }
}

// ============================================================
// Exports
// ============================================================

export {
  SECRET_PATTERNS,
  OWASP_PATTERNS,
};
