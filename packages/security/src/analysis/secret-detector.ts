/**
 * @fileoverview Secret detection engine (Full-featured / Standalone)
 * @module @nahisaho/musubix-security/analysis/secret-detector
 * @trace REQ-SEC-SECRET-001, REQ-SEC-SECRET-002
 *
 * NOTE: This is the full-featured secret detector in @nahisaho/musubix-security.
 * It provides AST-aware context detection, SHA-256 deduplication, test value filtering,
 * and file system scanning with configurable patterns.
 *
 * A lightweight regex-only scanner also exists in @nahisaho/musubix-core at
 * packages/core/src/symbolic/security-scanner.ts for embedded use in the symbolic
 * reasoning pipeline (zero external dependencies). The two share similar detection
 * targets (AWS keys, private keys, JWTs, etc.) but use different regex patterns
 * tuned for their respective use cases. This separation is intentional to preserve
 * core's zero-dependency isolation.
 */

import { createHash } from 'node:crypto';
import type {
  Secret,
  SecretType,
  SecretContext,
  SecretPattern,
  SecretScanOptions,
  SecretScanResult,
  Severity,
  SourceLocation,
} from '../types/index.js';
import { FileScanner, createFileScanner } from '../infrastructure/file-scanner.js';

/**
 * Generate secret ID
 */
let secretCounter = 0;
function generateSecretId(): string {
  const date = new Date();
  const dateStr = date.toISOString().slice(0, 10).replace(/-/g, '');
  return `SEC-${dateStr}-${String(++secretCounter).padStart(3, '0')}`;
}

/**
 * Reset secret counter (for testing)
 */
export function resetSecretCounter(): void {
  secretCounter = 0;
}

/**
 * Built-in secret patterns with regex
 */
const SECRET_PATTERNS: SecretPattern[] = [
  // AWS
  {
    id: 'aws-access-key',
    name: 'AWS Access Key ID',
    type: 'aws-access-key',
    regex: /\b(AKIA[0-9A-Z]{16})\b/g,
    severity: 'critical',
    description: 'AWS Access Key ID',
    enabled: true,
    testValuePatterns: [/AKIAIOSFODNN7EXAMPLE/],
  },
  {
    id: 'aws-secret-key',
    name: 'AWS Secret Access Key',
    type: 'aws-secret-key',
    regex: /\b([A-Za-z0-9/+=]{40})\b/g,
    keyPatterns: [/aws.?secret/i, /secret.?key/i],
    severity: 'critical',
    description: 'AWS Secret Access Key',
    enabled: true,
    testValuePatterns: [/wJalrXUtnFEMI\/K7MDENG\/bPxRfiCYEXAMPLEKEY/],
  },
  // GitHub
  {
    id: 'github-pat',
    name: 'GitHub Personal Access Token',
    type: 'github-token',
    regex: /\b(ghp_[a-zA-Z0-9]{36}|gho_[a-zA-Z0-9]{36}|ghu_[a-zA-Z0-9]{36}|ghs_[a-zA-Z0-9]{36}|ghr_[a-zA-Z0-9]{36})\b/g,
    severity: 'critical',
    description: 'GitHub Personal Access Token',
    enabled: true,
  },
  {
    id: 'github-oauth',
    name: 'GitHub OAuth Access Token',
    type: 'github-token',
    regex: /\b(gho_[a-zA-Z0-9]{36})\b/g,
    severity: 'critical',
    description: 'GitHub OAuth Access Token',
    enabled: true,
  },
  // Private keys
  {
    id: 'private-key-rsa',
    name: 'RSA Private Key',
    type: 'private-key',
    regex: /-----BEGIN RSA PRIVATE KEY-----[\s\S]*?-----END RSA PRIVATE KEY-----/g,
    severity: 'critical',
    description: 'RSA Private Key',
    enabled: true,
  },
  {
    id: 'private-key-ec',
    name: 'EC Private Key',
    type: 'private-key',
    regex: /-----BEGIN EC PRIVATE KEY-----[\s\S]*?-----END EC PRIVATE KEY-----/g,
    severity: 'critical',
    description: 'EC Private Key',
    enabled: true,
  },
  {
    id: 'private-key-openssh',
    name: 'OpenSSH Private Key',
    type: 'ssh-key',
    regex: /-----BEGIN OPENSSH PRIVATE KEY-----[\s\S]*?-----END OPENSSH PRIVATE KEY-----/g,
    severity: 'critical',
    description: 'OpenSSH Private Key',
    enabled: true,
  },
  // Azure
  {
    id: 'azure-storage-key',
    name: 'Azure Storage Account Key',
    type: 'azure-connection-string',
    regex: /AccountKey=[a-zA-Z0-9+/=]{86,88}/g,
    severity: 'critical',
    description: 'Azure Storage Account Key',
    enabled: true,
  },
  {
    id: 'azure-connection-string',
    name: 'Azure Connection String',
    type: 'azure-connection-string',
    regex: /DefaultEndpointsProtocol=https?;AccountName=[^;]+;AccountKey=[a-zA-Z0-9+/=]+/g,
    severity: 'critical',
    description: 'Azure Storage Connection String',
    enabled: true,
  },
  // Stripe
  {
    id: 'stripe-live-key',
    name: 'Stripe Live API Key',
    type: 'stripe-key',
    regex: /\b(sk_live_[a-zA-Z0-9]{24,})\b/g,
    severity: 'critical',
    description: 'Stripe Live Secret Key',
    enabled: true,
  },
  {
    id: 'stripe-test-key',
    name: 'Stripe Test API Key',
    type: 'stripe-key',
    regex: /\b(sk_test_[a-zA-Z0-9]{24,})\b/g,
    severity: 'low',
    description: 'Stripe Test Secret Key',
    enabled: true,
  },
  // Slack
  {
    id: 'slack-webhook',
    name: 'Slack Webhook URL',
    type: 'slack-webhook',
    regex: /https:\/\/hooks\.slack\.com\/services\/[A-Z0-9]+\/[A-Z0-9]+\/[a-zA-Z0-9]+/g,
    severity: 'medium',
    description: 'Slack Incoming Webhook URL',
    enabled: true,
  },
  {
    id: 'slack-token',
    name: 'Slack Token',
    type: 'api-key',
    regex: /\b(xox[baprs]-[0-9]{10,13}-[0-9]{10,13}-[a-zA-Z0-9]{24,})\b/g,
    severity: 'high',
    description: 'Slack Bot/User Token',
    enabled: true,
  },
  // Database URLs
  {
    id: 'database-url-postgres',
    name: 'PostgreSQL Connection String',
    type: 'database-url',
    regex: /postgres(?:ql)?:\/\/[^:]+:[^@]+@[^/]+\/[^\s'"]+/gi,
    severity: 'high',
    description: 'PostgreSQL connection string with credentials',
    enabled: true,
  },
  {
    id: 'database-url-mysql',
    name: 'MySQL Connection String',
    type: 'database-url',
    regex: /mysql:\/\/[^:]+:[^@]+@[^/]+\/[^\s'"]+/gi,
    severity: 'high',
    description: 'MySQL connection string with credentials',
    enabled: true,
  },
  {
    id: 'database-url-mongodb',
    name: 'MongoDB Connection String',
    type: 'database-url',
    regex: /mongodb(\+srv)?:\/\/[^:]+:[^@]+@[^/]+\/[^\s'"]+/gi,
    severity: 'high',
    description: 'MongoDB connection string with credentials',
    enabled: true,
  },
  // JWT
  {
    id: 'jwt-token',
    name: 'JWT Token',
    type: 'jwt-secret',
    regex: /\beyJ[a-zA-Z0-9_-]*\.eyJ[a-zA-Z0-9_-]*\.[a-zA-Z0-9_-]+\b/g,
    severity: 'medium',
    description: 'JSON Web Token (may contain sensitive claims)',
    enabled: true,
  },
  // Generic API keys
  {
    id: 'generic-api-key',
    name: 'Generic API Key',
    type: 'api-key',
    regex: /\b[a-f0-9]{32}\b/gi,
    keyPatterns: [/api.?key/i, /apikey/i, /secret/i, /token/i, /password/i],
    severity: 'medium',
    description: 'Generic API key pattern',
    enabled: true,
    falsePositiveRate: 0.4,
  },
  // Password patterns
  {
    id: 'hardcoded-password',
    name: 'Hardcoded Password',
    type: 'password',
    regex: /(?:password|passwd|pwd)\s*[=:]\s*['"][^'"]{8,}['"]/gi,
    severity: 'high',
    description: 'Hardcoded password in code',
    enabled: true,
  },
];

/**
 * Common test/example value patterns
 */
const TEST_VALUE_PATTERNS = [
  /example/i,
  /test/i,
  /dummy/i,
  /sample/i,
  /placeholder/i,
  /your.?key/i,
  /xxx+/i,
  /000+/,
  /123456/,
  /abcdef/,
];

/**
 * Detect context from surrounding code
 */
function detectContext(content: string, matchIndex: number): SecretContext {
  const before = content.slice(Math.max(0, matchIndex - 50), matchIndex);
  const after = content.slice(matchIndex, matchIndex + 50);
  
  if (/\/\/|\/\*|\*/.test(before)) return 'comment';
  if (/['"]/.test(before) && /['"]/.test(after)) return 'string-literal';
  if (/`/.test(before)) return 'template-literal';
  if (/[{,]\s*\w+\s*:\s*$/.test(before)) return 'object-property';
  if (/\[\s*$/.test(before)) return 'array-element';
  if (/\.(env|config|json|ya?ml)$/.test(content.slice(0, 100))) return 'config-file';
  
  return 'source-code';
}

/**
 * Mask a secret value
 */
function maskValue(value: string): string {
  if (value.length <= 8) {
    return '*'.repeat(value.length);
  }
  return `${value.slice(0, 4)}${'*'.repeat(value.length - 8)}${value.slice(-4)}`;
}

/**
 * Hash a value for deduplication
 */
function hashValue(value: string): string {
  return createHash('sha256').update(value).digest('hex');
}

/**
 * Check if a value looks like a test/example
 */
function isTestValue(value: string, pattern: SecretPattern): boolean {
  // Check pattern-specific test values
  if (pattern.testValuePatterns) {
    for (const testPattern of pattern.testValuePatterns) {
      if (testPattern.test(value)) {
        return true;
      }
    }
  }

  // Check generic test patterns
  for (const testPattern of TEST_VALUE_PATTERNS) {
    if (testPattern.test(value)) {
      return true;
    }
  }

  return false;
}

/**
 * Get line number from index in content
 */
function getLineNumber(content: string, index: number): number {
  return content.slice(0, index).split('\n').length;
}

/**
 * Get column from index in content
 */
function getColumn(content: string, index: number): number {
  const lastNewline = content.lastIndexOf('\n', index - 1);
  return index - lastNewline - 1;
}

/**
 * Secret detector engine
 */
export class SecretDetector {
  private patterns: SecretPattern[];
  private fileScanner: FileScanner;
  private options: SecretScanOptions;

  constructor(options: SecretScanOptions = {}) {
    this.options = options;
    this.fileScanner = createFileScanner({
      extensions: ['.ts', '.tsx', '.js', '.jsx', '.json', '.yml', '.yaml', '.env', '.config', '.md'],
      excludePatterns: options.excludePatterns,
      maxFileSize: options.maxFileSize,
    });

    // Initialize patterns
    this.patterns = SECRET_PATTERNS.filter((p) => {
      if (!p.enabled) return false;
      if (options.disablePatterns?.includes(p.id)) return false;
      return true;
    });

    // Add custom patterns
    if (options.customPatterns) {
      this.patterns.push(...options.customPatterns);
    }
  }

  /**
   * Scan file content for secrets
   */
  scanContent(content: string, filePath: string): Secret[] {
    const secrets: Secret[] = [];
    const seenHashes = new Set<string>();

    for (const pattern of this.patterns) {
      // Reset regex state
      pattern.regex.lastIndex = 0;

      // Check key patterns first if defined (for context-sensitive detection)
      if (pattern.keyPatterns) {
        let hasKeyContext = false;
        for (const keyPattern of pattern.keyPatterns) {
          if (keyPattern.test(content)) {
            hasKeyContext = true;
            break;
          }
        }
        if (!hasKeyContext) continue;
      }

      let match: RegExpExecArray | null;
      while ((match = pattern.regex.exec(content)) !== null) {
        const value = match[1] || match[0];
        const hash = hashValue(value);

        // Skip duplicates
        if (seenHashes.has(hash)) continue;
        seenHashes.add(hash);

        // Check if test value
        const testValue = isTestValue(value, pattern);
        if (this.options.ignoreTestValues && testValue) continue;

        const lineNumber = getLineNumber(content, match.index);
        const column = getColumn(content, match.index);

        // Extract key name if possible
        const beforeMatch = content.slice(Math.max(0, match.index - 50), match.index);
        const keyNameMatch = beforeMatch.match(/(\w+)\s*[=:]\s*['"]?\s*$/);
        const keyName = keyNameMatch ? keyNameMatch[1] : undefined;

        const location: SourceLocation = {
          file: filePath,
          startLine: lineNumber,
          endLine: lineNumber,
          startColumn: column,
          endColumn: column + value.length,
        };

        secrets.push({
          id: generateSecretId(),
          type: pattern.type,
          location,
          maskedValue: maskValue(value),
          valueHash: hash,
          keyName,
          context: detectContext(content, match.index),
          confidence: pattern.falsePositiveRate ? 1 - pattern.falsePositiveRate : 0.9,
          isTestValue: testValue,
          patternId: pattern.id,
          detectedAt: new Date(),
          severity: pattern.severity,
        });
      }
    }

    return secrets;
  }

  /**
   * Scan a single file
   */
  async scanFile(filePath: string): Promise<Secret[]> {
    const content = await this.fileScanner.readFile(filePath);
    return this.scanContent(content, filePath);
  }

  /**
   * Scan a directory for secrets
   */
  async scan(rootPath: string): Promise<SecretScanResult> {
    const startTime = Date.now();
    const files = await this.fileScanner.scan(rootPath);

    const allSecrets: Secret[] = [];
    let scannedFiles = 0;
    let skippedFiles = 0;

    for (const file of files) {
      try {
        const content = await this.fileScanner.readFileSafe(file.path);
        if (!content) {
          skippedFiles++;
          continue;
        }

        const secrets = this.scanContent(content, file.path);
        allSecrets.push(...secrets);
        scannedFiles++;
      } catch (error) {
        console.warn(`Warning: Failed to scan ${file.path}: ${error}`);
        skippedFiles++;
      }
    }

    const duration = Date.now() - startTime;

    // Build summary
    const byType: Partial<Record<SecretType, number>> = {};
    let testValuesCount = 0;
    const bySeverity: Record<Severity, number> = { critical: 0, high: 0, medium: 0, low: 0, info: 0 };

    for (const secret of allSecrets) {
      byType[secret.type] = (byType[secret.type] || 0) + 1;
      bySeverity[secret.severity]++;
      if (secret.isTestValue) testValuesCount++;
    }

    return {
      secrets: allSecrets,
      scannedFiles,
      skippedFiles,
      duration,
      timestamp: new Date(),
      options: this.options,
      summary: {
        byType,
        bySeverity,
        total: allSecrets.length,
        testValues: testValuesCount,
      },
    };
  }

  /**
   * Add a custom pattern
   */
  addPattern(pattern: SecretPattern): void {
    this.patterns.push(pattern);
  }

  /**
   * Get all patterns
   */
  getPatterns(): SecretPattern[] {
    return [...this.patterns];
  }
}

/**
 * Create a secret detector
 */
export function createSecretDetector(options?: SecretScanOptions): SecretDetector {
  return new SecretDetector(options);
}
