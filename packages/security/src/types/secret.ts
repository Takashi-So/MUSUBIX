/**
 * @fileoverview Secret detection type definitions
 * @module @nahisaho/musubix-security/types/secret
 * @trace REQ-SEC-SECRET-001, REQ-SEC-SECRET-002
 */

import type { SourceLocation, Severity } from './vulnerability.js';

/**
 * Secret type classification
 * @trace REQ-SEC-SECRET-001
 */
export type SecretType =
  | 'api-key' // Generic API keys
  | 'aws-access-key' // AWS Access Key ID
  | 'aws-secret-key' // AWS Secret Access Key
  | 'azure-connection-string' // Azure connection strings
  | 'gcp-service-account' // GCP service account keys
  | 'github-token' // GitHub personal access tokens
  | 'gitlab-token' // GitLab tokens
  | 'npm-token' // npm tokens
  | 'private-key' // RSA/EC private keys
  | 'ssh-key' // SSH private keys
  | 'database-url' // Database connection strings
  | 'jwt-secret' // JWT signing secrets
  | 'oauth-secret' // OAuth client secrets
  | 'password' // Hardcoded passwords
  | 'encryption-key' // Encryption keys
  | 'slack-webhook' // Slack webhook URLs
  | 'stripe-key' // Stripe API keys
  | 'twilio-key' // Twilio API keys
  | 'sendgrid-key' // SendGrid API keys
  | 'custom'; // Custom pattern match

/**
 * Secret context (where it was found)
 */
export type SecretContext =
  | 'source-code' // In source code file
  | 'config-file' // In configuration file
  | 'environment' // In .env file
  | 'comment' // In code comment
  | 'string-literal' // In string literal
  | 'template-literal' // In template literal
  | 'object-property' // As object property value
  | 'array-element'; // As array element

/**
 * Detected secret
 * @trace REQ-SEC-SECRET-001
 */
export interface Secret {
  /** Unique secret ID (e.g., "SEC-2026-001") */
  id: string;
  /** Secret type */
  type: SecretType;
  /** Source code location */
  location: SourceLocation;
  /** Masked value (first 4 and last 4 chars visible) */
  maskedValue: string;
  /** Full value hash (SHA-256) for deduplication */
  valueHash: string;
  /** Variable/key name if identifiable */
  keyName?: string;
  /** Context where secret was found */
  context: SecretContext;
  /** Detection confidence (0.0 - 1.0) */
  confidence: number;
  /** Whether this appears to be a test/example value */
  isTestValue: boolean;
  /** Pattern ID that detected this secret */
  patternId: string;
  /** Detection timestamp */
  detectedAt: Date;
  /** Severity based on secret type */
  severity: Severity;
}

/**
 * Secret detection pattern
 * @trace REQ-SEC-SECRET-002
 */
export interface SecretPattern {
  /** Unique pattern ID */
  id: string;
  /** Pattern name */
  name: string;
  /** Secret type this pattern detects */
  type: SecretType;
  /** Regex pattern to match */
  regex: RegExp;
  /** Optional key name patterns (for key=value pairs) */
  keyPatterns?: RegExp[];
  /** Severity when matched */
  severity: Severity;
  /** Patterns that indicate test/example values */
  testValuePatterns?: RegExp[];
  /** Additional validation function name */
  validator?: string;
  /** Pattern description */
  description: string;
  /** Whether pattern is enabled by default */
  enabled: boolean;
  /** False positive rate (for tuning) */
  falsePositiveRate?: number;
}

/**
 * Built-in secret patterns
 */
export const BUILTIN_SECRET_PATTERNS: Omit<SecretPattern, 'regex' | 'keyPatterns' | 'testValuePatterns'>[] = [
  {
    id: 'aws-access-key',
    name: 'AWS Access Key ID',
    type: 'aws-access-key',
    severity: 'critical',
    description: 'AWS Access Key ID (starts with AKIA)',
    enabled: true,
  },
  {
    id: 'aws-secret-key',
    name: 'AWS Secret Access Key',
    type: 'aws-secret-key',
    severity: 'critical',
    description: 'AWS Secret Access Key (40 character base64)',
    enabled: true,
  },
  {
    id: 'github-pat',
    name: 'GitHub Personal Access Token',
    type: 'github-token',
    severity: 'critical',
    description: 'GitHub PAT (ghp_*, gho_*, ghu_*, ghs_*, ghr_*)',
    enabled: true,
  },
  {
    id: 'private-key',
    name: 'Private Key',
    type: 'private-key',
    severity: 'critical',
    description: 'RSA/EC/DSA private key in PEM format',
    enabled: true,
  },
  {
    id: 'jwt-secret',
    name: 'JWT Secret',
    type: 'jwt-secret',
    severity: 'high',
    description: 'JWT signing secret in common patterns',
    enabled: true,
  },
  {
    id: 'database-url',
    name: 'Database URL',
    type: 'database-url',
    severity: 'high',
    description: 'Database connection string with credentials',
    enabled: true,
  },
  {
    id: 'generic-api-key',
    name: 'Generic API Key',
    type: 'api-key',
    severity: 'medium',
    description: 'Generic API key patterns',
    enabled: true,
  },
  {
    id: 'azure-connection',
    name: 'Azure Connection String',
    type: 'azure-connection-string',
    severity: 'critical',
    description: 'Azure storage/service connection strings',
    enabled: true,
  },
  {
    id: 'stripe-key',
    name: 'Stripe API Key',
    type: 'stripe-key',
    severity: 'critical',
    description: 'Stripe API keys (sk_live_*, rk_live_*)',
    enabled: true,
  },
  {
    id: 'slack-webhook',
    name: 'Slack Webhook URL',
    type: 'slack-webhook',
    severity: 'medium',
    description: 'Slack incoming webhook URLs',
    enabled: true,
  },
];

/**
 * Secret scan options
 */
export interface SecretScanOptions {
  /** Custom patterns to use */
  customPatterns?: SecretPattern[];
  /** Built-in patterns to disable */
  disablePatterns?: string[];
  /** File patterns to exclude */
  excludePatterns?: string[];
  /** Ignore test/example values */
  ignoreTestValues?: boolean;
  /** Maximum file size in bytes */
  maxFileSize?: number;
  /** Verify secrets (check if they're valid/active) */
  verify?: boolean;
  /** Entropy threshold for generic detection */
  entropyThreshold?: number;
}

/**
 * Secret scan result
 * @trace REQ-SEC-SECRET-001
 */
export interface SecretScanResult {
  /** Detected secrets */
  secrets: Secret[];
  /** Number of files scanned */
  scannedFiles: number;
  /** Number of files skipped */
  skippedFiles: number;
  /** Scan duration in milliseconds */
  duration: number;
  /** Scan timestamp */
  timestamp: Date;
  /** Scan options used */
  options: SecretScanOptions;
  /** Summary by type */
  summary: {
    byType: Partial<Record<SecretType, number>>;
    bySeverity: {
      critical: number;
      high: number;
      medium: number;
      low: number;
    };
    total: number;
    testValues: number;
  };
}

/**
 * Secret verification result
 */
export interface SecretVerification {
  /** Secret ID */
  secretId: string;
  /** Whether the secret is valid/active */
  isValid: boolean;
  /** Verification method used */
  method: 'api-call' | 'format-check' | 'entropy' | 'none';
  /** Additional info from verification */
  info?: {
    /** For API keys: associated account/org */
    account?: string;
    /** For API keys: permissions */
    permissions?: string[];
    /** Expiration if known */
    expiresAt?: Date;
  };
  /** Verification timestamp */
  verifiedAt: Date;
  /** Error if verification failed */
  error?: string;
}
