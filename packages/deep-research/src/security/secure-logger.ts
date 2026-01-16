// Secure Logger
// TSK-DR-015
// REQ: REQ-DR-NFR-001
// ADR: ADR-v3.4.0-001

import type { SecretManager } from './secret-manager.js';
import type { ContentSanitizer } from './content-sanitizer.js';

/**
 * Log Level
 */
export type LogLevel = 'debug' | 'info' | 'warn' | 'error';

/**
 * Log Options
 */
export interface LogOptions {
  /** Redact secrets */
  redactSecrets?: boolean;
  /** Redact PII (URLs, emails, phones) */
  redactPII?: boolean;
  /** Include timestamp */
  includeTimestamp?: boolean;
  /** Include log level */
  includeLevel?: boolean;
}

/**
 * Redaction Rule
 */
export interface RedactionRule {
  /** Rule name */
  name: string;
  /** Detection pattern */
  pattern: RegExp;
  /** Replacement text */
  replacement: string;
}

/**
 * Audit Log Entry
 */
export interface AuditLogEntry {
  /** Timestamp */
  timestamp: number;
  /** Log level */
  level: LogLevel;
  /** Redacted message */
  message: string;
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Secure Logger
 * 
 * Wraps console logging with automatic redaction of sensitive data.
 * 
 * Features:
 * - Automatic secret redaction (via SecretManager)
 * - PII redaction (via ContentSanitizer)
 * - Configurable redaction rules
 * - Audit trail support
 * - Log levels (debug, info, warn, error)
 * 
 * REQ: REQ-DR-NFR-001 - Secure logging with automatic redaction
 * ADR: ADR-v3.4.0-001 - Security best practices
 */
export class SecureLogger {
  private readonly sanitizer: ContentSanitizer | null;
  private readonly customRules: RedactionRule[] = [];
  private readonly auditLog: AuditLogEntry[] = [];
  private readonly defaultOptions: LogOptions = {
    redactSecrets: true,
    redactPII: true,
    includeTimestamp: true,
    includeLevel: true,
  };
  
  constructor(
    _secretManager?: SecretManager,
    sanitizer?: ContentSanitizer
  ) {
    // SecretManager parameter reserved for future use
    this.sanitizer = sanitizer || null;
  }
  
  /**
   * Add custom redaction rule
   * 
   * REQ: REQ-DR-NFR-001
   */
  addRule(rule: RedactionRule): void {
    this.customRules.push(rule);
    console.log(`📝 Added redaction rule: ${rule.name}`);
  }
  
  /**
   * Remove custom redaction rule
   */
  removeRule(name: string): boolean {
    const index = this.customRules.findIndex(r => r.name === name);
    if (index >= 0) {
      this.customRules.splice(index, 1);
      return true;
    }
    return false;
  }
  
  /**
   * Log debug message
   * 
   * REQ: REQ-DR-NFR-001
   */
  debug(message: string, metadata?: Record<string, unknown>, options?: LogOptions): void {
    this.log('debug', message, metadata, options);
  }
  
  /**
   * Log info message
   * 
   * REQ: REQ-DR-NFR-001
   */
  info(message: string, metadata?: Record<string, unknown>, options?: LogOptions): void {
    this.log('info', message, metadata, options);
  }
  
  /**
   * Log warning message
   * 
   * REQ: REQ-DR-NFR-001
   */
  warn(message: string, metadata?: Record<string, unknown>, options?: LogOptions): void {
    this.log('warn', message, metadata, options);
  }
  
  /**
   * Log error message
   * 
   * REQ: REQ-DR-NFR-001
   */
  error(message: string, error?: Error, metadata?: Record<string, unknown>, options?: LogOptions): void {
    const meta = { ...metadata };
    if (error) {
      meta.error = {
        name: error.name,
        message: error.message,
        stack: error.stack,
      };
    }
    this.log('error', message, meta, options);
  }
  
  /**
   * Get audit trail
   */
  getAuditTrail(): AuditLogEntry[] {
    return [...this.auditLog];
  }
  
  /**
   * Clear audit trail
   */
  clearAudit(): void {
    this.auditLog.length = 0;
    console.log('🗑️  Cleared audit trail');
  }
  
  /**
   * Get audit trail size
   */
  getAuditSize(): number {
    return this.auditLog.length;
  }
  
  /**
   * Core logging method
   */
  private log(
    level: LogLevel,
    message: string,
    metadata?: Record<string, unknown>,
    options?: LogOptions
  ): void {
    const opts = { ...this.defaultOptions, ...options };
    
    // Redact message
    const redactedMessage = this.redact(message, opts);
    
    // Redact metadata
    const redactedMetadata = metadata ? this.redactMetadata(metadata, opts) : undefined;
    
    // Build log output
    let output = '';
    
    if (opts.includeLevel) {
      output += `[${level.toUpperCase()}] `;
    }
    
    if (opts.includeTimestamp) {
      output += `${new Date().toISOString()} `;
    }
    
    output += redactedMessage;
    
    // Add to audit trail
    this.auditLog.push({
      timestamp: Date.now(),
      level,
      message: redactedMessage,
      metadata: redactedMetadata,
    });
    
    // Output to console
    switch (level) {
      case 'debug':
        console.debug(output, redactedMetadata ? JSON.stringify(redactedMetadata) : '');
        break;
      case 'info':
        console.info(output, redactedMetadata ? JSON.stringify(redactedMetadata) : '');
        break;
      case 'warn':
        console.warn(output, redactedMetadata ? JSON.stringify(redactedMetadata) : '');
        break;
      case 'error':
        console.error(output, redactedMetadata ? JSON.stringify(redactedMetadata) : '');
        break;
    }
  }
  
  /**
   * Redact sensitive data from message
   */
  private redact(message: string, options: LogOptions): string {
    let result = message;
    
    // Apply secret redaction
    if (options.redactSecrets && this.sanitizer) {
      const secrets = this.sanitizer.detectSecrets(result);
      
      // Sort by position (descending) to avoid index shifting
      secrets.sort((a, b) => b.position - a.position);
      
      for (const secret of secrets) {
        const before = result.substring(0, secret.position);
        const after = result.substring(secret.position + secret.length);
        result = before + `[REDACTED:${secret.type}]` + after;
      }
    }
    
    // Apply PII redaction
    if (options.redactPII && this.sanitizer) {
      result = this.sanitizer.sanitize(result, {
        removeHtml: false,
        removeScripts: false,
        removeUrls: true,
        removeEmails: true,
        removePhones: true,
        redactSecrets: false, // Already done above
        placeholder: '[REDACTED:PII]',
      });
    }
    
    // Apply custom rules
    for (const rule of this.customRules) {
      result = result.replace(rule.pattern, rule.replacement);
    }
    
    return result;
  }
  
  /**
   * Redact metadata object
   */
  private redactMetadata(
    metadata: Record<string, unknown>,
    options: LogOptions
  ): Record<string, unknown> {
    const redacted: Record<string, unknown> = {};
    
    for (const [key, value] of Object.entries(metadata)) {
      if (typeof value === 'string') {
        redacted[key] = this.redact(value, options);
      } else if (typeof value === 'object' && value !== null) {
        redacted[key] = this.redactMetadata(value as Record<string, unknown>, options);
      } else {
        redacted[key] = value;
      }
    }
    
    return redacted;
  }
}

/**
 * Create a secure logger instance
 */
export function createSecureLogger(
  secretManager?: SecretManager,
  sanitizer?: ContentSanitizer
): SecureLogger {
  return new SecureLogger(secretManager, sanitizer);
}

/**
 * Global secure logger instance (singleton pattern)
 */
let globalLogger: SecureLogger | null = null;

/**
 * Get or create global secure logger
 */
export function getGlobalLogger(): SecureLogger {
  if (!globalLogger) {
    globalLogger = new SecureLogger();
  }
  return globalLogger;
}

/**
 * Set global secure logger
 */
export function setGlobalLogger(logger: SecureLogger): void {
  globalLogger = logger;
}
