// Content Sanitizer
// TSK-DR-014
// REQ: REQ-DR-NFR-001, REQ-DR-NFR-002
// ADR: ADR-v3.4.0-001

/**
 * Sanitization Options
 */
export interface SanitizationOptions {
  /** Remove HTML tags */
  removeHtml?: boolean;
  /** Remove script tags specifically */
  removeScripts?: boolean;
  /** Remove URLs */
  removeUrls?: boolean;
  /** Remove email addresses */
  removeEmails?: boolean;
  /** Remove phone numbers */
  removePhones?: boolean;
  /** Redact secrets (API keys, tokens) */
  redactSecrets?: boolean;
  /** Replace with placeholder */
  placeholder?: string;
}

/**
 * Detected Secret
 */
export interface DetectedSecret {
  /** Secret type */
  type: 'api-key' | 'token' | 'password' | 'private-key' | 'unknown';
  /** Original position in text */
  position: number;
  /** Length of secret */
  length: number;
  /** Pattern that matched */
  pattern: string;
}

/**
 * Content Sanitizer
 * 
 * Sanitizes user input and generated content to prevent:
 * - XSS attacks
 * - Secret leakage
 * - PII exposure
 * - Malicious content injection
 * 
 * REQ: REQ-DR-NFR-001 - Data privacy protection
 * REQ: REQ-DR-NFR-002 - Input validation
 * ADR: ADR-v3.4.0-001 - Security best practices
 */
export class ContentSanitizer {
  private readonly defaultOptions: SanitizationOptions = {
    removeHtml: true,
    removeScripts: true,
    removeUrls: false,
    removeEmails: false,
    removePhones: false,
    redactSecrets: true,
    placeholder: '[REDACTED]',
  };
  
  /**
   * Sanitize content
   * 
   * REQ: REQ-DR-NFR-001, REQ-DR-NFR-002
   */
  sanitize(content: string, options?: SanitizationOptions): string {
    if (!content) return content;
    
    const opts = { ...this.defaultOptions, ...options };
    let result = content;
    
    // Remove script tags first (highest priority)
    if (opts.removeScripts) {
      result = this.removeScripts(result);
    }
    
    // Remove HTML tags
    if (opts.removeHtml) {
      result = this.removeHtml(result);
    }
    
    // Redact secrets
    if (opts.redactSecrets) {
      result = this.redactSecrets(result, opts.placeholder!);
    }
    
    // Remove URLs
    if (opts.removeUrls) {
      result = this.removeUrls(result, opts.placeholder!);
    }
    
    // Remove emails
    if (opts.removeEmails) {
      result = this.removeEmails(result, opts.placeholder!);
    }
    
    // Remove phone numbers
    if (opts.removePhones) {
      result = this.removePhones(result, opts.placeholder!);
    }
    
    return result;
  }
  
  /**
   * Detect secrets in content
   * 
   * REQ: REQ-DR-NFR-001
   */
  detectSecrets(content: string): DetectedSecret[] {
    const secrets: DetectedSecret[] = [];
    
    // Private keys (check first - most specific)
    const privateKeyPattern = /-----BEGIN (RSA |EC )?PRIVATE KEY-----[\s\S]+?-----END (RSA |EC )?PRIVATE KEY-----/g;
    const pkMatches = content.matchAll(privateKeyPattern);
    for (const match of pkMatches) {
      if (match.index !== undefined) {
        secrets.push({
          type: 'private-key',
          position: match.index,
          length: match[0].length,
          pattern: 'private-key',
        });
      }
    }
    
    // JWT tokens (check before generic patterns)
    const jwtPattern = /\beyJ[A-Za-z0-9_-]+\.eyJ[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+\b/g;
    const jwtMatches = content.matchAll(jwtPattern);
    for (const match of jwtMatches) {
      if (match.index !== undefined) {
        secrets.push({
          type: 'token',
          position: match.index,
          length: match[0].length,
          pattern: jwtPattern.source,
        });
      }
    }
    
    // Specific API key patterns
    const specificApiKeyPatterns: Array<{ pattern: RegExp; type: DetectedSecret['type'] }> = [
      { pattern: /\bsk_[a-z]{4}_[A-Za-z0-9]{24,}\b/g, type: 'api-key' }, // Stripe-like keys
      { pattern: /\bAKIA[0-9A-Z]{16}\b/g, type: 'api-key' }, // AWS access key
      { pattern: /\bghp_[a-zA-Z0-9]{36}\b/g, type: 'api-key' }, // GitHub personal token
      { pattern: /\bgho_[a-zA-Z0-9]{36}\b/g, type: 'api-key' }, // GitHub OAuth token
    ];
    
    for (const { pattern, type } of specificApiKeyPatterns) {
      const matches = content.matchAll(pattern);
      for (const match of matches) {
        if (match.index !== undefined) {
          secrets.push({
            type,
            position: match.index,
            length: match[0].length,
            pattern: pattern.source,
          });
        }
      }
    }
    
    // Generic 32+ char alphanumeric (last resort - most false positives)
    // Skip if already detected by specific patterns
    const detectedRanges = secrets.map(s => ({ start: s.position, end: s.position + s.length }));
    const genericPattern = /\b[A-Za-z0-9]{32,}\b/g;
    const genericMatches = content.matchAll(genericPattern);
    
    for (const match of genericMatches) {
      if (match.index !== undefined) {
        const matchStart = match.index;
        const matchEnd = match.index + match[0].length;
        
        // Check if already detected by specific pattern
        const alreadyDetected = detectedRanges.some(range => 
          matchStart >= range.start && matchEnd <= range.end
        );
        
        if (!alreadyDetected) {
          secrets.push({
            type: 'api-key',
            position: match.index,
            length: match[0].length,
            pattern: genericPattern.source,
          });
        }
      }
    }
    
    return secrets;
  }
  
  /**
   * Remove HTML tags
   */
  private removeHtml(content: string): string {
    return content.replace(/<[^>]*>/g, '');
  }
  
  /**
   * Remove script tags and their content
   */
  private removeScripts(content: string): string {
    return content.replace(/<script\b[^<]*(?:(?!<\/script>)<[^<]*)*<\/script>/gi, '');
  }
  
  /**
   * Redact secrets
   */
  private redactSecrets(content: string, placeholder: string): string {
    const secrets = this.detectSecrets(content);
    
    if (secrets.length === 0) {
      return content;
    }
    
    // Sort by position (descending) to avoid index shifting
    secrets.sort((a, b) => b.position - a.position);
    
    let result = content;
    for (const secret of secrets) {
      const before = result.substring(0, secret.position);
      const after = result.substring(secret.position + secret.length);
      result = before + placeholder + after;
    }
    
    return result;
  }
  
  /**
   * Remove URLs
   */
  private removeUrls(content: string, placeholder: string): string {
    return content.replace(
      /https?:\/\/(www\.)?[-a-zA-Z0-9@:%._+~#=]{1,256}\.[a-zA-Z0-9()]{1,6}\b([-a-zA-Z0-9()@:%_+.~#?&/=]*)/g,
      placeholder
    );
  }
  
  /**
   * Remove email addresses
   */
  private removeEmails(content: string, placeholder: string): string {
    return content.replace(
      /\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b/g,
      placeholder
    );
  }
  
  /**
   * Remove phone numbers
   */
  private removePhones(content: string, placeholder: string): string {
    // Simple pattern for common formats
    return content.replace(
      /\b(\+?\d{1,3}[-.\s]?)?\(?\d{3}\)?[-.\s]?\d{3}[-.\s]?\d{4}\b/g,
      placeholder
    );
  }
  
  /**
   * Escape HTML entities
   */
  escapeHtml(content: string): string {
    const htmlEntities: Record<string, string> = {
      '&': '&amp;',
      '<': '&lt;',
      '>': '&gt;',
      '"': '&quot;',
      "'": '&#39;',
      '/': '&#x2F;',
    };
    
    return content.replace(/[&<>"'/]/g, (char) => htmlEntities[char] || char);
  }
  
  /**
   * Validate content length
   */
  validateLength(content: string, maxLength: number): boolean {
    return content.length <= maxLength;
  }
  
  /**
   * Check if content is safe (no detected secrets or malicious patterns)
   */
  isSafe(content: string): boolean {
    // Check for scripts
    if (/<script/i.test(content)) {
      return false;
    }
    
    // Check for secrets
    const secrets = this.detectSecrets(content);
    if (secrets.length > 0) {
      return false;
    }
    
    // Check for common XSS patterns
    const xssPatterns = [
      /javascript:/i,
      /on\w+\s*=/i, // onclick=, onerror=, etc.
      /<iframe/i,
      /<embed/i,
      /<object/i,
    ];
    
    for (const pattern of xssPatterns) {
      if (pattern.test(content)) {
        return false;
      }
    }
    
    return true;
  }
}

/**
 * Create a content sanitizer instance
 */
export function createContentSanitizer(): ContentSanitizer {
  return new ContentSanitizer();
}

/**
 * Global content sanitizer instance (singleton pattern)
 */
let globalSanitizer: ContentSanitizer | null = null;

/**
 * Get or create global content sanitizer
 */
export function getGlobalSanitizer(): ContentSanitizer {
  if (!globalSanitizer) {
    globalSanitizer = new ContentSanitizer();
  }
  return globalSanitizer;
}
