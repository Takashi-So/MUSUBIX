// Secure Logger Tests
// TSK-DR-015

import { describe, it, expect, beforeEach } from 'vitest';
import { SecureLogger } from './secure-logger.js';
import { SecretManager } from './secret-manager.js';
import { ContentSanitizer } from './content-sanitizer.js';

describe('SecureLogger', () => {
  let logger: SecureLogger;
  let secretManager: SecretManager;
  let sanitizer: ContentSanitizer;
  let consoleOutput: string[] = [];
  
  // Capture console output
  const originalConsole = {
    debug: console.debug,
    info: console.info,
    warn: console.warn,
    error: console.error,
  };
  
  beforeEach(() => {
    secretManager = new SecretManager('test-key');
    sanitizer = new ContentSanitizer();
    logger = new SecureLogger(secretManager, sanitizer);
    
    consoleOutput = [];
    
    // Override console methods to capture output
    console.debug = (...args: any[]) => { consoleOutput.push(args.join(' ')); };
    console.info = (...args: any[]) => { consoleOutput.push(args.join(' ')); };
    console.warn = (...args: any[]) => { consoleOutput.push(args.join(' ')); };
    console.error = (...args: any[]) => { consoleOutput.push(args.join(' ')); };
  });

  describe('basic logging', () => {
    it('should log debug message', () => {
      logger.debug('Debug message');

      expect(consoleOutput.length).toBeGreaterThan(0);
      expect(consoleOutput[0]).toContain('[DEBUG]');
      expect(consoleOutput[0]).toContain('Debug message');
    });

    it('should log info message', () => {
      logger.info('Info message');

      expect(consoleOutput.length).toBeGreaterThan(0);
      expect(consoleOutput[0]).toContain('[INFO]');
      expect(consoleOutput[0]).toContain('Info message');
    });

    it('should log warn message', () => {
      logger.warn('Warning message');

      expect(consoleOutput.length).toBeGreaterThan(0);
      expect(consoleOutput[0]).toContain('[WARN]');
      expect(consoleOutput[0]).toContain('Warning message');
    });

    it('should log error message', () => {
      logger.error('Error message');

      expect(consoleOutput.length).toBeGreaterThan(0);
      expect(consoleOutput[0]).toContain('[ERROR]');
      expect(consoleOutput[0]).toContain('Error message');
    });

    it('should include timestamp', () => {
      logger.info('Test message');

      expect(consoleOutput[0]).toMatch(/\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}/);
    });

    it('should support metadata', () => {
      logger.info('Test message', { userId: 123, action: 'login' });

      expect(consoleOutput.length).toBeGreaterThan(0);
      expect(consoleOutput[0]).toContain('Test message');
      // Metadata is logged as second argument, converted to string
      expect(consoleOutput[0]).toContain('userId');
    });

    it('should log error with Error object', () => {
      const error = new Error('Test error');
      logger.error('Error occurred', error);

      expect(consoleOutput.length).toBeGreaterThan(0);
      expect(consoleOutput[0]).toContain('[ERROR]');
      expect(consoleOutput[0]).toContain('Error occurred');
    });
  });

  describe('secret redaction', () => {
    it('should redact API keys', () => {
      const message = 'API key: sk' + '_live_' + 'abcdefghijklmnopqrstuvwxyz123456';
      logger.info(message);

      expect(consoleOutput[0]).toContain('[REDACTED:api-key]');
      expect(consoleOutput[0]).not.toContain('sk' + '_live_');
    });

    it('should redact JWT tokens', () => {
      const token = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiIxMjM0NTY3ODkwIn0.dozjgNryP4J3jVmNHl0w5N_XgL0n3I9PlFUP0THsR8U';
      logger.info(`Token: ${token}`);

      expect(consoleOutput[0]).toContain('[REDACTED:token]');
      expect(consoleOutput[0]).not.toContain('eyJhbGciOiJI');
    });

    it('should redact secrets in metadata', () => {
      logger.info('Metadata test', { apiKey: 'sk' + '_live_' + 'abcdefghijklmnopqrstuvwxyz123456' });

      expect(consoleOutput[0]).toContain('[REDACTED:api-key]');
    });

    it('should not redact when option disabled', () => {
      const message = 'API key: sk' + '_live_' + 'abcdefghijklmnopqrstuvwxyz123456';
      logger.info(message, undefined, { redactSecrets: false });

      expect(consoleOutput[0]).toContain('sk' + '_live_');
    });
  });

  describe('PII redaction', () => {
    it('should redact URLs', () => {
      logger.info('Check https://example.com for details');

      expect(consoleOutput[0]).toContain('[REDACTED:PII]');
      expect(consoleOutput[0]).not.toContain('https://example.com');
    });

    it('should redact emails', () => {
      logger.info('Contact user@example.com');

      expect(consoleOutput[0]).toContain('[REDACTED:PII]');
      expect(consoleOutput[0]).not.toContain('user@example.com');
    });

    it('should redact phone numbers', () => {
      logger.info('Call 555-123-4567');

      expect(consoleOutput[0]).toContain('[REDACTED:PII]');
      expect(consoleOutput[0]).not.toContain('555-123-4567');
    });

    it('should not redact when option disabled', () => {
      logger.info('Check https://example.com', undefined, { redactPII: false });

      expect(consoleOutput[0]).toContain('https://example.com');
    });
  });

  describe('custom redaction rules', () => {
    it('should apply custom rule', () => {
      logger.addRule({
        name: 'credit-card',
        pattern: /\b\d{4}-\d{4}-\d{4}-\d{4}\b/g,
        replacement: '[REDACTED:CARD]',
      });

      // addRule outputs to console, so we have 1 output
      // Then info() adds another
      const beforeLength = consoleOutput.length;
      logger.info('Card: 1234-5678-9012-3456');

      const lastOutput = consoleOutput[consoleOutput.length - 1];
      expect(lastOutput).toContain('[REDACTED:CARD]');
      expect(lastOutput).not.toContain('1234-5678');
    });

    it('should remove custom rule', () => {
      logger.addRule({
        name: 'test-rule',
        pattern: /secret/g,
        replacement: '[REMOVED]',
      });

      const removed = logger.removeRule('test-rule');

      expect(removed).toBe(true);
    });

    it('should return false for non-existent rule', () => {
      const removed = logger.removeRule('non-existent');

      expect(removed).toBe(false);
    });
  });

  describe('audit trail', () => {
    it('should record audit entry', () => {
      logger.info('Test message');

      const audit = logger.getAuditTrail();
      expect(audit).toHaveLength(1);
      expect(audit[0].level).toBe('info');
      expect(audit[0].message).toContain('Test message');
    });

    it('should record multiple entries', () => {
      logger.debug('Debug');
      logger.info('Info');
      logger.warn('Warn');
      logger.error('Error');

      const audit = logger.getAuditTrail();
      expect(audit).toHaveLength(4);
      expect(audit[0].level).toBe('debug');
      expect(audit[3].level).toBe('error');
    });

    it('should include metadata in audit', () => {
      logger.info('Test', { userId: 123 });

      const audit = logger.getAuditTrail();
      expect(audit[0].metadata).toEqual({ userId: 123 });
    });

    it('should clear audit trail', () => {
      logger.info('Test 1');
      logger.info('Test 2');

      logger.clearAudit();

      const audit = logger.getAuditTrail();
      expect(audit).toHaveLength(0);
    });

    it('should return audit size', () => {
      logger.info('Test 1');
      logger.info('Test 2');
      logger.info('Test 3');

      expect(logger.getAuditSize()).toBe(3);
    });
  });

  describe('log options', () => {
    it('should exclude timestamp when option disabled', () => {
      logger.info('Test', undefined, { includeTimestamp: false });

      expect(consoleOutput[0]).not.toMatch(/\d{4}-\d{2}-\d{2}/);
    });

    it('should exclude level when option disabled', () => {
      logger.info('Test', undefined, { includeLevel: false });

      expect(consoleOutput[0]).not.toContain('[INFO]');
    });
  });

  describe('without dependencies', () => {
    it('should work without SecretManager', () => {
      const standaloneLogger = new SecureLogger(undefined, sanitizer);
      
      standaloneLogger.info('Test message');

      expect(consoleOutput.length).toBeGreaterThan(0);
    });

    it('should work without ContentSanitizer', () => {
      const standaloneLogger = new SecureLogger(secretManager, undefined);
      
      standaloneLogger.info('Test message');

      expect(consoleOutput.length).toBeGreaterThan(0);
    });

    it('should work without both dependencies', () => {
      const standaloneLogger = new SecureLogger();
      
      standaloneLogger.info('Test message');

      expect(consoleOutput.length).toBeGreaterThan(0);
    });
  });
});
