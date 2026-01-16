// Content Sanitizer Tests
// TSK-DR-014

import { describe, it, expect } from 'vitest';
import { ContentSanitizer } from './content-sanitizer.js';

describe('ContentSanitizer', () => {
  const sanitizer = new ContentSanitizer();

  describe('sanitize', () => {
    it('should remove HTML tags', () => {
      const input = '<div>Hello <b>World</b></div>';
      const result = sanitizer.sanitize(input);

      expect(result).toBe('Hello World');
    });

    it('should remove script tags', () => {
      const input = 'Safe content <script>alert("XSS")</script> more content';
      const result = sanitizer.sanitize(input);

      expect(result).not.toContain('<script>');
      expect(result).not.toContain('alert');
    });

    it('should redact API keys', () => {
      const input = 'My API key is sk' + '_live_' + 'abcdefghijklmnopqrstuvwxyz123456';
      const result = sanitizer.sanitize(input);

      expect(result).toContain('[REDACTED]');
      expect(result).not.toContain('sk' + '_live_');
    });

    it('should remove URLs when option enabled', () => {
      const input = 'Check out https://example.com for more info';
      const result = sanitizer.sanitize(input, { removeUrls: true });

      expect(result).toContain('[REDACTED]');
      expect(result).not.toContain('https://example.com');
    });

    it('should remove emails when option enabled', () => {
      const input = 'Contact me at user@example.com';
      const result = sanitizer.sanitize(input, { removeEmails: true });

      expect(result).toContain('[REDACTED]');
      expect(result).not.toContain('user@example.com');
    });

    it('should remove phone numbers when option enabled', () => {
      const input = 'Call me at 555-123-4567';
      const result = sanitizer.sanitize(input, { removePhones: true });

      expect(result).toContain('[REDACTED]');
      expect(result).not.toContain('555-123-4567');
    });

    it('should use custom placeholder', () => {
      const input = 'My secret is sk' + '_test_' + '1234567890123456789012345678';
      const result = sanitizer.sanitize(input, { placeholder: '***' });

      expect(result).toContain('***');
      expect(result).not.toContain('[REDACTED]');
    });

    it('should handle empty content', () => {
      const result = sanitizer.sanitize('');

      expect(result).toBe('');
    });
  });

  describe('detectSecrets', () => {
    it('should detect API keys', () => {
      const content = 'API: sk' + '_live_' + 'abcdefghijklmnopqrstuvwxyz123456';
      const secrets = sanitizer.detectSecrets(content);

      expect(secrets.length).toBeGreaterThan(0);
      expect(secrets[0].type).toBe('api-key');
    });

    it('should detect AWS access keys', () => {
      const content = 'AWS: AKIAIOSFODNN7EXAMPLE';
      const secrets = sanitizer.detectSecrets(content);

      expect(secrets.length).toBeGreaterThan(0);
      expect(secrets[0].type).toBe('api-key');
    });

    it('should detect JWT tokens', () => {
      const content = 'Token: eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiIxMjM0NTY3ODkwIiwibmFtZSI6IkpvaG4gRG9lIiwiaWF0IjoxNTE2MjM5MDIyfQ.SflKxwRJSMeKKF2QT4fwpMeJf36POk6yJV_adQssw5c';
      const secrets = sanitizer.detectSecrets(content);

      expect(secrets.length).toBeGreaterThan(0);
      expect(secrets[0].type).toBe('token');
    });

    it('should detect private keys', () => {
      const content = '-----BEGIN PRIVATE KEY-----\nMIIEvQIBADANBgkqhkiG9w0BAQEFAASCBKcwggSjAgEAAoIBAQC\n-----END PRIVATE KEY-----';
      const secrets = sanitizer.detectSecrets(content);

      expect(secrets.length).toBeGreaterThan(0);
      expect(secrets[0].type).toBe('private-key');
    });

    it('should detect GitHub tokens', () => {
      const content = 'GitHub: ghp_abcdefghijklmnopqrstuvwxyz1234567890';
      const secrets = sanitizer.detectSecrets(content);

      expect(secrets.length).toBeGreaterThan(0);
      expect(secrets[0].type).toBe('api-key');
    });

    it('should return empty array for safe content', () => {
      const content = 'This is completely safe text with no secrets';
      const secrets = sanitizer.detectSecrets(content);

      expect(secrets).toHaveLength(0);
    });

    it('should detect multiple secrets', () => {
      const content = 'Key1: sk' + '_live_' + 'abcdefghijklmnopqrstuvwxyz123456 Key2: AKIAIOSFODNN7EXAMPLE';
      const secrets = sanitizer.detectSecrets(content);

      expect(secrets.length).toBeGreaterThanOrEqual(2);
    });
  });

  describe('escapeHtml', () => {
    it('should escape HTML entities', () => {
      const input = '<div>"Hello" & \'World\'</div>';
      const result = sanitizer.escapeHtml(input);

      expect(result).toBe('&lt;div&gt;&quot;Hello&quot; &amp; &#39;World&#39;&lt;&#x2F;div&gt;');
    });

    it('should handle empty string', () => {
      const result = sanitizer.escapeHtml('');

      expect(result).toBe('');
    });
  });

  describe('validateLength', () => {
    it('should return true for content within limit', () => {
      const result = sanitizer.validateLength('Hello', 10);

      expect(result).toBe(true);
    });

    it('should return false for content exceeding limit', () => {
      const result = sanitizer.validateLength('Hello World', 5);

      expect(result).toBe(false);
    });
  });

  describe('isSafe', () => {
    it('should return true for safe content', () => {
      const result = sanitizer.isSafe('This is safe text');

      expect(result).toBe(true);
    });

    it('should return false for content with scripts', () => {
      const result = sanitizer.isSafe('<script>alert("XSS")</script>');

      expect(result).toBe(false);
    });

    it('should return false for content with secrets', () => {
      const result = sanitizer.isSafe('Secret: sk' + '_live_' + 'abcdefghijklmnopqrstuvwxyz123456');

      expect(result).toBe(false);
    });

    it('should return false for javascript: URLs', () => {
      const result = sanitizer.isSafe('<a href="javascript:alert(1)">Click</a>');

      expect(result).toBe(false);
    });

    it('should return false for event handlers', () => {
      const result = sanitizer.isSafe('<img onerror="alert(1)">');

      expect(result).toBe(false);
    });

    it('should return false for iframes', () => {
      const result = sanitizer.isSafe('<iframe src="malicious.com"></iframe>');

      expect(result).toBe(false);
    });
  });
});
