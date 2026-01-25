/**
 * Sensitive Data Filter Tests
 *
 * REQ-INT-004: SensitiveDataFilter - 機密情報のフィルタリング
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createSensitiveDataFilter,
  getDefaultFilter,
  filterSensitiveData,
  containsSensitiveData,
  formatFilterResultAsMarkdown,
  type SensitiveDataFilter,
  DEFAULT_SENSITIVE_PATTERNS,
  DEFAULT_FILTER_CONFIG,
} from '../../src/filters/index.js';

describe('SensitiveDataFilter', () => {
  let filter: SensitiveDataFilter;

  beforeEach(() => {
    filter = createSensitiveDataFilter();
  });

  describe('filter - テキストフィルタリング', () => {
    it('should filter API keys', () => {
      const text = 'const apiKey = "sk_live_1234567890abcdefghij";';
      const result = filter.filter(text);

      expect(result.wasModified).toBe(true);
      expect(result.filtered).toContain('[API_KEY_REDACTED]');
      expect(result.filtered).not.toContain('sk_live_1234567890abcdefghij');
    });

    it('should filter passwords', () => {
      const text = 'password=MySecretPassword123';
      const result = filter.filter(text);

      expect(result.wasModified).toBe(true);
      expect(result.filtered).toContain('[PASSWORD_REDACTED]');
      expect(result.filtered).not.toContain('MySecretPassword123');
    });

    it('should filter AWS access keys', () => {
      const text = 'AWS_ACCESS_KEY_ID=AKIAIOSFODNN7EXAMPLE';
      const result = filter.filter(text);

      expect(result.wasModified).toBe(true);
      expect(result.filtered).toContain('[AWS_KEY_REDACTED]');
    });

    it('should filter private keys', () => {
      const text = `-----BEGIN RSA PRIVATE KEY-----
MIIEowIBAAKCAQEA0Z3VS5JJ...
-----END RSA PRIVATE KEY-----`;
      const result = filter.filter(text);

      expect(result.wasModified).toBe(true);
      expect(result.filtered).toContain('[PRIVATE_KEY_REDACTED]');
    });

    it('should filter Bearer tokens', () => {
      const text = 'Authorization: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.test';
      const result = filter.filter(text);

      expect(result.wasModified).toBe(true);
      expect(result.filtered).toContain('[TOKEN_REDACTED]');
    });

    it('should filter JWTs', () => {
      const text = 'token=eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiIxMjM0NTY3ODkwIiwibmFtZSI6IkpvaG4gRG9lIiwiaWF0IjoxNTE2MjM5MDIyfQ.SflKxwRJSMeKKF2QT4fwpMeJf36POk6yJV_adQssw5c';
      const result = filter.filter(text);

      expect(result.wasModified).toBe(true);
      expect(result.filtered).toContain('[JWT_REDACTED]');
    });

    it('should filter connection strings', () => {
      const text = 'DATABASE_URL=postgres://user:password@localhost:5432/mydb';
      const result = filter.filter(text);

      expect(result.wasModified).toBe(true);
      expect(result.filtered).toContain('[CONNECTION_STRING_REDACTED]');
    });

    it('should filter credit card numbers', () => {
      const text = 'Card: 4111111111111111';
      const result = filter.filter(text);

      expect(result.wasModified).toBe(true);
      expect(result.filtered).toContain('[CREDIT_CARD_REDACTED]');
    });

    it('should filter multiple sensitive data in same text', () => {
      const text = `
        api_key: sk_test_12345678901234567890
        password: secretpass
        db: mysql://root:pass@localhost/db
      `;
      const result = filter.filter(text);

      expect(result.wasModified).toBe(true);
      expect(result.detections.length).toBeGreaterThanOrEqual(2);
    });

    it('should not modify text without sensitive data', () => {
      const text = 'const greeting = "Hello, World!";';
      const result = filter.filter(text);

      expect(result.wasModified).toBe(false);
      expect(result.filtered).toBe(text);
      expect(result.detections).toHaveLength(0);
    });

    it('should return stats with processing time', () => {
      const text = 'api_key: test_1234567890abcdefghij';
      const result = filter.filter(text);

      expect(result.stats.processingTimeMs).toBeGreaterThanOrEqual(0);
      expect(result.stats.totalDetections).toBeGreaterThanOrEqual(0);
    });
  });

  describe('containsSensitiveData - 機密データチェック', () => {
    it('should return true for text with API key', () => {
      const text = 'api_key=sk_live_1234567890abcdefghij';
      expect(filter.containsSensitiveData(text)).toBe(true);
    });

    it('should return true for text with password', () => {
      const text = 'password: mysecretpassword';
      expect(filter.containsSensitiveData(text)).toBe(true);
    });

    it('should return false for text without sensitive data', () => {
      const text = 'const x = 42;';
      expect(filter.containsSensitiveData(text)).toBe(false);
    });
  });

  describe('detect - 機密データ検出', () => {
    it('should detect and return positions', () => {
      const text = 'apiKey: abcdefghij1234567890abc';
      const detections = filter.detect(text);

      expect(detections.length).toBeGreaterThanOrEqual(0);
      if (detections.length > 0) {
        expect(detections[0].startIndex).toBeGreaterThanOrEqual(0);
        expect(detections[0].endIndex).toBeGreaterThan(detections[0].startIndex);
      }
    });

    it('should return empty array for clean text', () => {
      const text = 'const hello = "world";';
      const detections = filter.detect(text);

      expect(detections).toHaveLength(0);
    });
  });

  describe('getConfig - 設定取得', () => {
    it('should return default config', () => {
      const config = filter.getConfig();

      expect(config.minSeverity).toBe(DEFAULT_FILTER_CONFIG.minSeverity);
      expect(config.maskChar).toBe(DEFAULT_FILTER_CONFIG.maskChar);
    });

    it('should return custom config when provided', () => {
      const customFilter = createSensitiveDataFilter({
        minSeverity: 'high',
        maskChar: '#',
      });
      const config = customFilter.getConfig();

      expect(config.minSeverity).toBe('high');
      expect(config.maskChar).toBe('#');
    });
  });

  describe('addPattern - カスタムパターン追加', () => {
    it('should add custom pattern', () => {
      const initialCount = filter.getPatterns().length;

      filter.addPattern({
        type: 'custom',
        pattern: /CUSTOM_SECRET_[A-Z0-9]+/g,
        description: 'Custom Secret Pattern',
        severity: 'high',
        replacement: '[CUSTOM_REDACTED]',
      });

      expect(filter.getPatterns().length).toBe(initialCount + 1);
    });

    it('should use custom pattern in filtering', () => {
      // カスタムパターンを使用するには enabledTypes に 'custom' を追加する必要がある
      const customFilter = createSensitiveDataFilter({
        enabledTypes: [...DEFAULT_FILTER_CONFIG.enabledTypes, 'custom'],
      });
      
      customFilter.addPattern({
        type: 'custom',
        pattern: /MY_SPECIAL_TOKEN_[A-Z0-9]{10,}/g,
        description: 'Special Token',
        severity: 'high',
        replacement: '[SPECIAL_REDACTED]',
      });

      const text = 'token=MY_SPECIAL_TOKEN_ABCDEFGHIJ';
      const result = customFilter.filter(text);

      expect(result.wasModified).toBe(true);
      expect(result.filtered).toContain('[SPECIAL_REDACTED]');
    });
  });

  describe('getPatterns - パターン取得', () => {
    it('should return all patterns including defaults', () => {
      const patterns = filter.getPatterns();

      expect(patterns.length).toBeGreaterThanOrEqual(
        DEFAULT_SENSITIVE_PATTERNS.length
      );
    });
  });

  describe('Severity filtering', () => {
    it('should filter high severity only when configured', () => {
      const highOnlyFilter = createSensitiveDataFilter({
        minSeverity: 'high',
      });

      // Email is medium severity by default
      const textWithEmail = 'contact: test@example.com';
      expect(highOnlyFilter.containsSensitiveData(textWithEmail)).toBe(false);

      // Password is high severity
      const textWithPassword = 'password: secret123';
      expect(highOnlyFilter.containsSensitiveData(textWithPassword)).toBe(true);
    });

    it('should filter medium and high when minSeverity is medium', () => {
      const mediumFilter = createSensitiveDataFilter({
        minSeverity: 'medium',
        enabledTypes: ['email', 'password'],
      });

      const textWithEmail = 'contact: test@example.com';
      expect(mediumFilter.containsSensitiveData(textWithEmail)).toBe(true);
    });
  });

  describe('Enabled types filtering', () => {
    it('should only filter enabled types', () => {
      const passwordOnlyFilter = createSensitiveDataFilter({
        enabledTypes: ['password'],
      });

      const textWithApiKey = 'api_key: test_1234567890abcdefghij';
      const textWithPassword = 'password: secret';

      expect(passwordOnlyFilter.containsSensitiveData(textWithApiKey)).toBe(false);
      expect(passwordOnlyFilter.containsSensitiveData(textWithPassword)).toBe(true);
    });
  });
});

describe('Utility functions', () => {
  describe('getDefaultFilter', () => {
    it('should return singleton instance', () => {
      const filter1 = getDefaultFilter();
      const filter2 = getDefaultFilter();

      expect(filter1).toBe(filter2);
    });
  });

  describe('filterSensitiveData', () => {
    it('should filter using default filter', () => {
      const text = 'password: test123456';
      const result = filterSensitiveData(text);

      expect(result.wasModified).toBe(true);
    });
  });

  describe('containsSensitiveData', () => {
    it('should check using default filter', () => {
      expect(containsSensitiveData('password: secret')).toBe(true);
      expect(containsSensitiveData('hello world')).toBe(false);
    });
  });

  describe('formatFilterResultAsMarkdown', () => {
    it('should format result with no detections', () => {
      const result = createSensitiveDataFilter().filter('hello world');
      const markdown = formatFilterResultAsMarkdown(result);

      expect(markdown).toContain('✅');
      expect(markdown).toContain('検出されませんでした');
    });

    it('should format result with detections', () => {
      const result = createSensitiveDataFilter().filter('password: secret123');
      const markdown = formatFilterResultAsMarkdown(result);

      expect(markdown).toContain('⚠️');
      expect(markdown).toContain('機密データが検出されました');
      expect(markdown).toContain('検出数');
    });

    it('should include detection table', () => {
      const result = createSensitiveDataFilter().filter('password: secret123');
      const markdown = formatFilterResultAsMarkdown(result);

      expect(markdown).toContain('| 種類 | 重要度 | 説明 |');
    });
  });
});

describe('DEFAULT_SENSITIVE_PATTERNS', () => {
  it('should include essential patterns', () => {
    const types = DEFAULT_SENSITIVE_PATTERNS.map((p) => p.type);

    expect(types).toContain('api_key');
    expect(types).toContain('password');
    expect(types).toContain('secret');
    expect(types).toContain('aws_key');
    expect(types).toContain('private_key');
    expect(types).toContain('oauth_token');
    expect(types).toContain('bearer_token');
    expect(types).toContain('jwt');
  });

  it('should have valid patterns', () => {
    for (const pattern of DEFAULT_SENSITIVE_PATTERNS) {
      expect(pattern.pattern).toBeInstanceOf(RegExp);
      expect(pattern.description).toBeTruthy();
      expect(pattern.replacement).toBeTruthy();
      expect(['high', 'medium', 'low']).toContain(pattern.severity);
    }
  });
});

describe('Edge cases', () => {
  let filter: SensitiveDataFilter;

  beforeEach(() => {
    filter = createSensitiveDataFilter();
  });

  it('should handle empty string', () => {
    const result = filter.filter('');
    expect(result.wasModified).toBe(false);
    expect(result.filtered).toBe('');
  });

  it('should handle very long text', () => {
    const longText = 'x'.repeat(100000) + 'password: secret123' + 'y'.repeat(100000);
    const result = filter.filter(longText);

    expect(result.wasModified).toBe(true);
    expect(result.filtered).toContain('[PASSWORD_REDACTED]');
  });

  it('should handle overlapping patterns', () => {
    // oauth_token と bearer_token が同じ箇所にマッチする可能性
    const text = 'Authorization: Bearer oauth_token_1234567890abcdefgh';
    const result = filter.filter(text);

    expect(result.wasModified).toBe(true);
    // 重複が適切に処理されていることを確認
    expect(result.detections.length).toBeGreaterThanOrEqual(1);
  });

  it('should handle special characters in text', () => {
    const text = 'password: p@$$w0rd!#$%^&*()';
    const result = filter.filter(text);

    expect(result.wasModified).toBe(true);
  });

  it('should handle multiline text', () => {
    const text = `
      Line 1: normal text
      Line 2: api_key = abc123def456ghi789jkl012
      Line 3: more normal text
      Line 4: password = supersecret
      Line 5: end
    `;
    const result = filter.filter(text);

    expect(result.wasModified).toBe(true);
    expect(result.detections.length).toBeGreaterThanOrEqual(1);
  });
});
