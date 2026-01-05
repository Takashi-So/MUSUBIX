// Tests for Authentication
// REQ-AUTH-001, REQ-AUTH-002

import { describe, it, expect } from 'vitest';
import {
  createApiKey,
  isApiKeyValid,
  parseJwt,
  isJwtExpired,
  isValidIssuer,
  getJwtRoles,
} from '../src/domain/auth.js';

describe('Auth', () => {
  describe('createApiKey', () => {
    const validKey = 'a'.repeat(32);

    it('should create API key with valid input', () => {
      const apiKey = createApiKey(validKey, 'client-1', 'Test Key');

      expect(apiKey.key).toBe(validKey);
      expect(apiKey.clientId).toBe('client-1');
      expect(apiKey.name).toBe('Test Key');
      expect(apiKey.tier).toBe('free');
      expect(apiKey.active).toBe(true);
    });

    it('should create API key with custom tier', () => {
      const apiKey = createApiKey(validKey, 'client-1', 'Test Key', {
        tier: 'premium',
        roles: ['admin'],
      });

      expect(apiKey.tier).toBe('premium');
      expect(apiKey.roles).toEqual(['admin']);
    });

    it('should throw for short key', () => {
      expect(() => createApiKey('short', 'client-1', 'Test')).toThrow(
        'at least 32 characters'
      );
    });

    it('should throw for missing client ID', () => {
      expect(() => createApiKey(validKey, '', 'Test')).toThrow('Client ID is required');
    });

    it('should throw for missing name', () => {
      expect(() => createApiKey(validKey, 'client-1', '')).toThrow('Name is required');
    });
  });

  describe('isApiKeyValid', () => {
    const validKey = 'a'.repeat(32);

    it('should return true for active key', () => {
      const apiKey = createApiKey(validKey, 'client-1', 'Test');
      expect(isApiKeyValid(apiKey)).toBe(true);
    });

    it('should return false for inactive key', () => {
      const apiKey = createApiKey(validKey, 'client-1', 'Test');
      apiKey.active = false;
      expect(isApiKeyValid(apiKey)).toBe(false);
    });

    it('should return false for expired key', () => {
      const apiKey = createApiKey(validKey, 'client-1', 'Test', {
        expiresAt: new Date(Date.now() - 1000),
      });
      expect(isApiKeyValid(apiKey)).toBe(false);
    });

    it('should return true for key with future expiry', () => {
      const apiKey = createApiKey(validKey, 'client-1', 'Test', {
        expiresAt: new Date(Date.now() + 86400000),
      });
      expect(isApiKeyValid(apiKey)).toBe(true);
    });
  });

  describe('parseJwt', () => {
    // Create a simple JWT-like token for testing
    function createTestToken(
      payload: Record<string, unknown>,
      header = { alg: 'HS256', typ: 'JWT' }
    ): string {
      const headerB64 = btoa(JSON.stringify(header));
      const payloadB64 = btoa(JSON.stringify(payload));
      const signature = 'test-signature';
      return `${headerB64}.${payloadB64}.${signature}`;
    }

    it('should parse valid JWT', () => {
      const token = createTestToken({
        sub: 'user-123',
        iss: 'https://auth.example.com',
        exp: Math.floor(Date.now() / 1000) + 3600,
        iat: Math.floor(Date.now() / 1000),
        roles: ['admin'],
      });

      const result = parseJwt(token);

      expect(result.valid).toBe(true);
      if (result.valid) {
        expect(result.token.payload.sub).toBe('user-123');
        expect(result.token.payload.roles).toEqual(['admin']);
      }
    });

    it('should reject invalid format', () => {
      const result = parseJwt('invalid-token');

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('expected 3 parts');
      }
    });

    it('should reject missing sub claim', () => {
      const token = createTestToken({
        iss: 'https://auth.example.com',
        exp: Math.floor(Date.now() / 1000) + 3600,
      });

      const result = parseJwt(token);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('sub');
      }
    });

    it('should reject missing iss claim', () => {
      const token = createTestToken({
        sub: 'user-123',
        exp: Math.floor(Date.now() / 1000) + 3600,
      });

      const result = parseJwt(token);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('iss');
      }
    });

    it('should reject missing exp claim', () => {
      const token = createTestToken({
        sub: 'user-123',
        iss: 'https://auth.example.com',
      });

      const result = parseJwt(token);

      expect(result.valid).toBe(false);
      if (!result.valid) {
        expect(result.error).toContain('exp');
      }
    });
  });

  describe('isJwtExpired', () => {
    it('should return false for valid token', () => {
      const token = {
        header: { alg: 'HS256', typ: 'JWT' },
        payload: {
          sub: 'user-123',
          iss: 'test',
          aud: 'test',
          exp: Math.floor(Date.now() / 1000) + 3600,
          iat: Math.floor(Date.now() / 1000),
        },
        signature: 'sig',
        raw: 'raw',
      };

      expect(isJwtExpired(token)).toBe(false);
    });

    it('should return true for expired token', () => {
      const token = {
        header: { alg: 'HS256', typ: 'JWT' },
        payload: {
          sub: 'user-123',
          iss: 'test',
          aud: 'test',
          exp: Math.floor(Date.now() / 1000) - 3600, // 1 hour ago
          iat: Math.floor(Date.now() / 1000) - 7200,
        },
        signature: 'sig',
        raw: 'raw',
      };

      expect(isJwtExpired(token)).toBe(true);
    });
  });

  describe('isValidIssuer', () => {
    const token = {
      header: { alg: 'HS256', typ: 'JWT' },
      payload: {
        sub: 'user-123',
        iss: 'https://auth.example.com',
        aud: 'test',
        exp: Math.floor(Date.now() / 1000) + 3600,
        iat: Math.floor(Date.now() / 1000),
      },
      signature: 'sig',
      raw: 'raw',
    };

    it('should return true for allowed issuer', () => {
      expect(isValidIssuer(token, ['https://auth.example.com'])).toBe(true);
    });

    it('should return false for unknown issuer', () => {
      expect(isValidIssuer(token, ['https://other.com'])).toBe(false);
    });
  });

  describe('getJwtRoles', () => {
    it('should return roles from token', () => {
      const token = {
        header: { alg: 'HS256', typ: 'JWT' },
        payload: {
          sub: 'user-123',
          iss: 'test',
          aud: 'test',
          exp: Math.floor(Date.now() / 1000) + 3600,
          iat: Math.floor(Date.now() / 1000),
          roles: ['admin', 'user'],
        },
        signature: 'sig',
        raw: 'raw',
      };

      expect(getJwtRoles(token)).toEqual(['admin', 'user']);
    });

    it('should return empty array if no roles', () => {
      const token = {
        header: { alg: 'HS256', typ: 'JWT' },
        payload: {
          sub: 'user-123',
          iss: 'test',
          aud: 'test',
          exp: Math.floor(Date.now() / 1000) + 3600,
          iat: Math.floor(Date.now() / 1000),
        },
        signature: 'sig',
        raw: 'raw',
      };

      expect(getJwtRoles(token)).toEqual([]);
    });
  });
});
