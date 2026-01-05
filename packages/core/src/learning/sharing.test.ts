/**
 * Pattern Sharing Tests
 *
 * @description Phase 2: Pattern Sharing 機能のテスト
 * @requirements REQ-SHARE-001, REQ-SHARE-002, REQ-SHARE-003, REQ-SHARE-004, REQ-SHARE-005, REQ-SHARE-006
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import {
  PatternSerializer,
  PatternDeserializer,
  PatternServer,
  ConflictResolver,
  AuthManager,
  type SharedPattern,
} from './index.js';

/**
 * Input pattern type for serializer (simplified SharedPattern)
 */
interface InputPattern {
  id: string;
  name: string;
  confidence: number;
  usageCount?: number;
  template?: string;
  description?: string;
}

// =============================================================================
// PatternSerializer Tests
// =============================================================================

describe('PatternSerializer', () => {
  let serializer: PatternSerializer;

  beforeEach(() => {
    serializer = new PatternSerializer({ version: '1.0.0' });
  });

  describe('export()', () => {
    it('should export patterns to JSON format', () => {
      const patterns: InputPattern[] = [
        {
          id: 'PTN-001',
          name: 'Factory Pattern',
          confidence: 0.95,
          usageCount: 10,
          template: 'function create${Name}() { return new ${Name}(); }',
          description: 'Factory function pattern',
        },
      ];

      const result = serializer.export(patterns, { format: 'json', sanitize: false });

      expect(result.format).toBe('json');
      expect(result.patternCount).toBe(1);
      expect(result.size).toBeGreaterThan(0);
      expect(result.checksum).toBeDefined();

      const parsed = JSON.parse(result.data);
      expect(parsed.patterns).toHaveLength(1);
      expect(parsed.patterns[0].name).toBe('Factory Pattern');
    });

    it('should export patterns to N3 format', () => {
      const patterns: InputPattern[] = [
        {
          id: 'PTN-002',
          name: 'Repository Pattern',
          confidence: 0.9,
          usageCount: 5,
        },
      ];

      const result = serializer.export(patterns, { format: 'n3', sanitize: false });

      expect(result.format).toBe('n3');
      expect(result.data).toContain('@prefix musubix:');
      expect(result.data).toContain('Repository Pattern');
    });

    it('should sanitize sensitive data when enabled', () => {
      const patterns: InputPattern[] = [
        {
          id: 'PTN-003',
          name: 'Test Pattern',
          confidence: 0.8,
          template: 'const path = "/home/user/secret/file.ts"',
          description: 'Contains /home/nahisaho/private path',
        },
      ];

      const result = serializer.export(patterns, { format: 'json', sanitize: true });
      const parsed = JSON.parse(result.data);

      expect(parsed.patterns[0].template).toContain('[REDACTED]');
      expect(parsed.patterns[0].description).toContain('[REDACTED]');
    });

    it('should include version when specified', () => {
      const patterns: InputPattern[] = [
        { id: 'PTN-004', name: 'Test', confidence: 0.5 },
      ];

      const result = serializer.export(patterns, {
        format: 'json',
        sanitize: false,
        includeVersion: true,
      });

      const parsed = JSON.parse(result.data);
      expect(parsed.version).toBe('1.0.0');
    });

    it('should calculate valid checksum', () => {
      const patterns: InputPattern[] = [
        { id: 'PTN-005', name: 'Checksum Test', confidence: 0.7 },
      ];

      const result = serializer.export(patterns, { format: 'json', sanitize: false });

      expect(serializer.verifyChecksum(result.data, result.checksum)).toBe(true);
      expect(serializer.verifyChecksum(result.data + 'modified', result.checksum)).toBe(false);
    });
  });

  describe('sanitize()', () => {
    it('should remove email addresses', () => {
      const pattern: SharedPattern = {
        id: 'PTN-006',
        name: 'Email Test',
        category: 'code',
        description: 'Contact: test@example.com',
        confidence: 0.8,
        usageCount: 0,
        metadata: { source: 'local' },
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: 1,
      };

      const sanitized = serializer.sanitize(pattern);
      expect(sanitized.description).toContain('[REDACTED]');
      expect(sanitized.description).not.toContain('test@example.com');
    });

    it('should remove IP addresses', () => {
      const pattern: SharedPattern = {
        id: 'PTN-007',
        name: 'IP Test',
        category: 'code',
        description: 'Server: 192.168.1.100',
        confidence: 0.8,
        usageCount: 0,
        metadata: { source: 'local' },
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: 1,
      };

      const sanitized = serializer.sanitize(pattern);
      expect(sanitized.description).not.toContain('192.168.1.100');
    });
  });
});

// =============================================================================
// PatternDeserializer Tests
// =============================================================================

describe('PatternDeserializer', () => {
  let deserializer: PatternDeserializer;

  beforeEach(() => {
    deserializer = new PatternDeserializer();
  });

  describe('import()', () => {
    it('should import valid JSON data', async () => {
      const data = JSON.stringify({
        version: '1.0.0',
        exportedAt: new Date().toISOString(),
        patternCount: 1,
        patterns: [
          {
            id: 'PTN-001',
            name: 'Test Pattern',
            category: 'code',
            description: 'Test description',
            confidence: 0.8,
            usageCount: 5,
            createdAt: new Date().toISOString(),
            updatedAt: new Date().toISOString(),
            version: 1,
          },
        ],
      });

      const result = await deserializer.import(data);

      expect(result.success).toBe(true);
      expect(result.importedCount).toBe(1);
      expect(result.patterns[0].name).toBe('Test Pattern');
      expect(result.patterns[0].metadata.source).toBe('imported');
    });

    it('should handle invalid JSON', async () => {
      const result = await deserializer.import('invalid json {{{');

      expect(result.success).toBe(false);
      expect(result.errors).toHaveLength(1);
      expect(result.errors[0]).toContain('Parse error');
    });

    it('should skip validation when specified', async () => {
      const data = JSON.stringify({
        patterns: [{ name: 'Minimal', confidence: 0.5 }],
      });

      const result = await deserializer.import(data, { skipValidation: true });

      expect(result.success).toBe(true);
    });

    it('should import Base64 encoded data', async () => {
      // isBase64 requires length > 100, so we need more data
      const original = JSON.stringify({
        patterns: [
          { 
            id: 'PTN-B64', 
            name: 'Base64 Pattern', 
            confidence: 0.7,
            description: 'This is a longer description to make the Base64 string long enough for detection',
            category: 'code',
          },
        ],
        version: '1.0.0',
        exportedAt: new Date().toISOString(),
      });
      const encoded = Buffer.from(original).toString('base64');

      const result = await deserializer.import(encoded);

      expect(result.success).toBe(true);
      expect(result.patterns[0].name).toBe('Base64 Pattern');
    });
  });

  describe('validate()', () => {
    it('should validate correct data structure', () => {
      const data = JSON.stringify({
        patterns: [
          { id: 'PTN-001', name: 'Valid', confidence: 0.8 },
        ],
      });

      const result = deserializer.validate(data);

      expect(result.valid).toBe(true);
      expect(result.errors).toHaveLength(0);
    });

    it('should detect missing patterns array', () => {
      const data = JSON.stringify({ version: '1.0.0' });

      const result = deserializer.validate(data);

      expect(result.valid).toBe(false);
      expect(result.errors.some(e => e.code === 'INVALID_STRUCTURE')).toBe(true);
    });

    it('should detect missing required fields', () => {
      const data = JSON.stringify({
        patterns: [{ id: 'PTN-001' }], // missing name and confidence
      });

      const result = deserializer.validate(data);

      expect(result.valid).toBe(false);
      expect(result.errors.some(e => e.code === 'MISSING_NAME')).toBe(true);
      expect(result.errors.some(e => e.code === 'MISSING_CONFIDENCE')).toBe(true);
    });

    it('should detect invalid confidence range', () => {
      const data = JSON.stringify({
        patterns: [{ name: 'Test', confidence: 1.5 }], // > 1
      });

      const result = deserializer.validate(data);

      expect(result.valid).toBe(false);
      expect(result.errors.some(e => e.code === 'INVALID_CONFIDENCE')).toBe(true);
    });

    it('should detect duplicate IDs', () => {
      const data = JSON.stringify({
        patterns: [
          { id: 'PTN-DUP', name: 'First', confidence: 0.8 },
          { id: 'PTN-DUP', name: 'Second', confidence: 0.7 },
        ],
      });

      const result = deserializer.validate(data);

      expect(result.valid).toBe(false);
      expect(result.errors.some(e => e.code === 'DUPLICATE_IDS')).toBe(true);
    });

    it('should warn about unknown category', () => {
      const data = JSON.stringify({
        patterns: [{ name: 'Test', confidence: 0.8, category: 'unknown' }],
      });

      const result = deserializer.validate(data);

      expect(result.valid).toBe(true); // Warning only
      expect(result.warnings.some(w => w.code === 'UNKNOWN_CATEGORY')).toBe(true);
    });
  });
});

// =============================================================================
// ConflictResolver Tests
// =============================================================================

describe('ConflictResolver', () => {
  let resolver: ConflictResolver;

  const createPattern = (overrides: Partial<SharedPattern> = {}): SharedPattern => ({
    id: 'PTN-001',
    name: 'Test Pattern',
    category: 'code',
    description: 'Test',
    confidence: 0.8,
    usageCount: 5,
    metadata: { source: 'local' },
    createdAt: new Date().toISOString(),
    updatedAt: new Date().toISOString(),
    version: 1,
    ...overrides,
  });

  beforeEach(() => {
    resolver = new ConflictResolver();
  });

  describe('detectConflicts()', () => {
    it('should detect ID conflicts', () => {
      const local = createPattern({ id: 'PTN-001', name: 'Local' });
      const remote = createPattern({ id: 'PTN-001', name: 'Remote' });

      resolver.setLocalPatterns([local]);
      const conflicts = resolver.detectConflicts([remote]);

      expect(conflicts).toHaveLength(1);
      expect(conflicts[0].type).toBe('id');
    });

    it('should detect name conflicts', () => {
      const local = createPattern({ id: 'PTN-001', name: 'Same Name', confidence: 0.8 });
      const remote = createPattern({ id: 'PTN-002', name: 'Same Name', confidence: 0.9 });

      resolver.setLocalPatterns([local]);
      const conflicts = resolver.detectConflicts([remote]);

      expect(conflicts).toHaveLength(1);
      expect(conflicts[0].type).toBe('name');
    });

    it('should detect content conflicts (similar templates)', () => {
      const local = createPattern({
        id: 'PTN-001',
        name: 'Local Pattern',
        template: 'function createUser() { return new User(); }',
      });
      const remote = createPattern({
        id: 'PTN-002',
        name: 'Remote Pattern',
        template: 'function createUser() { return new User(); }',
      });

      resolver.setLocalPatterns([local]);
      const conflicts = resolver.detectConflicts([remote]);

      expect(conflicts).toHaveLength(1);
      expect(conflicts[0].type).toBe('content');
    });

    it('should not detect conflict for identical patterns', () => {
      const local = createPattern();
      const remote = createPattern();

      resolver.setLocalPatterns([local]);
      const conflicts = resolver.detectConflicts([remote]);

      expect(conflicts).toHaveLength(0);
    });
  });

  describe('resolve()', () => {
    it('should keep local pattern with keep-local strategy', async () => {
      resolver.setStrategy('keep-local');

      const conflict = {
        type: 'id' as const,
        localPattern: createPattern({ name: 'Local' }),
        remotePattern: createPattern({ name: 'Remote' }),
        details: 'ID conflict',
      };

      const result = await resolver.resolve([conflict]);

      expect(result.resolvedCount).toBe(1);
      expect(result.resolvedPatterns[0].name).toBe('Local');
    });

    it('should keep remote pattern with keep-remote strategy', async () => {
      resolver.setStrategy('keep-remote');

      const conflict = {
        type: 'id' as const,
        localPattern: createPattern({ name: 'Local' }),
        remotePattern: createPattern({ name: 'Remote' }),
        details: 'ID conflict',
      };

      const result = await resolver.resolve([conflict]);

      expect(result.resolvedCount).toBe(1);
      expect(result.resolvedPatterns[0].name).toBe('Remote');
    });

    it('should merge patterns with merge strategy', async () => {
      resolver.setStrategy('merge');

      const conflict = {
        type: 'id' as const,
        localPattern: createPattern({ confidence: 0.7, usageCount: 3 }),
        remotePattern: createPattern({ confidence: 0.9, usageCount: 5 }),
        details: 'ID conflict',
      };

      const result = await resolver.resolve([conflict]);

      expect(result.resolvedCount).toBe(1);
      expect(result.resolvedPatterns[0].confidence).toBe(0.9); // Max
      expect(result.resolvedPatterns[0].usageCount).toBe(8); // Sum
    });

    it('should skip conflicts with skip strategy', async () => {
      resolver.setStrategy('skip');

      const conflict = {
        type: 'id' as const,
        localPattern: createPattern(),
        remotePattern: createPattern(),
        details: 'ID conflict',
      };

      const result = await resolver.resolve([conflict]);

      expect(result.resolvedCount).toBe(0);
      expect(result.pendingConflicts).toHaveLength(1);
    });

    it('should use prompt callback when strategy is prompt', async () => {
      resolver.setStrategy('prompt');
      resolver.setPromptCallback(async () => 'keep-remote');

      const conflict = {
        type: 'id' as const,
        localPattern: createPattern({ name: 'Local' }),
        remotePattern: createPattern({ name: 'Remote' }),
        details: 'ID conflict',
      };

      const result = await resolver.resolve([conflict]);

      expect(result.resolvedCount).toBe(1);
      expect(result.resolvedPatterns[0].name).toBe('Remote');
    });
  });
});

// =============================================================================
// AuthManager Tests
// =============================================================================

describe('AuthManager', () => {
  let authManager: AuthManager;

  beforeEach(() => {
    authManager = new AuthManager({ tokenTTL: 1000 }); // Short TTL for testing
  });

  afterEach(() => {
    authManager.clearAll();
  });

  describe('createUser()', () => {
    it('should create a user successfully', () => {
      const user = authManager.createUser('testuser', 'password123', ['read', 'write']);

      expect(user.username).toBe('testuser');
      expect(user.allowedScopes).toContain('read');
      expect(user.allowedScopes).toContain('write');
      expect(user.active).toBe(true);
      expect(user.passwordHash).toBe('[HIDDEN]'); // Should be hidden
    });

    it('should hash password with salt', () => {
      const user1 = authManager.createUser('user1', 'samepass');
      const user2 = authManager.createUser('user2', 'samepass');

      // Both should have hidden hashes
      expect(user1.passwordHash).toBe('[HIDDEN]');
      expect(user2.passwordHash).toBe('[HIDDEN]');
    });
  });

  describe('authenticate()', () => {
    it('should authenticate valid user credentials', () => {
      authManager.createUser('testuser', 'password123', ['read']);

      const result = authManager.authenticate({
        credentials: 'testuser',
        secret: 'password123',
        scopes: ['read'],
      });

      expect(result.success).toBe(true);
      expect(result.token).toBeDefined();
      expect(result.token?.scopes).toContain('read');
    });

    it('should reject invalid password', () => {
      authManager.createUser('testuser', 'password123');

      const result = authManager.authenticate({
        credentials: 'testuser',
        secret: 'wrongpassword',
      });

      expect(result.success).toBe(false);
      expect(result.error).toBe('Invalid credentials');
    });

    it('should reject inactive user', () => {
      const user = authManager.createUser('testuser', 'password123');
      authManager.deactivateUser(user.id);

      const result = authManager.authenticate({
        credentials: 'testuser',
        secret: 'password123',
      });

      expect(result.success).toBe(false);
      expect(result.error).toBe('User is inactive');
    });

    it('should only grant allowed scopes', () => {
      authManager.createUser('testuser', 'password123', ['read']);

      const result = authManager.authenticate({
        credentials: 'testuser',
        secret: 'password123',
        scopes: ['read', 'write', 'admin'],
      });

      expect(result.success).toBe(true);
      expect(result.token?.scopes).toContain('read');
      expect(result.token?.scopes).not.toContain('write');
      expect(result.token?.scopes).not.toContain('admin');
    });
  });

  describe('createApiKey()', () => {
    it('should create an API key', () => {
      const { apiKey, key } = authManager.createApiKey('Test Key', ['read']);

      expect(apiKey.name).toBe('Test Key');
      expect(apiKey.scopes).toContain('read');
      expect(key).toMatch(/^msbx_/);
    });

    it('should authenticate with API key', () => {
      const { key } = authManager.createApiKey('Test Key', ['read', 'write']);

      const result = authManager.authenticate({ credentials: key });

      expect(result.success).toBe(true);
      expect(result.token?.scopes).toContain('read');
      expect(result.token?.scopes).toContain('write');
    });
  });

  describe('validateToken()', () => {
    it('should validate a valid token', () => {
      authManager.createUser('testuser', 'password123');
      const authResult = authManager.authenticate({
        credentials: 'testuser',
        secret: 'password123',
      });

      const token = authManager.validateToken(authResult.token!.token);

      expect(token).not.toBeNull();
    });

    it('should reject expired token', async () => {
      authManager.createUser('testuser', 'password123');
      const authResult = authManager.authenticate({
        credentials: 'testuser',
        secret: 'password123',
      });

      // Wait for token to expire
      await new Promise(resolve => setTimeout(resolve, 1100));

      const token = authManager.validateToken(authResult.token!.token);

      expect(token).toBeNull();
    });
  });

  describe('checkScope()', () => {
    it('should return true for valid scope', () => {
      authManager.createUser('testuser', 'password123', ['read', 'write']);
      const authResult = authManager.authenticate({
        credentials: 'testuser',
        secret: 'password123',
        scopes: ['read', 'write'],
      });

      expect(authManager.checkScope(authResult.token!.token, 'read')).toBe(true);
      expect(authManager.checkScope(authResult.token!.token, 'write')).toBe(true);
    });

    it('should allow admin scope to access everything', () => {
      authManager.createUser('admin', 'password123', ['admin']);
      const authResult = authManager.authenticate({
        credentials: 'admin',
        secret: 'password123',
        scopes: ['admin'],
      });

      expect(authManager.checkScope(authResult.token!.token, 'read')).toBe(true);
      expect(authManager.checkScope(authResult.token!.token, 'write')).toBe(true);
      expect(authManager.checkScope(authResult.token!.token, 'admin')).toBe(true);
    });
  });

  describe('revokeToken()', () => {
    it('should revoke a token', () => {
      authManager.createUser('testuser', 'password123');
      const authResult = authManager.authenticate({
        credentials: 'testuser',
        secret: 'password123',
      });

      const revoked = authManager.revokeToken(authResult.token!.token);
      const token = authManager.validateToken(authResult.token!.token);

      expect(revoked).toBe(true);
      expect(token).toBeNull();
    });
  });
});

// =============================================================================
// PatternServer Tests
// =============================================================================

describe('PatternServer', () => {
  let server: PatternServer;
  const testPort = 13456;

  beforeEach(() => {
    server = new PatternServer({ port: testPort, host: 'localhost' });
  });

  afterEach(async () => {
    if (server.isRunning()) {
      await server.stop();
    }
  });

  describe('start/stop', () => {
    it('should start and stop server', async () => {
      await server.start();
      expect(server.isRunning()).toBe(true);

      await server.stop();
      expect(server.isRunning()).toBe(false);
    });

    it('should throw when starting already running server', async () => {
      await server.start();

      await expect(server.start()).rejects.toThrow('Server is already running');
    });

    it('should emit start event', async () => {
      const startHandler = vi.fn();
      server.on('start', startHandler);

      await server.start();

      expect(startHandler).toHaveBeenCalledWith({
        port: testPort,
        host: 'localhost',
      });
    });
  });

  describe('pattern management', () => {
    it('should add and get patterns', () => {
      const pattern: SharedPattern = {
        id: 'PTN-001',
        name: 'Test Pattern',
        category: 'code',
        description: 'Test',
        confidence: 0.8,
        usageCount: 0,
        metadata: { source: 'local' },
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: 1,
      };

      server.addPattern(pattern);

      expect(server.getPattern('PTN-001')).toEqual(pattern);
      expect(server.getPatternCount()).toBe(1);
    });

    it('should clear patterns', () => {
      const pattern: SharedPattern = {
        id: 'PTN-001',
        name: 'Test',
        category: 'code',
        description: '',
        confidence: 0.8,
        usageCount: 0,
        metadata: { source: 'local' },
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: 1,
      };

      server.addPattern(pattern);
      server.clearPatterns();

      expect(server.getPatternCount()).toBe(0);
    });
  });

  describe('token management', () => {
    it('should register and revoke tokens', () => {
      const token = {
        token: 'test-token',
        expiresAt: new Date(Date.now() + 10000).toISOString(),
        scopes: ['read' as const],
      };

      server.registerToken(token);
      server.revokeToken('test-token');

      // Token should be removed (we can't directly check, but no errors)
    });
  });

  describe('configuration', () => {
    it('should return server config', () => {
      const config = server.getConfig();

      expect(config.port).toBe(testPort);
      expect(config.host).toBe('localhost');
    });

    it('should return address when running', async () => {
      expect(server.getAddress()).toBeNull();

      await server.start();
      const address = server.getAddress();

      expect(address?.port).toBe(testPort);
      expect(address?.host).toBe('localhost');
    });
  });
});

// =============================================================================
// Integration Tests
// =============================================================================

describe('Pattern Sharing Integration', () => {
  it('should export and import patterns round-trip', async () => {
    const serializer = new PatternSerializer();
    const deserializer = new PatternDeserializer();

    // Create test patterns
    const patterns: InputPattern[] = [
      {
        id: 'PTN-001',
        name: 'Factory Pattern',
        confidence: 0.95,
        usageCount: 10,
        template: 'function create() {}',
        description: 'Factory function',
      },
      {
        id: 'PTN-002',
        name: 'Repository Pattern',
        confidence: 0.9,
        usageCount: 5,
        template: 'class Repository {}',
        description: 'Repository class',
      },
    ];

    // Export
    const exportResult = serializer.export(patterns, { format: 'json', sanitize: false });
    expect(exportResult.patternCount).toBe(2);

    // Import
    const importResult = await deserializer.import(exportResult.data);
    expect(importResult.success).toBe(true);
    expect(importResult.importedCount).toBe(2);

    // Verify patterns
    expect(importResult.patterns[0].name).toBe('Factory Pattern');
    expect(importResult.patterns[1].name).toBe('Repository Pattern');
  });

  it('should handle conflict detection and resolution', async () => {
    const resolver = new ConflictResolver({ defaultStrategy: 'merge' });

    const localPatterns: SharedPattern[] = [
      {
        id: 'PTN-001',
        name: 'Shared Pattern',
        category: 'code',
        description: 'Local version',
        confidence: 0.7,
        usageCount: 3,
        metadata: { source: 'local' },
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: 1,
      },
    ];

    const remotePatterns: SharedPattern[] = [
      {
        id: 'PTN-001',
        name: 'Shared Pattern',
        category: 'code',
        description: 'Remote version',
        confidence: 0.9,
        usageCount: 5,
        metadata: { source: 'imported' },
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: 2,
      },
    ];

    resolver.setLocalPatterns(localPatterns);
    const conflicts = resolver.detectConflicts(remotePatterns);

    expect(conflicts).toHaveLength(1);

    const resolution = await resolver.resolve(conflicts);

    expect(resolution.resolvedCount).toBe(1);
    expect(resolution.resolvedPatterns[0].confidence).toBe(0.9);
    expect(resolution.resolvedPatterns[0].usageCount).toBe(8);
  });
});
