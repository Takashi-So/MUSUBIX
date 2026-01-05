/**
 * Pattern Sharing Module
 *
 * @module learning/sharing
 * @description Phase 2: パターン共有機能のエクスポート
 * @requirements REQ-SHARE-001, REQ-SHARE-002, REQ-SHARE-003, REQ-SHARE-004, REQ-SHARE-005, REQ-SHARE-006
 */

// Types
export type {
  ExportOptions,
  ImportOptions,
  ExportResult,
  ImportResult,
  ValidationResult,
  ValidationError as SharingValidationError,
  ValidationWarning as SharingValidationWarning,
  SharedPattern,
  PatternContext,
  PatternMetadata,
  Conflict,
  ConflictStrategy,
  Resolution,
  SanitizeConfig,
  PatternRepository,
  ServerConfig,
  CorsConfig,
  RateLimitConfig,
  AuthToken,
  AuthScope,
  AuthRequest,
  AuthResult,
} from './types.js';

// Serialization
export { PatternSerializer } from './pattern-serializer.js';
export { PatternDeserializer } from './pattern-deserializer.js';

// Server
export { PatternServer, type ServerEvents } from './pattern-server.js';

// Conflict Resolution
export { ConflictResolver, type ConflictPromptCallback, type ResolverOptions } from './conflict-resolver.js';

// Authentication
export { AuthManager, type User, type ApiKey, type AuthManagerOptions } from './auth-manager.js';
