/**
 * Authentication Manager
 *
 * @module learning/sharing/auth-manager
 * @description パターン共有の認証・認可管理
 * @requirements REQ-SHARE-006
 */

import { createHash, randomBytes } from 'crypto';
import type { AuthToken, AuthScope, AuthRequest, AuthResult } from './types.js';

/**
 * ユーザー情報
 */
export interface User {
  /** ユーザーID */
  id: string;
  /** ユーザー名 */
  username: string;
  /** パスワードハッシュ */
  passwordHash: string;
  /** ソルト */
  salt: string;
  /** 許可されたスコープ */
  allowedScopes: AuthScope[];
  /** 作成日時 */
  createdAt: string;
  /** 最終ログイン */
  lastLoginAt?: string;
  /** 有効か */
  active: boolean;
}

/**
 * APIキー情報
 */
export interface ApiKey {
  /** キーID */
  id: string;
  /** キーハッシュ */
  keyHash: string;
  /** 名前 */
  name: string;
  /** 許可されたスコープ */
  scopes: AuthScope[];
  /** 作成日時 */
  createdAt: string;
  /** 有効期限 */
  expiresAt?: string;
  /** 最終使用日時 */
  lastUsedAt?: string;
  /** 有効か */
  active: boolean;
}

/**
 * 認証マネージャーオプション
 */
export interface AuthManagerOptions {
  /** トークン有効期限（ミリ秒） */
  tokenTTL: number;
  /** APIキー有効期限（ミリ秒） */
  apiKeyTTL: number;
  /** ハッシュイテレーション */
  hashIterations: number;
}

/**
 * デフォルトオプション
 */
const DEFAULT_OPTIONS: AuthManagerOptions = {
  tokenTTL: 24 * 60 * 60 * 1000, // 24時間
  apiKeyTTL: 365 * 24 * 60 * 60 * 1000, // 1年
  hashIterations: 10000,
};

/**
 * 認証マネージャー
 */
export class AuthManager {
  private options: AuthManagerOptions;
  private users: Map<string, User> = new Map();
  private apiKeys: Map<string, ApiKey> = new Map();
  private tokens: Map<string, AuthToken> = new Map();

  constructor(options: Partial<AuthManagerOptions> = {}) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
  }

  /**
   * ユーザーを作成
   */
  createUser(username: string, password: string, scopes: AuthScope[] = ['read']): User {
    const id = this.generateId('USR');
    const salt = randomBytes(32).toString('hex');
    const passwordHash = this.hashPassword(password, salt);

    const user: User = {
      id,
      username,
      passwordHash,
      salt,
      allowedScopes: scopes,
      createdAt: new Date().toISOString(),
      active: true,
    };

    this.users.set(id, user);
    return { ...user, passwordHash: '[HIDDEN]', salt: '[HIDDEN]' };
  }

  /**
   * ユーザー認証
   */
  authenticate(request: AuthRequest): AuthResult {
    // ユーザー名で検索
    const user = this.findUserByUsername(request.credentials);

    if (!user) {
      // APIキーとして試行
      return this.authenticateApiKey(request.credentials, request.scopes);
    }

    // パスワード検証
    if (!request.secret) {
      return { success: false, error: 'Password required' };
    }

    const passwordHash = this.hashPassword(request.secret, user.salt);
    if (passwordHash !== user.passwordHash) {
      return { success: false, error: 'Invalid credentials' };
    }

    if (!user.active) {
      return { success: false, error: 'User is inactive' };
    }

    // トークン生成
    const requestedScopes = request.scopes ?? ['read'];
    const grantedScopes = this.validateScopes(requestedScopes, user.allowedScopes);

    if (grantedScopes.length === 0) {
      return { success: false, error: 'No valid scopes' };
    }

    const token = this.createToken(user.id, grantedScopes);

    // 最終ログイン更新
    user.lastLoginAt = new Date().toISOString();

    return { success: true, token };
  }

  /**
   * APIキーで認証
   */
  private authenticateApiKey(key: string, requestedScopes?: AuthScope[]): AuthResult {
    const keyHash = this.hashApiKey(key);
    const apiKey = this.findApiKeyByHash(keyHash);

    if (!apiKey) {
      return { success: false, error: 'Invalid credentials' };
    }

    if (!apiKey.active) {
      return { success: false, error: 'API key is inactive' };
    }

    // 有効期限チェック
    if (apiKey.expiresAt && new Date(apiKey.expiresAt) < new Date()) {
      return { success: false, error: 'API key expired' };
    }

    const scopes = requestedScopes ?? apiKey.scopes;
    const grantedScopes = this.validateScopes(scopes, apiKey.scopes);

    if (grantedScopes.length === 0) {
      return { success: false, error: 'No valid scopes' };
    }

    const token = this.createToken(apiKey.id, grantedScopes);

    // 最終使用日時更新
    apiKey.lastUsedAt = new Date().toISOString();

    return { success: true, token };
  }

  /**
   * トークンを検証
   */
  validateToken(tokenString: string): AuthToken | null {
    const token = this.tokens.get(tokenString);

    if (!token) {
      return null;
    }

    // 有効期限チェック
    if (new Date(token.expiresAt) < new Date()) {
      this.tokens.delete(tokenString);
      return null;
    }

    return token;
  }

  /**
   * スコープをチェック
   */
  checkScope(tokenString: string, requiredScope: AuthScope): boolean {
    const token = this.validateToken(tokenString);

    if (!token) {
      return false;
    }

    return token.scopes.includes(requiredScope) || token.scopes.includes('admin');
  }

  /**
   * APIキーを作成
   */
  createApiKey(name: string, scopes: AuthScope[] = ['read'], expiresInMs?: number): { apiKey: ApiKey; key: string } {
    const id = this.generateId('KEY');
    const key = this.generateApiKeyString();
    const keyHash = this.hashApiKey(key);

    const apiKey: ApiKey = {
      id,
      keyHash,
      name,
      scopes,
      createdAt: new Date().toISOString(),
      expiresAt: expiresInMs
        ? new Date(Date.now() + expiresInMs).toISOString()
        : new Date(Date.now() + this.options.apiKeyTTL).toISOString(),
      active: true,
    };

    this.apiKeys.set(id, apiKey);

    return {
      apiKey: { ...apiKey, keyHash: '[HIDDEN]' },
      key, // 一度だけ返す
    };
  }

  /**
   * APIキーを無効化
   */
  revokeApiKey(id: string): boolean {
    const apiKey = this.apiKeys.get(id);
    if (apiKey) {
      apiKey.active = false;
      return true;
    }
    return false;
  }

  /**
   * トークンを無効化
   */
  revokeToken(tokenString: string): boolean {
    return this.tokens.delete(tokenString);
  }

  /**
   * ユーザーを無効化
   */
  deactivateUser(id: string): boolean {
    const user = this.users.get(id);
    if (user) {
      user.active = false;
      return true;
    }
    return false;
  }

  /**
   * ユーザーを有効化
   */
  activateUser(id: string): boolean {
    const user = this.users.get(id);
    if (user) {
      user.active = true;
      return true;
    }
    return false;
  }

  /**
   * パスワードを変更
   */
  changePassword(userId: string, newPassword: string): boolean {
    const user = this.users.get(userId);
    if (!user) {
      return false;
    }

    const salt = randomBytes(32).toString('hex');
    user.salt = salt;
    user.passwordHash = this.hashPassword(newPassword, salt);
    return true;
  }

  /**
   * ユーザーのスコープを更新
   */
  updateUserScopes(userId: string, scopes: AuthScope[]): boolean {
    const user = this.users.get(userId);
    if (!user) {
      return false;
    }

    user.allowedScopes = scopes;
    return true;
  }

  /**
   * トークンを作成
   */
  private createToken(userId: string, scopes: AuthScope[]): AuthToken {
    const tokenString = this.generateTokenString();
    const expiresAt = new Date(Date.now() + this.options.tokenTTL).toISOString();

    const token: AuthToken = {
      token: tokenString,
      expiresAt,
      scopes,
      userId,
    };

    this.tokens.set(tokenString, token);
    return token;
  }

  /**
   * パスワードをハッシュ化
   */
  private hashPassword(password: string, salt: string): string {
    let hash = password + salt;
    for (let i = 0; i < this.options.hashIterations; i++) {
      hash = createHash('sha256').update(hash).digest('hex');
    }
    return hash;
  }

  /**
   * APIキーをハッシュ化
   */
  private hashApiKey(key: string): string {
    return createHash('sha256').update(key).digest('hex');
  }

  /**
   * スコープを検証
   */
  private validateScopes(requested: AuthScope[], allowed: AuthScope[]): AuthScope[] {
    // adminは全てのスコープを許可
    if (allowed.includes('admin')) {
      return requested;
    }

    return requested.filter((scope) => allowed.includes(scope));
  }

  /**
   * ユーザー名でユーザーを検索
   */
  private findUserByUsername(username: string): User | undefined {
    for (const user of this.users.values()) {
      if (user.username === username) {
        return user;
      }
    }
    return undefined;
  }

  /**
   * ハッシュでAPIキーを検索
   */
  private findApiKeyByHash(keyHash: string): ApiKey | undefined {
    for (const apiKey of this.apiKeys.values()) {
      if (apiKey.keyHash === keyHash) {
        return apiKey;
      }
    }
    return undefined;
  }

  /**
   * IDを生成
   */
  private generateId(prefix: string): string {
    const random = randomBytes(4).toString('hex').toUpperCase();
    return `${prefix}-${random}`;
  }

  /**
   * トークン文字列を生成
   */
  private generateTokenString(): string {
    return randomBytes(32).toString('hex');
  }

  /**
   * APIキー文字列を生成
   */
  private generateApiKeyString(): string {
    return `msbx_${randomBytes(24).toString('hex')}`;
  }

  /**
   * ユーザー数を取得
   */
  getUserCount(): number {
    return this.users.size;
  }

  /**
   * APIキー数を取得
   */
  getApiKeyCount(): number {
    return this.apiKeys.size;
  }

  /**
   * アクティブトークン数を取得
   */
  getActiveTokenCount(): number {
    const now = new Date();
    let count = 0;
    for (const token of this.tokens.values()) {
      if (new Date(token.expiresAt) > now) {
        count++;
      }
    }
    return count;
  }

  /**
   * 期限切れトークンをクリーンアップ
   */
  cleanupExpiredTokens(): number {
    const now = new Date();
    let count = 0;

    for (const [key, token] of this.tokens.entries()) {
      if (new Date(token.expiresAt) < now) {
        this.tokens.delete(key);
        count++;
      }
    }

    return count;
  }

  /**
   * 全データをクリア（テスト用）
   */
  clearAll(): void {
    this.users.clear();
    this.apiKeys.clear();
    this.tokens.clear();
  }
}
