/**
 * Authentication Manager
 * 
 * Manages authentication and authorization
 * 
 * @packageDocumentation
 * @module auth/auth-manager
 * 
 * @see REQ-SEC-002 - Authentication & Authorization
 * @see Article VIII - Human Oversight
 */

/**
 * Auth provider type
 */
export type AuthProvider = 'local' | 'oauth' | 'saml' | 'ldap' | 'api-key';

/**
 * Token type
 */
export type TokenType = 'access' | 'refresh' | 'api-key';

/**
 * Permission
 */
export type Permission = 
  | 'read'
  | 'write'
  | 'delete'
  | 'admin'
  | 'requirements:read'
  | 'requirements:write'
  | 'design:read'
  | 'design:write'
  | 'code:generate'
  | 'code:execute'
  | 'explain:access'
  | 'config:read'
  | 'config:write';

/**
 * User info
 */
export interface UserInfo {
  /** User ID */
  id: string;
  /** Username */
  username: string;
  /** Email */
  email?: string;
  /** Display name */
  displayName?: string;
  /** Roles */
  roles: string[];
  /** Permissions */
  permissions: Permission[];
  /** Auth provider */
  provider: AuthProvider;
  /** Created at */
  createdAt: Date;
  /** Last login */
  lastLogin?: Date;
  /** Is active */
  active: boolean;
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Auth token
 */
export interface AuthToken {
  /** Token string */
  token: string;
  /** Token type */
  type: TokenType;
  /** User ID */
  userId: string;
  /** Issued at */
  issuedAt: Date;
  /** Expires at */
  expiresAt: Date;
  /** Scopes */
  scopes: string[];
  /** Is valid */
  valid: boolean;
}

/**
 * Auth session
 */
export interface AuthSession {
  /** Session ID */
  id: string;
  /** User ID */
  userId: string;
  /** Access token */
  accessToken: AuthToken;
  /** Refresh token */
  refreshToken?: AuthToken;
  /** Created at */
  createdAt: Date;
  /** Expires at */
  expiresAt: Date;
  /** IP address */
  ipAddress?: string;
  /** User agent */
  userAgent?: string;
  /** Is active */
  active: boolean;
}

/**
 * Login credentials
 */
export interface LoginCredentials {
  /** Username or email */
  username: string;
  /** Password */
  password: string;
  /** Remember me */
  rememberMe?: boolean;
  /** MFA code */
  mfaCode?: string;
}

/**
 * Auth result
 */
export interface AuthResult {
  /** Success */
  success: boolean;
  /** Session */
  session?: AuthSession;
  /** User */
  user?: UserInfo;
  /** Error message */
  error?: string;
  /** Requires MFA */
  requiresMfa?: boolean;
}

/**
 * Role definition
 */
export interface RoleDefinition {
  /** Role name */
  name: string;
  /** Description */
  description: string;
  /** Permissions */
  permissions: Permission[];
  /** Parent roles (inherit permissions) */
  inherits?: string[];
}

/**
 * Auth config
 */
export interface AuthManagerConfig {
  /** Supported providers */
  providers: AuthProvider[];
  /** Access token lifetime (ms) */
  accessTokenLifetime: number;
  /** Refresh token lifetime (ms) */
  refreshTokenLifetime: number;
  /** Session lifetime (ms) */
  sessionLifetime: number;
  /** Max sessions per user */
  maxSessionsPerUser: number;
  /** Require MFA */
  requireMfa: boolean;
  /** Password policy */
  passwordPolicy: {
    minLength: number;
    requireUppercase: boolean;
    requireLowercase: boolean;
    requireNumbers: boolean;
    requireSpecial: boolean;
  };
}

/**
 * Default configuration
 */
export const DEFAULT_AUTH_CONFIG: AuthManagerConfig = {
  providers: ['local', 'api-key'],
  accessTokenLifetime: 15 * 60 * 1000, // 15 minutes
  refreshTokenLifetime: 7 * 24 * 60 * 60 * 1000, // 7 days
  sessionLifetime: 24 * 60 * 60 * 1000, // 24 hours
  maxSessionsPerUser: 5,
  requireMfa: false,
  passwordPolicy: {
    minLength: 8,
    requireUppercase: true,
    requireLowercase: true,
    requireNumbers: true,
    requireSpecial: false,
  },
};

/**
 * Built-in roles
 */
export const BUILTIN_ROLES: RoleDefinition[] = [
  {
    name: 'viewer',
    description: 'Read-only access',
    permissions: [
      'read',
      'requirements:read',
      'design:read',
      'explain:access',
      'config:read',
    ],
  },
  {
    name: 'developer',
    description: 'Development access',
    permissions: [
      'read',
      'write',
      'requirements:read',
      'requirements:write',
      'design:read',
      'design:write',
      'code:generate',
      'explain:access',
      'config:read',
    ],
    inherits: ['viewer'],
  },
  {
    name: 'admin',
    description: 'Full administrative access',
    permissions: [
      'read',
      'write',
      'delete',
      'admin',
      'requirements:read',
      'requirements:write',
      'design:read',
      'design:write',
      'code:generate',
      'code:execute',
      'explain:access',
      'config:read',
      'config:write',
    ],
    inherits: ['developer'],
  },
];

/**
 * Authentication Manager
 */
export class AuthManager {
  private config: AuthManagerConfig;
  private users: Map<string, UserInfo> = new Map();
  private passwords: Map<string, string> = new Map(); // userId -> hashed password
  private sessions: Map<string, AuthSession> = new Map();
  private tokens: Map<string, AuthToken> = new Map();
  private apiKeys: Map<string, { userId: string; scopes: string[] }> = new Map();
  private roles: Map<string, RoleDefinition> = new Map();
  private userCounter = 0;
  private sessionCounter = 0;

  constructor(config?: Partial<AuthManagerConfig>) {
    this.config = { ...DEFAULT_AUTH_CONFIG, ...config };
    this.initializeRoles();
  }

  /**
   * Initialize built-in roles
   */
  private initializeRoles(): void {
    for (const role of BUILTIN_ROLES) {
      this.roles.set(role.name, role);
    }
  }

  /**
   * Register a new user
   */
  async register(
    username: string,
    password: string,
    email?: string,
    roles: string[] = ['viewer']
  ): Promise<AuthResult> {
    // Check if username exists
    const existingUser = Array.from(this.users.values()).find(
      (u) => u.username === username || u.email === email
    );
    if (existingUser) {
      return { success: false, error: 'Username or email already exists' };
    }

    // Validate password
    const passwordValidation = this.validatePassword(password);
    if (!passwordValidation.valid) {
      return { success: false, error: passwordValidation.error };
    }

    // Create user
    const userId = `user-${++this.userCounter}-${Date.now()}`;
    const permissions = this.resolvePermissions(roles);

    const user: UserInfo = {
      id: userId,
      username,
      email,
      displayName: username,
      roles,
      permissions,
      provider: 'local',
      createdAt: new Date(),
      active: true,
    };

    // Store user and password
    this.users.set(userId, user);
    this.passwords.set(userId, await this.hashPassword(password));

    return { success: true, user };
  }

  /**
   * Login with credentials
   */
  async login(credentials: LoginCredentials): Promise<AuthResult> {
    // Find user
    const user = Array.from(this.users.values()).find(
      (u) => u.username === credentials.username || u.email === credentials.username
    );

    if (!user) {
      return { success: false, error: 'Invalid credentials' };
    }

    if (!user.active) {
      return { success: false, error: 'Account is disabled' };
    }

    // Verify password
    const storedHash = this.passwords.get(user.id);
    if (!storedHash || !(await this.verifyPassword(credentials.password, storedHash))) {
      return { success: false, error: 'Invalid credentials' };
    }

    // Check MFA if required
    if (this.config.requireMfa && !credentials.mfaCode) {
      return { success: false, requiresMfa: true, error: 'MFA code required' };
    }

    // Clean up old sessions
    await this.cleanupSessions(user.id);

    // Create session
    const session = await this.createSession(user, credentials.rememberMe);

    // Update last login
    user.lastLogin = new Date();

    return { success: true, session, user };
  }

  /**
   * Logout
   */
  async logout(sessionId: string): Promise<boolean> {
    const session = this.sessions.get(sessionId);
    if (!session) return false;

    // Invalidate tokens
    this.tokens.delete(session.accessToken.token);
    if (session.refreshToken) {
      this.tokens.delete(session.refreshToken.token);
    }

    // Remove session
    this.sessions.delete(sessionId);

    return true;
  }

  /**
   * Validate token
   */
  validateToken(tokenString: string): AuthToken | null {
    const token = this.tokens.get(tokenString);
    if (!token) return null;

    if (!token.valid || new Date() > token.expiresAt) {
      token.valid = false;
      return null;
    }

    return token;
  }

  /**
   * Refresh session
   */
  async refreshSession(refreshTokenString: string): Promise<AuthResult> {
    const refreshToken = this.validateToken(refreshTokenString);
    if (!refreshToken || refreshToken.type !== 'refresh') {
      return { success: false, error: 'Invalid refresh token' };
    }

    const user = this.users.get(refreshToken.userId);
    if (!user || !user.active) {
      return { success: false, error: 'User not found or inactive' };
    }

    // Find and invalidate old session
    const oldSession = Array.from(this.sessions.values()).find(
      (s) => s.refreshToken?.token === refreshTokenString
    );
    if (oldSession) {
      this.tokens.delete(oldSession.accessToken.token);
      this.sessions.delete(oldSession.id);
    }

    // Create new session
    const session = await this.createSession(user, true);

    return { success: true, session, user };
  }

  /**
   * Create API key
   */
  createApiKey(userId: string, scopes: string[]): string {
    const user = this.users.get(userId);
    if (!user) {
      throw new Error('User not found');
    }

    const apiKey = `msbx_${this.generateToken(32)}`;
    this.apiKeys.set(apiKey, { userId, scopes });

    // Create token record
    const token: AuthToken = {
      token: apiKey,
      type: 'api-key',
      userId,
      issuedAt: new Date(),
      expiresAt: new Date(Date.now() + 365 * 24 * 60 * 60 * 1000), // 1 year
      scopes,
      valid: true,
    };
    this.tokens.set(apiKey, token);

    return apiKey;
  }

  /**
   * Validate API key
   */
  validateApiKey(apiKey: string): { user: UserInfo; scopes: string[] } | null {
    const keyInfo = this.apiKeys.get(apiKey);
    if (!keyInfo) return null;

    const user = this.users.get(keyInfo.userId);
    if (!user || !user.active) return null;

    return { user, scopes: keyInfo.scopes };
  }

  /**
   * Check permission
   */
  hasPermission(userId: string, permission: Permission): boolean {
    const user = this.users.get(userId);
    if (!user || !user.active) return false;

    return user.permissions.includes(permission) || user.permissions.includes('admin');
  }

  /**
   * Check multiple permissions (all required)
   */
  hasAllPermissions(userId: string, permissions: Permission[]): boolean {
    return permissions.every((p) => this.hasPermission(userId, p));
  }

  /**
   * Check multiple permissions (any required)
   */
  hasAnyPermission(userId: string, permissions: Permission[]): boolean {
    return permissions.some((p) => this.hasPermission(userId, p));
  }

  /**
   * Get user from token
   */
  getUserFromToken(tokenString: string): UserInfo | null {
    const token = this.validateToken(tokenString);
    if (!token) return null;

    const user = this.users.get(token.userId);
    if (!user || !user.active) return null;

    return user;
  }

  /**
   * Add role to user
   */
  addRole(userId: string, roleName: string): boolean {
    const user = this.users.get(userId);
    if (!user) return false;

    if (!user.roles.includes(roleName)) {
      user.roles.push(roleName);
      user.permissions = this.resolvePermissions(user.roles);
    }

    return true;
  }

  /**
   * Remove role from user
   */
  removeRole(userId: string, roleName: string): boolean {
    const user = this.users.get(userId);
    if (!user) return false;

    const index = user.roles.indexOf(roleName);
    if (index > -1) {
      user.roles.splice(index, 1);
      user.permissions = this.resolvePermissions(user.roles);
    }

    return true;
  }

  /**
   * Define custom role
   */
  defineRole(role: RoleDefinition): void {
    this.roles.set(role.name, role);
  }

  /**
   * Get all sessions for user
   */
  getUserSessions(userId: string): AuthSession[] {
    return Array.from(this.sessions.values()).filter(
      (s) => s.userId === userId && s.active
    );
  }

  /**
   * Revoke all sessions for user
   */
  revokeAllSessions(userId: string): number {
    let count = 0;
    for (const [sessionId, session] of this.sessions) {
      if (session.userId === userId) {
        this.tokens.delete(session.accessToken.token);
        if (session.refreshToken) {
          this.tokens.delete(session.refreshToken.token);
        }
        this.sessions.delete(sessionId);
        count++;
      }
    }
    return count;
  }

  /**
   * Deactivate user
   */
  deactivateUser(userId: string): boolean {
    const user = this.users.get(userId);
    if (!user) return false;

    user.active = false;
    this.revokeAllSessions(userId);

    return true;
  }

  /**
   * Activate user
   */
  activateUser(userId: string): boolean {
    const user = this.users.get(userId);
    if (!user) return false;

    user.active = true;
    return true;
  }

  /**
   * Change password
   */
  async changePassword(
    userId: string,
    oldPassword: string,
    newPassword: string
  ): Promise<{ success: boolean; error?: string }> {
    const user = this.users.get(userId);
    if (!user) {
      return { success: false, error: 'User not found' };
    }

    const storedHash = this.passwords.get(userId);
    if (!storedHash || !(await this.verifyPassword(oldPassword, storedHash))) {
      return { success: false, error: 'Invalid current password' };
    }

    const validation = this.validatePassword(newPassword);
    if (!validation.valid) {
      return { success: false, error: validation.error };
    }

    this.passwords.set(userId, await this.hashPassword(newPassword));

    // Revoke all sessions (force re-login)
    this.revokeAllSessions(userId);

    return { success: true };
  }

  /**
   * Create session
   */
  private async createSession(user: UserInfo, longLived: boolean = false): Promise<AuthSession> {
    const sessionId = `session-${++this.sessionCounter}-${Date.now()}`;
    const now = new Date();
    const accessTokenExpiry = new Date(now.getTime() + this.config.accessTokenLifetime);
    const refreshTokenExpiry = longLived
      ? new Date(now.getTime() + this.config.refreshTokenLifetime)
      : new Date(now.getTime() + this.config.sessionLifetime);
    const sessionExpiry = longLived
      ? refreshTokenExpiry
      : new Date(now.getTime() + this.config.sessionLifetime);

    // Create access token
    const accessToken: AuthToken = {
      token: this.generateToken(64),
      type: 'access',
      userId: user.id,
      issuedAt: now,
      expiresAt: accessTokenExpiry,
      scopes: user.permissions,
      valid: true,
    };

    // Create refresh token
    const refreshToken: AuthToken = {
      token: this.generateToken(64),
      type: 'refresh',
      userId: user.id,
      issuedAt: now,
      expiresAt: refreshTokenExpiry,
      scopes: ['refresh'],
      valid: true,
    };

    // Store tokens
    this.tokens.set(accessToken.token, accessToken);
    this.tokens.set(refreshToken.token, refreshToken);

    // Create session
    const session: AuthSession = {
      id: sessionId,
      userId: user.id,
      accessToken,
      refreshToken,
      createdAt: now,
      expiresAt: sessionExpiry,
      active: true,
    };

    this.sessions.set(sessionId, session);

    return session;
  }

  /**
   * Cleanup old sessions for user
   */
  private async cleanupSessions(userId: string): Promise<void> {
    const userSessions = this.getUserSessions(userId);

    // Remove expired sessions
    const now = new Date();
    for (const session of userSessions) {
      if (session.expiresAt < now) {
        await this.logout(session.id);
      }
    }

    // Enforce max sessions limit
    const activeSessions = this.getUserSessions(userId);
    if (activeSessions.length >= this.config.maxSessionsPerUser) {
      // Remove oldest sessions
      activeSessions
        .sort((a, b) => a.createdAt.getTime() - b.createdAt.getTime())
        .slice(0, activeSessions.length - this.config.maxSessionsPerUser + 1)
        .forEach((s) => this.logout(s.id));
    }
  }

  /**
   * Resolve permissions from roles
   */
  private resolvePermissions(roleNames: string[]): Permission[] {
    const permissions = new Set<Permission>();

    const processRole = (roleName: string, visited: Set<string>) => {
      if (visited.has(roleName)) return;
      visited.add(roleName);

      const role = this.roles.get(roleName);
      if (!role) return;

      for (const perm of role.permissions) {
        permissions.add(perm);
      }

      if (role.inherits) {
        for (const parentRole of role.inherits) {
          processRole(parentRole, visited);
        }
      }
    };

    for (const roleName of roleNames) {
      processRole(roleName, new Set());
    }

    return Array.from(permissions);
  }

  /**
   * Validate password against policy
   */
  private validatePassword(password: string): { valid: boolean; error?: string } {
    const { passwordPolicy } = this.config;

    if (password.length < passwordPolicy.minLength) {
      return { valid: false, error: `Password must be at least ${passwordPolicy.minLength} characters` };
    }

    if (passwordPolicy.requireUppercase && !/[A-Z]/.test(password)) {
      return { valid: false, error: 'Password must contain uppercase letters' };
    }

    if (passwordPolicy.requireLowercase && !/[a-z]/.test(password)) {
      return { valid: false, error: 'Password must contain lowercase letters' };
    }

    if (passwordPolicy.requireNumbers && !/[0-9]/.test(password)) {
      return { valid: false, error: 'Password must contain numbers' };
    }

    if (passwordPolicy.requireSpecial && !/[!@#$%^&*(),.?":{}|<>]/.test(password)) {
      return { valid: false, error: 'Password must contain special characters' };
    }

    return { valid: true };
  }

  /**
   * Hash password (simplified - in production use bcrypt/argon2)
   */
  private async hashPassword(password: string): Promise<string> {
    // In production, use proper hashing like bcrypt
    const encoder = new TextEncoder();
    const data = encoder.encode(password + 'musubix-salt');
    
    if (typeof crypto !== 'undefined' && crypto.subtle) {
      const hashBuffer = await crypto.subtle.digest('SHA-256', data);
      const hashArray = Array.from(new Uint8Array(hashBuffer));
      return hashArray.map((b) => b.toString(16).padStart(2, '0')).join('');
    }
    
    // Fallback (not secure, for demo only)
    return Buffer.from(data).toString('base64');
  }

  /**
   * Verify password
   */
  private async verifyPassword(password: string, hash: string): Promise<boolean> {
    const computed = await this.hashPassword(password);
    return computed === hash;
  }

  /**
   * Generate random token
   */
  private generateToken(length: number): string {
    const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
    let result = '';
    for (let i = 0; i < length; i++) {
      result += chars.charAt(Math.floor(Math.random() * chars.length));
    }
    return result;
  }

  /**
   * Get user by ID
   */
  getUser(userId: string): UserInfo | undefined {
    return this.users.get(userId);
  }

  /**
   * Get all users
   */
  getAllUsers(): UserInfo[] {
    return Array.from(this.users.values());
  }

  /**
   * Get role definition
   */
  getRole(roleName: string): RoleDefinition | undefined {
    return this.roles.get(roleName);
  }

  /**
   * Get all roles
   */
  getAllRoles(): RoleDefinition[] {
    return Array.from(this.roles.values());
  }
}

/**
 * Create auth manager instance
 */
export function createAuthManager(config?: Partial<AuthManagerConfig>): AuthManager {
  return new AuthManager(config);
}

/**
 * Middleware helper for permission check
 */
export function requirePermission(
  authManager: AuthManager,
  ...permissions: Permission[]
): (token: string) => boolean {
  return (token: string) => {
    const user = authManager.getUserFromToken(token);
    if (!user) return false;
    return authManager.hasAllPermissions(user.id, permissions);
  };
}
