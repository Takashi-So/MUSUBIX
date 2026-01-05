// REQ-AUTH-001, REQ-AUTH-002: Authentication entities
// Traces to: DES-AUTH-001, DES-AUTH-002

/**
 * API Key entity
 * @requirement REQ-AUTH-001
 */
export interface ApiKey {
  key: string;
  clientId: string;
  name: string;
  tier: 'free' | 'standard' | 'premium';
  roles: string[];
  createdAt: Date;
  expiresAt?: Date;
  active: boolean;
}

/**
 * Create API key
 * @requirement REQ-AUTH-001
 */
export function createApiKey(
  key: string,
  clientId: string,
  name: string,
  options: Partial<Pick<ApiKey, 'tier' | 'roles' | 'expiresAt'>> = {}
): ApiKey {
  if (!key || key.length < 32) {
    throw new Error('API key must be at least 32 characters');
  }
  if (!clientId) {
    throw new Error('Client ID is required');
  }
  if (!name) {
    throw new Error('Name is required');
  }

  return {
    key,
    clientId,
    name,
    tier: options.tier ?? 'free',
    roles: options.roles ?? [],
    createdAt: new Date(),
    expiresAt: options.expiresAt,
    active: true,
  };
}

/**
 * Validate API key
 * @requirement REQ-AUTH-001
 */
export function isApiKeyValid(apiKey: ApiKey, now: Date = new Date()): boolean {
  if (!apiKey.active) {
    return false;
  }
  if (apiKey.expiresAt && apiKey.expiresAt < now) {
    return false;
  }
  return true;
}

/**
 * JWT token claims
 * @requirement REQ-AUTH-002
 */
export interface JwtClaims {
  sub: string; // Subject (user ID)
  iss: string; // Issuer
  aud: string | string[]; // Audience
  exp: number; // Expiration time (Unix timestamp)
  iat: number; // Issued at time
  roles?: string[];
  [key: string]: unknown;
}

/**
 * Parsed JWT token
 * @requirement REQ-AUTH-002
 */
export interface JwtToken {
  header: {
    alg: string;
    typ: string;
  };
  payload: JwtClaims;
  signature: string;
  raw: string;
}

/**
 * JWT validation result
 */
export type JwtValidationResult =
  | { valid: true; token: JwtToken }
  | { valid: false; error: string };

/**
 * Parse JWT token (basic parsing, signature validation is simplified)
 * @requirement REQ-AUTH-002
 */
export function parseJwt(tokenString: string): JwtValidationResult {
  const parts = tokenString.split('.');
  if (parts.length !== 3) {
    return { valid: false, error: 'Invalid JWT format: expected 3 parts' };
  }

  try {
    const header = JSON.parse(atob(parts[0]));
    const payload = JSON.parse(atob(parts[1])) as JwtClaims;
    const signature = parts[2];

    // Validate required claims
    if (!payload.sub) {
      return { valid: false, error: 'Missing subject (sub) claim' };
    }
    if (!payload.iss) {
      return { valid: false, error: 'Missing issuer (iss) claim' };
    }
    if (!payload.exp) {
      return { valid: false, error: 'Missing expiration (exp) claim' };
    }

    const token: JwtToken = {
      header,
      payload,
      signature,
      raw: tokenString,
    };

    return { valid: true, token };
  } catch {
    return { valid: false, error: 'Failed to parse JWT' };
  }
}

/**
 * Check if JWT token is expired
 * @requirement REQ-AUTH-002
 */
export function isJwtExpired(token: JwtToken, now: number = Date.now()): boolean {
  const expMs = token.payload.exp * 1000;
  return now > expMs;
}

/**
 * Validate JWT issuer
 * @requirement REQ-AUTH-002
 */
export function isValidIssuer(token: JwtToken, allowedIssuers: string[]): boolean {
  return allowedIssuers.includes(token.payload.iss);
}

/**
 * Get roles from JWT token
 * @requirement REQ-AUTH-003
 */
export function getJwtRoles(token: JwtToken): string[] {
  return token.payload.roles ?? [];
}
