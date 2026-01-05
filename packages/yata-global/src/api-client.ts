/**
 * YATA Global - HTTP API Client
 *
 * @packageDocumentation
 * @module @nahisaho/yata-global
 *
 * @see REQ-YG-API-001
 */

import type {
  ApiResponse,
  AuthToken,
  RateLimitInfo,
  SyncConfig,
} from './types.js';
import { DEFAULT_SYNC_CONFIG } from './types.js';

/**
 * HTTP client for YATA Global API
 */
export class ApiClient {
  private config: SyncConfig;
  private authToken: AuthToken | null = null;
  private rateLimitInfo: RateLimitInfo | null = null;

  constructor(config: Partial<SyncConfig> = {}) {
    this.config = { ...DEFAULT_SYNC_CONFIG, ...config };
  }

  /**
   * Set authentication token
   */
  setAuthToken(token: AuthToken | null): void {
    this.authToken = token;
  }

  /**
   * Get current auth token
   */
  getAuthToken(): AuthToken | null {
    return this.authToken;
  }

  /**
   * Get rate limit info
   */
  getRateLimitInfo(): RateLimitInfo | null {
    return this.rateLimitInfo;
  }

  /**
   * Update configuration
   */
  configure(config: Partial<SyncConfig>): void {
    this.config = { ...this.config, ...config };
  }

  /**
   * GET request
   */
  async get<T>(path: string, params?: Record<string, string | number | boolean>): Promise<ApiResponse<T>> {
    const url = this.buildUrl(path, params);
    return this.request<T>('GET', url);
  }

  /**
   * POST request
   */
  async post<T>(path: string, body?: unknown): Promise<ApiResponse<T>> {
    const url = this.buildUrl(path);
    return this.request<T>('POST', url, body);
  }

  /**
   * PUT request
   */
  async put<T>(path: string, body?: unknown): Promise<ApiResponse<T>> {
    const url = this.buildUrl(path);
    return this.request<T>('PUT', url, body);
  }

  /**
   * DELETE request
   */
  async delete<T>(path: string): Promise<ApiResponse<T>> {
    const url = this.buildUrl(path);
    return this.request<T>('DELETE', url);
  }

  /**
   * Build full URL with query parameters
   */
  private buildUrl(path: string, params?: Record<string, string | number | boolean>): string {
    const base = this.config.endpoint.replace(/\/$/, '');
    const url = new URL(`${base}${path}`);

    if (params) {
      Object.entries(params).forEach(([key, value]) => {
        if (value !== undefined && value !== null) {
          url.searchParams.set(key, String(value));
        }
      });
    }

    return url.toString();
  }

  /**
   * Execute HTTP request
   */
  private async request<T>(method: string, url: string, body?: unknown): Promise<ApiResponse<T>> {
    const headers: Record<string, string> = {
      'Content-Type': 'application/json',
      'Accept': 'application/json',
    };

    // Add auth header if token exists
    if (this.authToken) {
      headers['Authorization'] = `${this.authToken.tokenType} ${this.authToken.accessToken}`;
    }

    // Add API key if configured
    if (this.config.apiKey) {
      headers['X-API-Key'] = this.config.apiKey;
    }

    try {
      const response = await fetch(url, {
        method,
        headers,
        body: body ? JSON.stringify(body) : undefined,
      });

      // Parse rate limit headers
      this.parseRateLimitHeaders(response.headers);

      // Parse response
      const data = await response.json() as T;

      if (!response.ok) {
        return {
          success: false,
          error: (data as { message?: string }).message || `HTTP ${response.status}`,
          rateLimit: this.rateLimitInfo ?? undefined,
        };
      }

      return {
        success: true,
        data,
        rateLimit: this.rateLimitInfo ?? undefined,
      };
    } catch (error) {
      return {
        success: false,
        error: error instanceof Error ? error.message : 'Unknown error',
      };
    }
  }

  /**
   * Parse rate limit headers from response
   */
  private parseRateLimitHeaders(headers: Headers): void {
    const remaining = headers.get('X-RateLimit-Remaining');
    const limit = headers.get('X-RateLimit-Limit');
    const reset = headers.get('X-RateLimit-Reset');

    if (remaining && limit && reset) {
      this.rateLimitInfo = {
        remaining: parseInt(remaining, 10),
        limit: parseInt(limit, 10),
        resetAt: new Date(parseInt(reset, 10) * 1000),
      };
    }
  }

  /**
   * Check if currently rate limited
   */
  isRateLimited(): boolean {
    if (!this.rateLimitInfo) return false;
    return this.rateLimitInfo.remaining <= 0 && this.rateLimitInfo.resetAt > new Date();
  }

  /**
   * Get time until rate limit reset
   */
  getTimeUntilReset(): number {
    if (!this.rateLimitInfo) return 0;
    return Math.max(0, this.rateLimitInfo.resetAt.getTime() - Date.now());
  }
}
