// Mock HTTP Client for Testing
// TSK-DR-028
// REQ: 憲法Article III (Test-First)

/**
 * Mock HTTP Response
 */
export interface MockHTTPResponse<T = any> {
  data: T;
  status: number;
  statusText: string;
  headers: Record<string, string>;
}

/**
 * Mock HTTP Client for unit testing
 * 
 * Usage:
 * ```typescript
 * const mockHttp = new MockHTTPClient();
 * mockHttp.setResponse('GET', 'https://api.example.com', { data: { result: 'success' } });
 * const response = await mockHttp.get('https://api.example.com');
 * ```
 */
export class MockHTTPClient {
  private responses: Map<string, MockHTTPResponse> = new Map();
  private callHistory: Array<{ method: string; url: string; data?: any }> = [];
  private shouldFail = false;
  private failureError: Error | null = null;
  
  /**
   * Set a mock response for a specific URL
   */
  setResponse<T = any>(method: string, url: string, response: Partial<MockHTTPResponse<T>>): void {
    const key = `${method.toUpperCase()}:${url}`;
    this.responses.set(key, {
      data: response.data ?? {},
      status: response.status ?? 200,
      statusText: response.statusText ?? 'OK',
      headers: response.headers ?? { 'content-type': 'application/json' },
    });
  }
  
  /**
   * Make next request fail
   */
  setShouldFail(shouldFail: boolean, error?: Error): void {
    this.shouldFail = shouldFail;
    this.failureError = error ?? new Error('Mock HTTP client: Simulated failure');
  }
  
  /**
   * GET request (mock)
   */
  async get<T = any>(url: string, config?: { headers?: Record<string, string>; timeout?: number }): Promise<MockHTTPResponse<T>> {
    return this.request('GET', url, undefined, config);
  }
  
  /**
   * POST request (mock)
   */
  async post<T = any>(url: string, data?: any, config?: { headers?: Record<string, string>; timeout?: number }): Promise<MockHTTPResponse<T>> {
    return this.request('POST', url, data, config);
  }
  
  /**
   * HEAD request (mock)
   */
  async head(url: string, config?: { timeout?: number }): Promise<MockHTTPResponse<void>> {
    return this.request('HEAD', url, undefined, config);
  }
  
  /**
   * Generic request handler
   */
  private async request<T = any>(
    method: string,
    url: string,
    _data?: any,
    _config?: { headers?: Record<string, string>; timeout?: number }
  ): Promise<MockHTTPResponse<T>> {
    this.callHistory.push({ method, url, data: _data });
    
    if (this.shouldFail) {
      throw this.failureError ?? new Error('Mock HTTP client: Simulated failure');
    }
    
    const key = `${method.toUpperCase()}:${url}`;
    const response = this.responses.get(key);
    
    if (!response) {
      // Return default 404 response if no mock set
      return {
        data: {} as T,
        status: 404,
        statusText: 'Not Found',
        headers: {},
      };
    }
    
    return response as MockHTTPResponse<T>;
  }
  
  /**
   * Get call history for assertions
   */
  getCallHistory(): Array<{ method: string; url: string; data?: any }> {
    return [...this.callHistory];
  }
  
  /**
   * Get number of calls
   */
  getCallCount(): number {
    return this.callHistory.length;
  }
  
  /**
   * Reset mock state
   */
  reset(): void {
    this.responses.clear();
    this.callHistory = [];
    this.shouldFail = false;
    this.failureError = null;
  }
  
  /**
   * Verify a URL was called
   */
  wasUrlCalled(urlSubstring: string): boolean {
    return this.callHistory.some(call => call.url.includes(urlSubstring));
  }
  
  /**
   * Verify a specific method was used for a URL
   */
  wasMethodUsed(method: string, urlSubstring: string): boolean {
    return this.callHistory.some(
      call => call.method.toUpperCase() === method.toUpperCase() && call.url.includes(urlSubstring)
    );
  }
}
