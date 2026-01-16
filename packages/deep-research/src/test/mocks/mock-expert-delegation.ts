// Mock Expert Delegation for Testing
// TSK-DR-028
// REQ: 憲法Article III (Test-First)

/**
 * Mock Delegation Request (matching @nahisaho/musubix-expert-delegation v3.2.0+ API)
 */
export interface MockDelegationRequest {
  prompt: string;
  expertType: 'ears-analyst' | 'design-reviewer' | 'security-analyst' | 'architect';
  mode: 'advisory' | 'authoritative';
  context?: Record<string, unknown>;
}

/**
 * Mock Delegation Result
 */
export interface MockDelegationResult {
  content: string;
  confidence: number;
  expertType: string;
  tokensUsed: number;
}

/**
 * Mock Expert Delegation for unit testing
 * 
 * Usage:
 * ```typescript
 * const mockExpert = new MockExpertDelegation();
 * mockExpert.setResponse('ears-analyst', 'WHEN user logs in, THE system SHALL authenticate');
 * const result = await mockExpert.delegate({ prompt: '...', expertType: 'ears-analyst', mode: 'advisory' });
 * ```
 */
export class MockExpertDelegation {
  private responses: Map<string, string> = new Map();
  private defaultResponse = 'Mock expert delegation response';
  private callHistory: MockDelegationRequest[] = [];
  
  /**
   * Set a specific response for an expert type
   */
  setResponse(expertType: string, response: string): void {
    this.responses.set(expertType, response);
  }
  
  /**
   * Set default response for unmatched experts
   */
  setDefaultResponse(response: string): void {
    this.defaultResponse = response;
  }
  
  /**
   * Delegate to expert (mock implementation)
   */
  async delegate(request: MockDelegationRequest): Promise<MockDelegationResult> {
    this.callHistory.push(request);
    
    const response = this.responses.get(request.expertType) ?? this.defaultResponse;
    
    return {
      content: response,
      confidence: 0.95,
      expertType: request.expertType,
      tokensUsed: Math.ceil(response.length / 4),
    };
  }
  
  /**
   * Get call history for assertions
   */
  getCallHistory(): MockDelegationRequest[] {
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
    this.defaultResponse = 'Mock expert delegation response';
  }
  
  /**
   * Verify an expert was consulted
   */
  wasExpertConsulted(expertType: string): boolean {
    return this.callHistory.some(req => req.expertType === expertType);
  }
}
