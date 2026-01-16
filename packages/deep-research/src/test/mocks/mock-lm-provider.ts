// Mock LM Provider for Testing
// TSK-DR-028
// REQ: 憲法Article III (Test-First)

import type { LMProvider, LMRequest, LMResponse } from '../../types/index.js';

/**
 * Mock LM Provider for unit testing
 * 
 * Usage:
 * ```typescript
 * const mockLM = new MockLMProvider();
 * mockLM.setResponse('prompt text', 'mock response');
 * const response = await mockLM.generateText(request);
 * ```
 */
export class MockLMProvider implements LMProvider {
  private responses: Map<string, string> = new Map();
  private defaultResponse = 'Mock LM response';
  private callHistory: LMRequest[] = [];
  
  /**
   * Set a specific response for a prompt
   */
  setResponse(promptSubstring: string, response: string): void {
    this.responses.set(promptSubstring, response);
  }
  
  /**
   * Set default response for unmatched prompts
   */
  setDefaultResponse(response: string): void {
    this.defaultResponse = response;
  }
  
  /**
   * Generate text (mock implementation)
   */
  async generateText(request: LMRequest): Promise<LMResponse> {
    this.callHistory.push(request);
    
    const userMessage = request.messages.find(m => m.role === 'user');
    if (!userMessage) {
      throw new Error('No user message in request');
    }
    
    // Find matching response
    let responseText = this.defaultResponse;
    for (const [promptSubstring, response] of this.responses.entries()) {
      if (userMessage.content.includes(promptSubstring)) {
        responseText = response;
        break;
      }
    }
    
    return {
      text: responseText,
      tokensUsed: Math.ceil(responseText.length / 4), // Rough estimate: 4 chars = 1 token
      model: 'mock-gpt-4',
    };
  }
  
  /**
   * Get call history for assertions
   */
  getCallHistory(): LMRequest[] {
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
    this.defaultResponse = 'Mock LM response';
  }
  
  /**
   * Verify a prompt was sent
   */
  wasPromptSent(substring: string): boolean {
    return this.callHistory.some(req =>
      req.messages.some(m => m.content.includes(substring))
    );
  }
}
