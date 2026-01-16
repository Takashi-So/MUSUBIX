// Mock LM Provider Tests
// TSK-DR-028

import { describe, it, expect, beforeEach } from 'vitest';
import { MockLMProvider } from '../mocks/mock-lm-provider.js';

describe('MockLMProvider', () => {
  let mockLM: MockLMProvider;

  beforeEach(() => {
    mockLM = new MockLMProvider();
  });

  it('should return default response when no specific response set', async () => {
    const response = await mockLM.generateText({
      messages: [{ role: 'user', content: 'test prompt' }],
    });

    expect(response.text).toBe('Mock LM response');
    expect(response.tokensUsed).toBeGreaterThan(0);
    expect(response.model).toBe('mock-gpt-4');
  });

  it('should return specific response when set', async () => {
    mockLM.setResponse('authentication', 'Auth is important for security');

    const response = await mockLM.generateText({
      messages: [{ role: 'user', content: 'How to implement authentication?' }],
    });

    expect(response.text).toBe('Auth is important for security');
  });

  it('should track call history', async () => {
    await mockLM.generateText({
      messages: [{ role: 'user', content: 'prompt 1' }],
    });
    await mockLM.generateText({
      messages: [{ role: 'user', content: 'prompt 2' }],
    });

    expect(mockLM.getCallCount()).toBe(2);
    expect(mockLM.wasPromptSent('prompt 1')).toBe(true);
    expect(mockLM.wasPromptSent('prompt 3')).toBe(false);
  });

  it('should reset state correctly', async () => {
    mockLM.setResponse('test', 'response');
    await mockLM.generateText({
      messages: [{ role: 'user', content: 'test' }],
    });

    mockLM.reset();

    expect(mockLM.getCallCount()).toBe(0);
    const response = await mockLM.generateText({
      messages: [{ role: 'user', content: 'test' }],
    });
    expect(response.text).toBe('Mock LM response');
  });
});
