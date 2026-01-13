/**
 * VS Code API Mock for Testing
 */

export const lm = {
  selectChatModels: vi.fn().mockResolvedValue([
    {
      id: 'mock-model-1',
      name: 'Mock Model',
      family: 'gpt-4',
      vendor: 'copilot',
      maxInputTokens: 8192,
      sendRequest: vi.fn().mockResolvedValue({
        [Symbol.asyncIterator]: async function* () {
          yield 'Mock response';
        },
      }),
    },
  ]),
};

export const LanguageModelChatMessage = {
  User: (content: string) => ({ role: 'user', content }),
  Assistant: (content: string) => ({ role: 'assistant', content }),
};

export const window = {
  showInformationMessage: vi.fn(),
  showErrorMessage: vi.fn(),
  showWarningMessage: vi.fn(),
};

export const workspace = {
  getConfiguration: vi.fn().mockReturnValue({
    get: vi.fn(),
  }),
};
