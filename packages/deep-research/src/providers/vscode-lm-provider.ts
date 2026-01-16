// VS Code LM Provider
// TSK-DR-011
// REQ: REQ-DR-CORE-004
// ADR: ADR-v3.4.0-003

import type { LMProvider, LMGenerationOptions } from '../reasoning/lm-reasoning.js';

/**
 * VS Code Language Model Provider
 * 
 * Wrapper for VS Code's Language Model API (vscode.lm).
 * 
 * Features:
 * - Access to VS Code's LM API
 * - Automatic model selection
 * - Token counting
 * - Streaming support (future)
 * 
 * REQ: REQ-DR-CORE-004 - LM-based reasoning
 * ADR: ADR-v3.4.0-003 - Use VS Code LM API
 */
export class VSCodeLMProvider implements LMProvider {
  name = 'VS Code LM';
  
  private readonly modelSelector: string;
  
  constructor(modelSelector: string = 'copilot-gpt-4') {
    this.modelSelector = modelSelector;
  }
  
  /**
   * Generate text completion using VS Code LM API
   */
  async generate(prompt: string, options?: LMGenerationOptions): Promise<string> {
    console.log(`🤖 Generating with VS Code LM (${this.modelSelector})...`);
    
    try {
      // Check if VS Code API is available
      if (typeof (globalThis as any).vscode === 'undefined') {
        throw new Error('VS Code API not available');
      }
      
      const vscode = (globalThis as any).vscode;
      
      // Select language model
      const models = await vscode.lm.selectChatModels({
        vendor: 'copilot',
        family: this.modelSelector,
      });
      
      if (models.length === 0) {
        throw new Error(`No models found for selector: ${this.modelSelector}`);
      }
      
      const model = models[0];
      
      // Prepare messages
      const messages: any[] = [];
      
      if (options?.systemPrompt) {
        messages.push(
          vscode.LanguageModelChatMessage.User(options.systemPrompt)
        );
      }
      
      messages.push(vscode.LanguageModelChatMessage.User(prompt));
      
      // Send request
      const response = await model.sendRequest(messages, {
        maxTokens: options?.maxTokens,
        temperature: options?.temperature,
        stopSequences: options?.stop,
      });
      
      // Collect response
      let result = '';
      for await (const chunk of response.text) {
        result += chunk;
      }
      
      console.log(`✅ Generated ${result.length} characters`);
      
      return result;
    } catch (error) {
      const err = error instanceof Error ? error : new Error(String(error));
      console.error(`❌ VS Code LM generation failed:`, err.message);
      throw err;
    }
  }
  
  /**
   * Check if VS Code LM is available
   */
  async isAvailable(): Promise<boolean> {
    try {
      if (typeof (globalThis as any).vscode === 'undefined') {
        return false;
      }
      
      const vscode = (globalThis as any).vscode;
      
      const models = await vscode.lm.selectChatModels({
        vendor: 'copilot',
      });
      
      return models.length > 0;
    } catch (error) {
      console.warn('⚠️  VS Code LM availability check failed:', error);
      return false;
    }
  }
}

/**
 * Create a VS Code LM provider instance
 */
export function createVSCodeLMProvider(modelSelector?: string): VSCodeLMProvider {
  return new VSCodeLMProvider(modelSelector);
}
