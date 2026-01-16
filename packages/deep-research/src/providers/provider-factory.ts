// Search Provider Factory - Strategy + Chain of Responsibility Pattern
// TSK-DR-006
// REQ: REQ-DR-CORE-002, REQ-DR-NFR-005
// ADR: ADR-v3.4.0-002

import type { SearchProvider, SERPQuery, SearchResult } from '../types/index.js';
import { AllProvidersFailedError } from '../types/errors.js';

export interface ProviderConfig {
  name: string;
  enabled: boolean;
  maxRetries?: number;
  retryDelayMs?: number;
  backoffMultiplier?: number;
}

/**
 * Search Provider Factory
 * 
 * Implements Strategy Pattern for provider selection and
 * Chain of Responsibility Pattern for automatic fallback.
 * 
 * Provider order (REQ: ADR-v3.4.0-002):
 * 1. Jina AI (primary) - Search + Reader API
 * 2. Brave Search (fallback 1) - Exponential backoff
 * 3. DuckDuckGo (fallback 2) - No API key required
 * 
 * Retry strategy:
 * - Initial delay: 1000ms
 * - Backoff multiplier: 2x
 * - Max delay: 10000ms
 * - Max retries: 3
 */
export class SearchProviderFactory {
  private providers: Map<string, SearchProvider> = new Map();
  private providerOrder: string[] = [];
  private configs: Map<string, ProviderConfig> = new Map();
  
  private readonly DEFAULT_RETRY_DELAY = 1000; // 1s
  private readonly DEFAULT_BACKOFF_MULTIPLIER = 2;
  private readonly DEFAULT_MAX_RETRIES = 3;
  private readonly MAX_DELAY = 10000; // 10s
  
  constructor() {
    // Empty constructor - providers are registered via register()
  }
  
  /**
   * Register a search provider
   */
  register(provider: SearchProvider, config?: Partial<ProviderConfig>): void {
    const providerConfig: ProviderConfig = {
      name: provider.name,
      enabled: true,
      maxRetries: this.DEFAULT_MAX_RETRIES,
      retryDelayMs: this.DEFAULT_RETRY_DELAY,
      backoffMultiplier: this.DEFAULT_BACKOFF_MULTIPLIER,
      ...config,
    };
    
    this.providers.set(provider.name, provider);
    this.configs.set(provider.name, providerConfig);
    this.providerOrder.push(provider.name);
    
    console.log(`✅ Registered search provider: ${provider.name}`);
  }
  
  /**
   * Search with automatic provider fallback
   * 
   * REQ: REQ-DR-CORE-002 - Multi-provider search
   * REQ: REQ-DR-NFR-005 - Error handling
   */
  async search(query: SERPQuery): Promise<SearchResult[]> {
    const errors: Array<{ provider: string; error: Error }> = [];
    
    for (const providerName of this.providerOrder) {
      const provider = this.providers.get(providerName);
      const config = this.configs.get(providerName);
      
      if (!provider || !config || !config.enabled) {
        continue;
      }
      
      try {
        // Check provider availability
        if (!(await provider.isAvailable())) {
          console.warn(`⚠️  Provider ${providerName} is not available, trying next...`);
          continue;
        }
        
        console.log(`🔍 Searching with ${providerName}...`);
        
        // Attempt search with retries
        const results = await this.searchWithRetry(provider, query, config);
        
        if (results.length > 0) {
          console.log(`✅ ${providerName} returned ${results.length} results`);
          return results;
        }
        
        console.warn(`⚠️  ${providerName} returned 0 results, trying next...`);
      } catch (error) {
        const err = error instanceof Error ? error : new Error(String(error));
        errors.push({ provider: providerName, error: err });
        console.error(`❌ ${providerName} failed:`, err.message);
      }
    }
    
    // All providers failed
    throw new AllProvidersFailedError(
      `All search providers failed. Tried: ${this.providerOrder.join(', ')}`,
      {
        providers: this.providerOrder,
        errors: errors.map(e => ({ provider: e.provider, message: e.error.message })),
      }
    );
  }
  
  /**
   * Search with exponential backoff retry
   */
  private async searchWithRetry(
    provider: SearchProvider,
    query: SERPQuery,
    config: ProviderConfig
  ): Promise<SearchResult[]> {
    let lastError: Error | null = null;
    let delay = config.retryDelayMs!;
    
    for (let attempt = 0; attempt <= config.maxRetries!; attempt++) {
      try {
        if (attempt > 0) {
          console.log(`🔄 Retry ${attempt}/${config.maxRetries} for ${provider.name} after ${delay}ms...`);
          await this.sleep(delay);
          
          // Exponential backoff with max delay cap
          delay = Math.min(delay * config.backoffMultiplier!, this.MAX_DELAY);
        }
        
        return await provider.search(query);
      } catch (error) {
        lastError = error instanceof Error ? error : new Error(String(error));
        
        if (attempt === config.maxRetries) {
          throw lastError;
        }
      }
    }
    
    throw lastError || new Error('Search failed with unknown error');
  }
  
  /**
   * Get provider by name
   */
  getProvider(name: string): SearchProvider | undefined {
    return this.providers.get(name);
  }
  
  /**
   * Get all registered provider names
   */
  getProviderNames(): string[] {
    return Array.from(this.providers.keys());
  }
  
  /**
   * Enable/disable a provider
   */
  setProviderEnabled(name: string, enabled: boolean): void {
    const config = this.configs.get(name);
    if (config) {
      config.enabled = enabled;
      console.log(`${enabled ? '✅' : '⏸️'} Provider ${name} ${enabled ? 'enabled' : 'disabled'}`);
    }
  }
  
  /**
   * Get provider status
   */
  async getProviderStatus(): Promise<Array<{ name: string; enabled: boolean; available: boolean }>> {
    const status: Array<{ name: string; enabled: boolean; available: boolean }> = [];
    
    for (const [name, provider] of this.providers) {
      const config = this.configs.get(name);
      const available = await provider.isAvailable();
      
      status.push({
        name,
        enabled: config?.enabled ?? false,
        available,
      });
    }
    
    return status;
  }
  
  /**
   * Clear all providers
   */
  clear(): void {
    this.providers.clear();
    this.configs.clear();
    this.providerOrder = [];
  }
  
  /**
   * Sleep utility
   */
  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }
}

/**
 * Create a default factory with standard configuration
 */
export function createSearchProviderFactory(): SearchProviderFactory {
  return new SearchProviderFactory();
}
