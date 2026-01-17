// DuckDuckGo Search Provider
// TSK-DR-009
// REQ: REQ-DR-CORE-002
// ADR: ADR-v3.4.0-002

import type { SearchProvider, SERPQuery, SearchResult } from '../types/index.js';

/**
 * Rate Limiter for DuckDuckGo API
 * 
 * DuckDuckGo doesn't publish official rate limits, but excessive requests
 * may result in temporary blocks. This implements conservative rate limiting.
 */
class RateLimiter {
  private lastRequestTime = 0;
  private requestCount = 0;
  private windowStart = Date.now();
  
  // Conservative limits: max 10 requests per minute, min 2s between requests
  private readonly minInterval: number;
  private readonly maxRequestsPerMinute: number;
  private readonly windowMs = 60000;
  
  constructor(minIntervalMs: number = 2000, maxRequestsPerMinute: number = 10) {
    this.minInterval = minIntervalMs;
    this.maxRequestsPerMinute = maxRequestsPerMinute;
  }
  
  async waitForSlot(): Promise<void> {
    const now = Date.now();
    
    // Reset window if needed
    if (now - this.windowStart >= this.windowMs) {
      this.windowStart = now;
      this.requestCount = 0;
    }
    
    // Check if we've hit the per-minute limit
    if (this.requestCount >= this.maxRequestsPerMinute) {
      const waitTime = this.windowMs - (now - this.windowStart);
      console.log(`⏳ Rate limit reached, waiting ${Math.ceil(waitTime / 1000)}s...`);
      await this.sleep(waitTime);
      this.windowStart = Date.now();
      this.requestCount = 0;
    }
    
    // Ensure minimum interval between requests
    const timeSinceLastRequest = now - this.lastRequestTime;
    if (timeSinceLastRequest < this.minInterval) {
      const waitTime = this.minInterval - timeSinceLastRequest;
      await this.sleep(waitTime);
    }
    
    this.lastRequestTime = Date.now();
    this.requestCount++;
  }
  
  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }
}

/**
 * DuckDuckGo Search Provider
 * 
 * Uses DuckDuckGo Instant Answer API for web search.
 * 
 * Features:
 * - No API key required
 * - Instant Answer API (simpler results)
 * - Best-effort basis
 * - Fallback provider #2
 * - Rate limiting to avoid blocks
 * - Exponential backoff on errors
 * 
 * REQ: REQ-DR-CORE-002 - Multi-provider search
 * ADR: ADR-v3.4.0-002 - DuckDuckGo as fallback 2
 */
export class DuckDuckGoProvider implements SearchProvider {
  name = 'DuckDuckGo';
  
  private readonly API_BASE_URL = 'https://api.duckduckgo.com';
  private readonly timeout: number;
  private readonly rateLimiter: RateLimiter;
  private readonly maxRetries: number;
  private readonly baseBackoffMs: number;
  
  constructor(options: {
    timeout?: number;
    minIntervalMs?: number;
    maxRequestsPerMinute?: number;
    maxRetries?: number;
    baseBackoffMs?: number;
  } = {}) {
    this.timeout = options.timeout ?? 10000;
    this.maxRetries = options.maxRetries ?? 3;
    this.baseBackoffMs = options.baseBackoffMs ?? 1000;
    this.rateLimiter = new RateLimiter(
      options.minIntervalMs ?? 2000,
      options.maxRequestsPerMinute ?? 10
    );
  }
  
  /**
   * Search using DuckDuckGo Instant Answer API
   * 
   * REQ: REQ-DR-CORE-002
   */
  async search(query: SERPQuery): Promise<SearchResult[]> {
    let lastError: Error | null = null;
    
    for (let attempt = 0; attempt < this.maxRetries; attempt++) {
      try {
        // Wait for rate limiter slot
        await this.rateLimiter.waitForSlot();
        
        const url = new URL(this.API_BASE_URL);
        url.searchParams.set('q', query.keywords);
        url.searchParams.set('format', 'json');
        url.searchParams.set('no_html', '1');
        url.searchParams.set('skip_disambig', '1');
        
        console.log(`🔍 DuckDuckGo searching: ${query.keywords}${attempt > 0 ? ` (retry ${attempt})` : ''}`);
        
        const response = await this.fetch(url.toString(), {
          headers: {
            'Accept': 'application/json',
            'User-Agent': 'MUSUBIX-DeepResearch/3.4.2',
          },
        });
        
        // Handle rate limiting response
        if (response.status === 429) {
          const retryAfter = response.headers.get('Retry-After');
          const waitTime = retryAfter ? parseInt(retryAfter, 10) * 1000 : this.baseBackoffMs * Math.pow(2, attempt);
          console.warn(`⚠️  DuckDuckGo rate limited, waiting ${Math.ceil(waitTime / 1000)}s...`);
          await this.sleep(waitTime);
          continue;
        }
        
        if (!response.ok) {
          throw new Error(`DuckDuckGo search failed: ${response.status} ${response.statusText}`);
        }
        
        const data = await response.json();
        
        // Parse DuckDuckGo response
        const results = this.parseSearchResponse(data, query.topK || 10);
        
        console.log(`✅ DuckDuckGo returned ${results.length} results`);
        
        return results;
      } catch (error) {
        lastError = error instanceof Error ? error : new Error(String(error));
        
        // Don't retry on abort (timeout)
        if (lastError.name === 'AbortError') {
          console.error(`❌ DuckDuckGo search timed out`);
          throw lastError;
        }
        
        // Exponential backoff for other errors
        if (attempt < this.maxRetries - 1) {
          const backoffTime = this.baseBackoffMs * Math.pow(2, attempt);
          console.warn(`⚠️  DuckDuckGo error, retrying in ${Math.ceil(backoffTime / 1000)}s...`);
          await this.sleep(backoffTime);
        }
      }
    }
    
    console.error(`❌ DuckDuckGo search failed after ${this.maxRetries} attempts:`, lastError?.message);
    throw lastError;
  }
  
  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }
  
  /**
   * Check if DuckDuckGo is available
   */
  async isAvailable(): Promise<boolean> {
    try {
      // Wait for rate limiter slot
      await this.rateLimiter.waitForSlot();
      
      const url = new URL(this.API_BASE_URL);
      url.searchParams.set('q', 'test');
      url.searchParams.set('format', 'json');
      
      const response = await this.fetch(url.toString(), {
        method: 'GET',
        headers: {
          'Accept': 'application/json',
          'User-Agent': 'MUSUBIX-DeepResearch/3.4.2',
        },
      });
      
      // 200-499 means service is accessible (429 = rate limited but available)
      return response.status < 500;
    } catch (error) {
      console.warn('⚠️  DuckDuckGo availability check failed:', error);
      return false;
    }
  }
  
  /**
   * Parse DuckDuckGo response
   */
  private parseSearchResponse(data: any, topK: number): SearchResult[] {
    const results: SearchResult[] = [];
    
    // DuckDuckGo Instant Answer API returns various types of results
    
    // Abstract (main answer)
    if (data.Abstract && data.AbstractURL) {
      results.push({
        title: data.Heading || 'DuckDuckGo Answer',
        url: data.AbstractURL,
        snippet: data.Abstract,
        relevance: 0.95,
      });
    }
    
    // Related Topics
    if (data.RelatedTopics && Array.isArray(data.RelatedTopics)) {
      for (const topic of data.RelatedTopics) {
        if (results.length >= topK) break;
        
        if (topic.FirstURL && topic.Text) {
          results.push({
            title: this.extractTitle(topic.Text),
            url: topic.FirstURL,
            snippet: topic.Text,
            relevance: 0.7 - results.length * 0.05,
          });
        }
        
        // Some topics have nested topics
        if (topic.Topics && Array.isArray(topic.Topics)) {
          for (const subtopic of topic.Topics) {
            if (results.length >= topK) break;
            
            if (subtopic.FirstURL && subtopic.Text) {
              results.push({
                title: this.extractTitle(subtopic.Text),
                url: subtopic.FirstURL,
                snippet: subtopic.Text,
                relevance: 0.6 - results.length * 0.05,
              });
            }
          }
        }
      }
    }
    
    // Results (additional web results)
    if (data.Results && Array.isArray(data.Results)) {
      for (const result of data.Results) {
        if (results.length >= topK) break;
        
        if (result.FirstURL && result.Text) {
          results.push({
            title: this.extractTitle(result.Text),
            url: result.FirstURL,
            snippet: result.Text,
            relevance: 0.5 - results.length * 0.05,
          });
        }
      }
    }
    
    return results.slice(0, topK);
  }
  
  /**
   * Extract title from text (first part before dash or full text)
   */
  private extractTitle(text: string): string {
    const parts = text.split(' - ');
    if (parts.length > 1) {
      return parts[0].trim();
    }
    
    // Use first 60 characters as title
    if (text.length > 60) {
      return text.substring(0, 57) + '...';
    }
    
    return text;
  }
  
  /**
   * Fetch wrapper with timeout
   */
  private async fetch(url: string, options: RequestInit = {}): Promise<Response> {
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), this.timeout);
    
    try {
      const response = await fetch(url, {
        ...options,
        signal: controller.signal,
      });
      
      return response;
    } finally {
      clearTimeout(timeoutId);
    }
  }
}

/**
 * Create a DuckDuckGo provider instance
 */
export function createDuckDuckGoProvider(options?: {
  timeout?: number;
  minIntervalMs?: number;
  maxRequestsPerMinute?: number;
  maxRetries?: number;
  baseBackoffMs?: number;
} | number): DuckDuckGoProvider {
  // Support legacy timeout-only parameter
  if (typeof options === 'number') {
    return new DuckDuckGoProvider({ timeout: options });
  }
  return new DuckDuckGoProvider(options);
}
