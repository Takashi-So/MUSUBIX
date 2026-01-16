// DuckDuckGo Search Provider
// TSK-DR-009
// REQ: REQ-DR-CORE-002
// ADR: ADR-v3.4.0-002

import type { SearchProvider, SERPQuery, SearchResult } from '../types/index.js';

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
 * 
 * REQ: REQ-DR-CORE-002 - Multi-provider search
 * ADR: ADR-v3.4.0-002 - DuckDuckGo as fallback 2
 */
export class DuckDuckGoProvider implements SearchProvider {
  name = 'DuckDuckGo';
  
  private readonly API_BASE_URL = 'https://api.duckduckgo.com';
  private readonly timeout: number;
  
  constructor(timeout: number = 10000) {
    this.timeout = timeout;
  }
  
  /**
   * Search using DuckDuckGo Instant Answer API
   * 
   * REQ: REQ-DR-CORE-002
   */
  async search(query: SERPQuery): Promise<SearchResult[]> {
    try {
      const url = new URL(this.API_BASE_URL);
      url.searchParams.set('q', query.keywords);
      url.searchParams.set('format', 'json');
      url.searchParams.set('no_html', '1');
      url.searchParams.set('skip_disambig', '1');
      
      console.log(`🔍 DuckDuckGo searching: ${query.keywords}`);
      
      const response = await this.fetch(url.toString(), {
        headers: {
          'Accept': 'application/json',
        },
      });
      
      if (!response.ok) {
        throw new Error(`DuckDuckGo search failed: ${response.status} ${response.statusText}`);
      }
      
      const data = await response.json();
      
      // Parse DuckDuckGo response
      const results = this.parseSearchResponse(data, query.topK || 10);
      
      console.log(`✅ DuckDuckGo returned ${results.length} results`);
      
      return results;
    } catch (error) {
      const err = error instanceof Error ? error : new Error(String(error));
      console.error(`❌ DuckDuckGo search failed:`, err.message);
      throw err;
    }
  }
  
  /**
   * Check if DuckDuckGo is available
   */
  async isAvailable(): Promise<boolean> {
    try {
      const url = new URL(this.API_BASE_URL);
      url.searchParams.set('q', 'test');
      url.searchParams.set('format', 'json');
      
      const response = await this.fetch(url.toString(), {
        method: 'GET',
        headers: {
          'Accept': 'application/json',
        },
      });
      
      // 200-499 means service is accessible
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
export function createDuckDuckGoProvider(timeout?: number): DuckDuckGoProvider {
  return new DuckDuckGoProvider(timeout);
}
