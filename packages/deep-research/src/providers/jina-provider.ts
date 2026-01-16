// Jina AI Search Provider
// TSK-DR-007
// REQ: REQ-DR-CORE-002, REQ-DR-CORE-003
// ADR: ADR-v3.4.0-002

import type { SearchProvider, SERPQuery, SearchResult, WebContent, WebReadRequest } from '../types/index.js';

/**
 * Jina AI Search Provider
 * 
 * Uses Jina AI's r.jina.ai API for both search and web content reading.
 * 
 * Features:
 * - Search API: s.jina.ai (SERP results)
 * - Reader API: r.jina.ai (full web content extraction)
 * - No API key required for basic usage
 * - Supports both search and read operations
 * 
 * REQ: REQ-DR-CORE-002 - Primary search provider
 * REQ: REQ-DR-CORE-003 - Web content reading
 * ADR: ADR-v3.4.0-002 - Jina AI as primary provider
 */
export class JinaProvider implements SearchProvider {
  name = 'Jina AI';
  
  private readonly SEARCH_BASE_URL = 'https://s.jina.ai';
  private readonly READER_BASE_URL = 'https://r.jina.ai';
  private readonly timeout: number;
  
  constructor(timeout: number = 10000) {
    this.timeout = timeout;
  }
  
  /**
   * Search using Jina AI Search API
   * 
   * REQ: REQ-DR-CORE-002
   */
  async search(query: SERPQuery): Promise<SearchResult[]> {
    try {
      const url = `${this.SEARCH_BASE_URL}/${encodeURIComponent(query.keywords)}`;
      
      console.log(`🔍 Jina AI searching: ${query.keywords}`);
      
      const response = await this.fetch(url, {
        headers: {
          'Accept': 'application/json',
        },
      });
      
      if (!response.ok) {
        throw new Error(`Jina AI search failed: ${response.status} ${response.statusText}`);
      }
      
      const data = await response.json();
      
      // Parse Jina AI response format
      const results = this.parseSearchResponse(data, query.topK || 10);
      
      console.log(`✅ Jina AI returned ${results.length} results`);
      
      return results;
    } catch (error) {
      const err = error instanceof Error ? error : new Error(String(error));
      console.error(`❌ Jina AI search failed:`, err.message);
      throw err;
    }
  }
  
  /**
   * Read web content using Jina AI Reader API
   * 
   * REQ: REQ-DR-CORE-003
   */
  async read(request: WebReadRequest): Promise<WebContent> {
    try {
      const url = `${this.READER_BASE_URL}/${request.url}`;
      
      console.log(`📖 Jina AI reading: ${request.url}`);
      
      const response = await this.fetch(url, {
        headers: {
          'Accept': 'application/json',
        },
      });
      
      if (!response.ok) {
        throw new Error(`Jina AI reader failed: ${response.status} ${response.statusText}`);
      }
      
      const data = await response.json();
      
      // Parse Jina AI reader response
      const content = this.parseReaderResponse(data, request.url);
      
      console.log(`✅ Jina AI read ${content.extractedFacts.length} facts from ${request.url}`);
      
      return content;
    } catch (error) {
      const err = error instanceof Error ? error : new Error(String(error));
      console.error(`❌ Jina AI reader failed for ${request.url}:`, err.message);
      throw err;
    }
  }
  
  /**
   * Check if Jina AI is available
   */
  async isAvailable(): Promise<boolean> {
    try {
      // Simple health check - try to access the search endpoint
      const response = await this.fetch(`${this.SEARCH_BASE_URL}/test`, {
        method: 'HEAD',
        headers: {
          'Accept': 'application/json',
        },
      });
      
      // Jina AI returns various status codes, but 200-499 means it's accessible
      return response.status < 500;
    } catch (error) {
      console.warn('⚠️  Jina AI availability check failed:', error);
      return false;
    }
  }
  
  /**
   * Parse Jina AI search response
   */
  private parseSearchResponse(data: any, topK: number): SearchResult[] {
    const results: SearchResult[] = [];
    
    // Jina AI response format varies, handle multiple formats
    const items = data.data || data.results || data.items || [];
    
    for (let i = 0; i < Math.min(items.length, topK); i++) {
      const item = items[i];
      
      // Extract fields with fallbacks
      const title = item.title || item.name || item.heading || 'Untitled';
      const url = item.url || item.link || item.href || '';
      const snippet = item.snippet || item.description || item.content || item.text || '';
      
      if (url) {
        results.push({
          title,
          url,
          snippet,
          relevance: this.calculateRelevance(i, items.length),
          date: item.publishedDate || item.date,
        });
      }
    }
    
    return results;
  }
  
  /**
   * Parse Jina AI reader response
   */
  private parseReaderResponse(data: any, url: string): WebContent {
    // Extract content from Jina AI reader response
    const content = data.content || data.text || data.data || '';
    const title = data.title || data.heading || this.extractTitleFromUrl(url);
    
    // Extract facts from content (simple paragraph splitting)
    const extractedFacts = this.extractFacts(content);
    
    return {
      url,
      title,
      content,
      extractedFacts,
    };
  }
  
  /**
   * Extract facts from content (simple heuristic)
   */
  private extractFacts(content: string): string[] {
    if (!content || content.length === 0) {
      return [];
    }
    
    // Split by paragraphs and filter meaningful sentences
    const paragraphs = content
      .split(/\n\n+/)
      .map(p => p.trim())
      .filter(p => p.length > 50 && p.length < 500); // Reasonable fact length
    
    return paragraphs.slice(0, 10); // Return top 10 facts
  }
  
  /**
   * Calculate relevance score based on position
   */
  private calculateRelevance(index: number, total: number): number {
    if (total === 0) return 0.5;
    
    // Linear decay from 0.95 to 0.5
    const maxRelevance = 0.95;
    const minRelevance = 0.5;
    const decay = (maxRelevance - minRelevance) / Math.max(total - 1, 1);
    
    return Math.max(minRelevance, maxRelevance - index * decay);
  }
  
  /**
   * Extract title from URL
   */
  private extractTitleFromUrl(url: string): string {
    try {
      const urlObj = new URL(url);
      const path = urlObj.pathname;
      const lastSegment = path.split('/').filter(s => s.length > 0).pop();
      
      if (lastSegment) {
        return lastSegment
          .replace(/[-_]/g, ' ')
          .replace(/\.[^.]+$/, '') // Remove extension
          .split(' ')
          .map(w => w.charAt(0).toUpperCase() + w.slice(1))
          .join(' ');
      }
      
      return urlObj.hostname;
    } catch {
      return 'Unknown Title';
    }
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
 * Create a Jina AI provider instance
 */
export function createJinaProvider(timeout?: number): JinaProvider {
  return new JinaProvider(timeout);
}
