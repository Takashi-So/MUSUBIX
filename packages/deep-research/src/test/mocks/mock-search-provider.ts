// Mock Search Provider for Testing
// TSK-DR-028
// REQ: 憲法Article III (Test-First)

import type { SearchProvider, SERPQuery, SearchResult } from '../../types/index.js';

/**
 * Mock Search Provider for unit testing
 * 
 * Usage:
 * ```typescript
 * const mockSearch = new MockSearchProvider('MyProvider');
 * mockSearch.setResults([
 *   { title: 'Result 1', url: 'https://example.com', snippet: '...' }
 * ]);
 * const results = await mockSearch.search(query);
 * ```
 */
export class MockSearchProvider implements SearchProvider {
  name: string;
  
  private results: SearchResult[] = [];
  private available = true;
  private callHistory: SERPQuery[] = [];
  private shouldFail = false;
  
  constructor(name: string = 'Mock Search Provider') {
    this.name = name;
  }
  
  /**
   * Set mock search results
   */
  setResults(results: SearchResult[]): void {
    this.results = results;
  }
  
  /**
   * Set availability status
   */
  setAvailable(available: boolean): void {
    this.available = available;
  }
  
  /**
   * Make next search call fail
   */
  setShouldFail(shouldFail: boolean): void {
    this.shouldFail = shouldFail;
  }
  
  /**
   * Search (mock implementation)
   */
  async search(query: SERPQuery): Promise<SearchResult[]> {
    this.callHistory.push(query);
    
    if (this.shouldFail) {
      throw new Error('Mock search provider: Simulated failure');
    }
    
    // Return up to topK results
    const topK = query.topK ?? 5;
    return this.results.slice(0, topK);
  }
  
  /**
   * Check availability
   */
  async isAvailable(): Promise<boolean> {
    return this.available;
  }
  
  /**
   * Get call history for assertions
   */
  getCallHistory(): SERPQuery[] {
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
    this.results = [];
    this.callHistory = [];
    this.available = true;
    this.shouldFail = false;
  }
  
  /**
   * Verify a query was made
   */
  wasQueryMade(keywordsSubstring: string): boolean {
    return this.callHistory.some(q => q.keywords.includes(keywordsSubstring));
  }
}

/**
 * Create mock search results
 */
export function createMockSearchResults(count: number): SearchResult[] {
  return Array.from({ length: count }, (_, i) => ({
    title: `Mock Result ${i + 1}`,
    url: `https://example.com/page${i + 1}`,
    snippet: `This is a mock search result snippet for result ${i + 1}`,
    date: new Date().toISOString(),
    relevance: 1 - (i * 0.1),
  }));
}
