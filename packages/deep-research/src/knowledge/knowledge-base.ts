// Knowledge Base - Repository Pattern
// TSK-DR-002
// REQ: REQ-DR-CORE-008

import type { KnowledgeItem } from '../types/index.js';

/**
 * Knowledge Base for storing research findings
 * 
 * Uses Repository Pattern for knowledge management.
 * 
 * REQ: REQ-DR-CORE-008 - Knowledge accumulation across iterations
 */
export class KnowledgeBase {
  private items: Map<string, KnowledgeItem> = new Map();
  private iterationIndex: Map<number, string[]> = new Map();
  
  /**
   * Add a single knowledge item
   */
  add(item: KnowledgeItem): void {
    const id = this.generateId();
    item.id = id;
    
    this.items.set(id, item);
    
    // Index by iteration
    if (typeof item.iteration === 'number') {
      const iterationItems = this.iterationIndex.get(item.iteration) || [];
      iterationItems.push(id);
      this.iterationIndex.set(item.iteration, iterationItems);
    }
  }
  
  /**
   * Add multiple knowledge items
   */
  addAll(items: KnowledgeItem[]): void {
    for (const item of items) {
      this.add(item);
    }
  }
  
  /**
   * Get all findings (facts only), sorted by relevance
   */
  getFindings(): KnowledgeItem[] {
    return Array.from(this.items.values())
      .filter(item => item.type === 'fact')
      .sort((a, b) => b.relevance - a.relevance);
  }
  
  /**
   * Get knowledge items from a specific iteration
   */
  getByIteration(iteration: number): KnowledgeItem[] {
    const ids = this.iterationIndex.get(iteration) || [];
    return ids.map(id => this.items.get(id)!).filter(Boolean);
  }
  
  /**
   * Get total number of knowledge items
   */
  size(): number {
    return this.items.size;
  }
  
  /**
   * Get summary of top knowledge items (for LM prompts)
   */
  getSummary(maxItems: number = 10): string {
    const topItems = Array.from(this.items.values())
      .sort((a, b) => b.relevance - a.relevance)
      .slice(0, maxItems);
    
    if (topItems.length === 0) {
      return '(No knowledge accumulated yet)';
    }
    
    return topItems
      .map(item => `- [${item.type}] ${item.content}`)
      .join('\n');
  }
  
  /**
   * Get all knowledge items
   */
  getAll(): KnowledgeItem[] {
    return Array.from(this.items.values());
  }
  
  /**
   * Clear all knowledge
   */
  clear(): void {
    this.items.clear();
    this.iterationIndex.clear();
  }
  
  /**
   * Generate unique ID for knowledge item
   */
  private generateId(): string {
    return `knowledge-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
  }
}
