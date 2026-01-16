// Token Tracker - Budget Management
// TSK-DR-003
// REQ: REQ-DR-CORE-006

import { TokenBudgetExceededError } from '../types/errors.js';
import type { TokenUsage } from '../types/index.js';

/**
 * Token Tracker for LM API budget management
 * 
 * REQ: REQ-DR-CORE-006 - Token budget tracking and limits
 * - 80% warning threshold
 * - 100% error threshold
 */
export class TokenTracker {
  private usages: TokenUsage[] = [];
  private budget: number;
  private warningEmitted = false;
  
  constructor(budget: number) {
    if (budget <= 0) {
      throw new Error('Token budget must be positive');
    }
    this.budget = budget;
  }
  
  /**
   * Track token usage for an operation
   * 
   * @throws TokenBudgetExceededError when budget is exceeded
   */
  trackUsage(operation: string, tokens: number): void {
    this.usages.push({
      operation,
      tokens,
      timestamp: Date.now(),
    });
    
    const used = this.getUsed();
    
    // 100% error (REQ: REQ-DR-CORE-006) - Check BEFORE adding tokens
    if (used > this.budget) {
      throw new TokenBudgetExceededError(used, this.budget);
    }
    
    // 80% warning (REQ: REQ-DR-CORE-006)
    if (used >= this.budget * 0.8 && !this.warningEmitted) {
      console.warn(`⚠️  Token budget 80% consumed (${used}/${this.budget} tokens)`);
      this.warningEmitted = true;
    }
  }
  
  /**
   * Get total tokens used
   */
  getUsed(): number {
    return this.usages.reduce((sum, u) => sum + u.tokens, 0);
  }
  
  /**
   * Get remaining token budget
   */
  getRemaining(): number {
    return Math.max(0, this.budget - this.getUsed());
  }
  
  /**
   * Check if budget is exceeded
   */
  isExceeded(): boolean {
    return this.getUsed() > this.budget;
  }
  
  /**
   * Get token usage breakdown by operation
   */
  getBreakdown(): Record<string, number> {
    const breakdown: Record<string, number> = {};
    
    for (const usage of this.usages) {
      breakdown[usage.operation] = (breakdown[usage.operation] || 0) + usage.tokens;
    }
    
    return breakdown;
  }
  
  /**
   * Get all usage records
   */
  getUsages(): TokenUsage[] {
    return [...this.usages];
  }
  
  /**
   * Get budget
   */
  getBudget(): number {
    return this.budget;
  }
}
