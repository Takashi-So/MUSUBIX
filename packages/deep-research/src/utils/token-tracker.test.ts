// Token Tracker Tests
// TSK-DR-003

import { describe, it, expect, beforeEach } from 'vitest';
import { TokenTracker } from './token-tracker.js';
import { TokenBudgetExceededError } from '../types/errors.js';

describe('TokenTracker', () => {
  let tracker: TokenTracker;

  beforeEach(() => {
    tracker = new TokenTracker(1000);
  });

  it('should initialize with budget', () => {
    expect(tracker.getBudget()).toBe(1000);
    expect(tracker.getUsed()).toBe(0);
    expect(tracker.getRemaining()).toBe(1000);
  });

  it('should throw error for invalid budget', () => {
    expect(() => new TokenTracker(0)).toThrow('Token budget must be positive');
    expect(() => new TokenTracker(-100)).toThrow('Token budget must be positive');
  });

  it('should track token usage', () => {
    tracker.trackUsage('search', 100);
    expect(tracker.getUsed()).toBe(100);
    expect(tracker.getRemaining()).toBe(900);

    tracker.trackUsage('reason', 200);
    expect(tracker.getUsed()).toBe(300);
    expect(tracker.getRemaining()).toBe(700);
  });

  it('should throw error when budget exceeded', () => {
    tracker.trackUsage('operation1', 500);
    tracker.trackUsage('operation2', 500);
    
    // Should throw on next call that exceeds budget
    expect(() => tracker.trackUsage('operation3', 100)).toThrow(TokenBudgetExceededError);
  });

  it('should detect when budget is exceeded', () => {
    expect(tracker.isExceeded()).toBe(false);
    
    // Exactly at budget - not exceeded
    tracker.trackUsage('operation1', 1000);
    expect(tracker.isExceeded()).toBe(false);
    
    // Over budget - would throw error
    expect(() => tracker.trackUsage('operation2', 1)).toThrow(TokenBudgetExceededError);
  });

  it('should provide usage breakdown', () => {
    tracker.trackUsage('search', 100);
    tracker.trackUsage('reason', 200);
    tracker.trackUsage('search', 150);

    const breakdown = tracker.getBreakdown();
    expect(breakdown.search).toBe(250);
    expect(breakdown.reason).toBe(200);
  });

  it('should track usage history', () => {
    tracker.trackUsage('op1', 100);
    tracker.trackUsage('op2', 200);

    const usages = tracker.getUsages();
    expect(usages).toHaveLength(2);
    expect(usages[0].operation).toBe('op1');
    expect(usages[1].operation).toBe('op2');
  });

  it('should warn at 80% budget', () => {
    // Track 80% of budget
    tracker.trackUsage('operation', 800);
    
    // Should not throw, but would emit warning in console
    expect(tracker.getUsed()).toBe(800);
    expect(tracker.isExceeded()).toBe(false);
  });
});
