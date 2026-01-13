/**
 * Time Constraint Patterns
 *
 * Best practice patterns for time-based operations.
 *
 * @packageDocumentation
 * @module patterns/time
 *
 * @see BP-DESIGN-007 - Expiry Time Logic
 * @see TSK-PAT-002 - 時間制約パターン
 */

import type { DesignPattern, PatternExample } from '../../types.js';

/**
 * PAT-TIME-001: Expiry Pattern
 *
 * Manages entities with expiration times.
 */
export const EXPIRY_PATTERN: DesignPattern = {
  id: 'PAT-TIME-001',
  name: 'Expiry Pattern',
  category: 'temporal',
  domain: ['all'],
  description:
    'Manages entities with explicit expiration times. Use expiresAt field to track validity.',
  problem:
    'Entities need to become invalid after a certain time (e.g., tokens, coupons, sessions).',
  solution:
    'Store expiresAt as a Date field. Provide isExpired() method that compares against current time.',
  applicability: [
    'Tokens and sessions',
    'Coupons and promotions',
    'Temporary access',
    'Cache entries',
  ],
  consequences: {
    positive: [
      'Clear expiration semantics',
      'Easy to query expired entities',
      'Timezone-safe with UTC',
    ],
    negative: [
      'Requires periodic cleanup jobs',
      'Clock synchronization needed for distributed systems',
    ],
  },
  implementation: `interface Expirable {
  readonly expiresAt: Date;
}

function isExpired(entity: Expirable, now: Date = new Date()): boolean {
  return entity.expiresAt <= now;
}

function createExpiry(durationMs: number, from: Date = new Date()): Date {
  return new Date(from.getTime() + durationMs);
}`,
  relatedPatterns: ['PAT-TIME-002', 'PAT-TIME-003'],
  confidence: 0.9,
};

/**
 * PAT-TIME-002: Scheduled Event Pattern
 *
 * Handles events that occur at specific times.
 */
export const SCHEDULED_PATTERN: DesignPattern = {
  id: 'PAT-TIME-002',
  name: 'Scheduled Event Pattern',
  category: 'temporal',
  domain: ['all'],
  description:
    'Manages events scheduled for future execution at specific times.',
  problem:
    'Need to execute actions at predetermined times (e.g., reminders, appointments).',
  solution:
    'Store scheduledAt timestamp. Use job queue to trigger actions when time arrives.',
  applicability: [
    'Appointment systems',
    'Reminder notifications',
    'Scheduled publishing',
    'Delayed tasks',
  ],
  consequences: {
    positive: [
      'Predictable execution timing',
      'Supports multiple time zones',
      'Can reschedule easily',
    ],
    negative: [
      'Requires reliable scheduler',
      'Missed events need handling strategy',
    ],
  },
  implementation: `interface Schedulable {
  readonly scheduledAt: Date;
  readonly status: 'pending' | 'executed' | 'cancelled';
}

function isReady(event: Schedulable, now: Date = new Date()): boolean {
  return event.status === 'pending' && event.scheduledAt <= now;
}

function reschedule(event: Schedulable, newTime: Date): Schedulable {
  if (event.status !== 'pending') {
    throw new Error('Cannot reschedule non-pending event');
  }
  return { ...event, scheduledAt: newTime };
}`,
  relatedPatterns: ['PAT-TIME-001', 'PAT-TIME-003'],
  confidence: 0.85,
};

/**
 * PAT-TIME-003: Interval Pattern
 *
 * Manages recurring events at fixed intervals.
 */
export const INTERVAL_PATTERN: DesignPattern = {
  id: 'PAT-TIME-003',
  name: 'Interval Pattern',
  category: 'temporal',
  domain: ['all'],
  description:
    'Manages recurring events that happen at fixed intervals.',
  problem:
    'Events need to repeat periodically (e.g., subscriptions, polling, cron jobs).',
  solution:
    'Store intervalMs and lastRunAt. Calculate nextRunAt from last execution.',
  applicability: [
    'Subscription billing',
    'Recurring tasks',
    'Health checks',
    'Data synchronization',
  ],
  consequences: {
    positive: [
      'Consistent timing',
      'Easy to adjust frequency',
      'Tracks execution history',
    ],
    negative: [
      'Drift accumulation if not anchored',
      'Overlapping executions need handling',
    ],
  },
  implementation: `interface Recurring {
  readonly intervalMs: number;
  readonly lastRunAt: Date | null;
  readonly anchorTime: Date;
}

function getNextRunAt(recurring: Recurring, now: Date = new Date()): Date {
  if (!recurring.lastRunAt) {
    return recurring.anchorTime;
  }
  const elapsed = now.getTime() - recurring.anchorTime.getTime();
  const periods = Math.floor(elapsed / recurring.intervalMs) + 1;
  return new Date(recurring.anchorTime.getTime() + periods * recurring.intervalMs);
}

function isDue(recurring: Recurring, now: Date = new Date()): boolean {
  const next = getNextRunAt(recurring, now);
  return next <= now;
}`,
  relatedPatterns: ['PAT-TIME-001', 'PAT-TIME-002', 'PAT-TIME-004'],
  confidence: 0.85,
};

/**
 * PAT-TIME-004: Streak Pattern
 *
 * Tracks consecutive activity streaks.
 */
export const STREAK_PATTERN: DesignPattern = {
  id: 'PAT-TIME-004',
  name: 'Streak Pattern',
  category: 'temporal',
  domain: ['fitness', 'education', 'gaming'],
  description:
    'Tracks consecutive day/activity streaks with grace period support.',
  problem:
    'Need to track user engagement through consecutive activity days (e.g., login streaks, workout streaks).',
  solution:
    'Store currentStreak, longestStreak, lastActivityAt. Update on each activity with grace period.',
  applicability: [
    'Gamification features',
    'Habit tracking',
    'User engagement metrics',
    'Loyalty programs',
  ],
  consequences: {
    positive: [
      'Motivates consistent engagement',
      'Clear progress tracking',
      'Supports grace periods',
    ],
    negative: [
      'Timezone handling complexity',
      'Grace period edge cases',
    ],
  },
  implementation: `interface Streak {
  currentStreak: number;
  longestStreak: number;
  lastActivityAt: Date | null;
}

const ONE_DAY_MS = 24 * 60 * 60 * 1000;

function recordActivity(
  streak: Streak,
  gracePeriodMs: number = ONE_DAY_MS * 1.5,
  now: Date = new Date()
): Streak {
  if (!streak.lastActivityAt) {
    return {
      currentStreak: 1,
      longestStreak: Math.max(1, streak.longestStreak),
      lastActivityAt: now,
    };
  }

  const elapsed = now.getTime() - streak.lastActivityAt.getTime();

  if (elapsed < ONE_DAY_MS) {
    // Same day, no change
    return streak;
  } else if (elapsed <= gracePeriodMs) {
    // Within grace period, increment streak
    const newCurrent = streak.currentStreak + 1;
    return {
      currentStreak: newCurrent,
      longestStreak: Math.max(newCurrent, streak.longestStreak),
      lastActivityAt: now,
    };
  } else {
    // Streak broken
    return {
      currentStreak: 1,
      longestStreak: streak.longestStreak,
      lastActivityAt: now,
    };
  }
}`,
  relatedPatterns: ['PAT-TIME-003'],
  confidence: 0.8,
};

/**
 * PAT-TIME-005: Cooldown Pattern
 *
 * Prevents actions from being repeated too quickly.
 */
export const COOLDOWN_PATTERN: DesignPattern = {
  id: 'PAT-TIME-005',
  name: 'Cooldown Pattern',
  category: 'temporal',
  domain: ['all'],
  description:
    'Prevents actions from being performed too frequently with a cooldown period.',
  problem:
    'Need to rate-limit user actions (e.g., password reset, notifications, API calls).',
  solution:
    'Track lastActionAt and cooldownMs. Check if enough time has passed before allowing action.',
  applicability: [
    'Rate limiting',
    'Spam prevention',
    'Resource protection',
    'Gaming abilities',
  ],
  consequences: {
    positive: [
      'Prevents abuse',
      'Fair resource distribution',
      'Simple implementation',
    ],
    negative: [
      'May frustrate legitimate users',
      'Clock skew issues in distributed systems',
    ],
  },
  implementation: `interface Cooldownable {
  readonly lastActionAt: Date | null;
  readonly cooldownMs: number;
}

function canPerformAction(
  item: Cooldownable,
  now: Date = new Date()
): { allowed: boolean; remainingMs: number } {
  if (!item.lastActionAt) {
    return { allowed: true, remainingMs: 0 };
  }

  const elapsed = now.getTime() - item.lastActionAt.getTime();
  const remaining = item.cooldownMs - elapsed;

  return {
    allowed: remaining <= 0,
    remainingMs: Math.max(0, remaining),
  };
}

function performAction(item: Cooldownable, now: Date = new Date()): Cooldownable {
  const check = canPerformAction(item, now);
  if (!check.allowed) {
    throw new Error(\`Action on cooldown. Wait \${check.remainingMs}ms\`);
  }
  return { ...item, lastActionAt: now };
}`,
  relatedPatterns: ['PAT-TIME-001', 'PAT-CONC-004'],
  confidence: 0.85,
};

/**
 * All time constraint patterns
 */
export const TIME_PATTERNS: DesignPattern[] = [
  EXPIRY_PATTERN,
  SCHEDULED_PATTERN,
  INTERVAL_PATTERN,
  STREAK_PATTERN,
  COOLDOWN_PATTERN,
];

/**
 * Get a time pattern by ID
 */
export function getTimePattern(id: string): DesignPattern | undefined {
  return TIME_PATTERNS.find((p) => p.id === id);
}

/**
 * Get patterns applicable to a domain
 */
export function getTimePatternsByDomain(domain: string): DesignPattern[] {
  return TIME_PATTERNS.filter(
    (p) => p.domain.includes('all') || p.domain.includes(domain)
  );
}

/**
 * Pattern examples for time patterns
 */
export const TIME_PATTERN_EXAMPLES: PatternExample[] = [
  {
    patternId: 'PAT-TIME-001',
    scenario: 'クーポンの有効期限管理',
    code: `const coupon = {
  code: 'SUMMER2025',
  discount: 20,
  expiresAt: new Date('2025-08-31T23:59:59Z'),
};

if (isExpired(coupon)) {
  throw new Error('このクーポンは有効期限切れです');
}`,
    domain: 'ecommerce',
  },
  {
    patternId: 'PAT-TIME-002',
    scenario: '予約のスケジュール管理',
    code: `const appointment = {
  id: 'APT-001',
  scheduledAt: new Date('2025-01-20T10:00:00Z'),
  status: 'pending' as const,
};

if (isReady(appointment)) {
  sendReminder(appointment);
}`,
    domain: 'healthcare',
  },
  {
    patternId: 'PAT-TIME-004',
    scenario: 'フィットネスアプリの連続記録',
    code: `let streak: Streak = {
  currentStreak: 5,
  longestStreak: 10,
  lastActivityAt: new Date('2025-01-18'),
};

streak = recordActivity(streak);
console.log(\`現在の連続: \${streak.currentStreak}日\`);`,
    domain: 'fitness',
  },
];
