// REQ-ALERT-001, REQ-ALERT-002, REQ-ALERT-003: Alert entity
// Traces to: DES-ALERT-001, DES-ALERT-002, DES-ALERT-003

import type { DeviceId } from './device.js';

/**
 * Alert ID value object
 */
export interface AlertId {
  readonly value: string;
}

/**
 * Alert severity levels
 * @requirement REQ-ALERT-001
 */
export type AlertSeverity = 'low' | 'medium' | 'high' | 'critical';

/**
 * Alert status
 * @requirement REQ-ALERT-003
 */
export type AlertStatus = 'active' | 'acknowledged' | 'resolved';

/**
 * Comparison operator for alert rules
 */
export type ComparisonOperator = '>' | '>=' | '<' | '<=' | '==' | '!=';

/**
 * Alert rule input
 * @requirement REQ-ALERT-001
 */
export interface AlertRuleInput {
  name: string;
  deviceId?: string; // Optional: apply to specific device or all devices
  metric: string;
  operator: ComparisonOperator;
  threshold: number;
  severity: AlertSeverity;
  enabled?: boolean;
}

/**
 * Alert rule entity
 * @requirement REQ-ALERT-001
 */
export interface AlertRule {
  readonly id: string;
  name: string;
  deviceId?: DeviceId;
  metric: string;
  operator: ComparisonOperator;
  threshold: number;
  severity: AlertSeverity;
  enabled: boolean;
  createdAt: Date;
  version: number;
}

/**
 * Alert entity
 * @requirement REQ-ALERT-001, REQ-ALERT-003
 */
export interface Alert {
  readonly id: AlertId;
  ruleId: string;
  deviceId: DeviceId;
  severity: AlertSeverity;
  status: AlertStatus;
  message: string;
  value: number;
  threshold: number;
  triggeredAt: Date;
  acknowledgedAt?: Date;
  acknowledgedBy?: string;
  resolvedAt?: Date;
  version: number;
}

let alertRuleCounter = 0;
let alertCounter = 0;

/**
 * Reset counters (for testing)
 */
export function resetAlertCounters(): void {
  alertRuleCounter = 0;
  alertCounter = 0;
}

/**
 * Generate alert rule ID
 */
export function generateAlertRuleId(): string {
  alertRuleCounter++;
  return `RULE-${String(alertRuleCounter).padStart(4, '0')}`;
}

/**
 * Generate alert ID
 */
export function generateAlertId(): AlertId {
  alertCounter++;
  const ts = Date.now();
  const seq = String(alertCounter).padStart(4, '0');
  return { value: `ALERT-${ts}-${seq}` };
}

/**
 * Create alert rule
 * @requirement REQ-ALERT-001
 */
export function createAlertRule(input: AlertRuleInput): AlertRule {
  if (!input.name || input.name.length === 0) {
    throw new Error('Alert rule name is required');
  }
  if (!input.metric || input.metric.length === 0) {
    throw new Error('Metric is required');
  }
  if (typeof input.threshold !== 'number' || isNaN(input.threshold)) {
    throw new Error('Threshold must be a valid number');
  }

  const validOperators: ComparisonOperator[] = ['>', '>=', '<', '<=', '==', '!='];
  if (!validOperators.includes(input.operator)) {
    throw new Error(`Invalid operator: ${input.operator}`);
  }

  const validSeverities: AlertSeverity[] = ['low', 'medium', 'high', 'critical'];
  if (!validSeverities.includes(input.severity)) {
    throw new Error(`Invalid severity: ${input.severity}`);
  }

  return {
    id: generateAlertRuleId(),
    name: input.name,
    deviceId: input.deviceId ? { value: input.deviceId } : undefined,
    metric: input.metric,
    operator: input.operator,
    threshold: input.threshold,
    severity: input.severity,
    enabled: input.enabled ?? true,
    createdAt: new Date(),
    version: 1,
  };
}

/**
 * Evaluate if value triggers alert rule
 * @requirement REQ-ALERT-001
 */
export function evaluateAlertRule(rule: AlertRule, value: number): boolean {
  if (!rule.enabled) return false;

  switch (rule.operator) {
    case '>':
      return value > rule.threshold;
    case '>=':
      return value >= rule.threshold;
    case '<':
      return value < rule.threshold;
    case '<=':
      return value <= rule.threshold;
    case '==':
      return value === rule.threshold;
    case '!=':
      return value !== rule.threshold;
    default:
      return false;
  }
}

/**
 * Create alert from triggered rule
 * @requirement REQ-ALERT-001
 */
export function createAlert(
  rule: AlertRule,
  deviceId: DeviceId,
  value: number
): Alert {
  return {
    id: generateAlertId(),
    ruleId: rule.id,
    deviceId,
    severity: rule.severity,
    status: 'active',
    message: `${rule.metric} ${rule.operator} ${rule.threshold} (actual: ${value})`,
    value,
    threshold: rule.threshold,
    triggeredAt: new Date(),
    version: 1,
  };
}

/**
 * Valid alert status transitions
 * @requirement REQ-ALERT-003
 */
const validAlertStatusTransitions: Record<AlertStatus, AlertStatus[]> = {
  active: ['acknowledged', 'resolved'],
  acknowledged: ['resolved'],
  resolved: [], // Terminal state
};

/**
 * Acknowledge alert
 * @requirement REQ-ALERT-003
 */
export function acknowledgeAlert(alert: Alert, userId: string): Alert {
  if (alert.status !== 'active') {
    throw new Error(`Cannot acknowledge alert in '${alert.status}' status`);
  }

  return {
    ...alert,
    status: 'acknowledged',
    acknowledgedAt: new Date(),
    acknowledgedBy: userId,
    version: alert.version + 1,
  };
}

/**
 * Resolve alert
 * @requirement REQ-ALERT-003
 */
export function resolveAlert(alert: Alert): Alert {
  if (!validAlertStatusTransitions[alert.status].includes('resolved')) {
    throw new Error(`Cannot resolve alert in '${alert.status}' status`);
  }

  return {
    ...alert,
    status: 'resolved',
    resolvedAt: new Date(),
    version: alert.version + 1,
  };
}
