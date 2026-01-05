// Tests for Alert entity
// REQ-ALERT-001, REQ-ALERT-002, REQ-ALERT-003

import { describe, it, expect, beforeEach } from 'vitest';
import {
  createAlertRule,
  evaluateAlertRule,
  createAlert,
  acknowledgeAlert,
  resolveAlert,
  resetAlertCounters,
  type AlertRuleInput,
} from '../src/domain/alert.js';

describe('Alert', () => {
  beforeEach(() => {
    resetAlertCounters();
  });

  describe('createAlertRule', () => {
    it('should create alert rule with valid input', () => {
      const input: AlertRuleInput = {
        name: 'High Temperature Alert',
        deviceId: 'DEV-20250106-001',
        metric: 'temperature',
        operator: '>',
        threshold: 30,
        severity: 'high',
      };

      const rule = createAlertRule(input);

      expect(rule.id).toBe('RULE-0001');
      expect(rule.name).toBe('High Temperature Alert');
      expect(rule.deviceId?.value).toBe('DEV-20250106-001');
      expect(rule.metric).toBe('temperature');
      expect(rule.operator).toBe('>');
      expect(rule.threshold).toBe(30);
      expect(rule.severity).toBe('high');
      expect(rule.enabled).toBe(true);
      expect(rule.version).toBe(1);
    });

    it('should create rule without device ID (global rule)', () => {
      const input: AlertRuleInput = {
        name: 'Global Alert',
        metric: 'battery',
        operator: '<',
        threshold: 20,
        severity: 'medium',
      };

      const rule = createAlertRule(input);
      expect(rule.deviceId).toBeUndefined();
    });

    it('should create disabled rule', () => {
      const input: AlertRuleInput = {
        name: 'Test',
        metric: 'test',
        operator: '>',
        threshold: 0,
        severity: 'low',
        enabled: false,
      };

      const rule = createAlertRule(input);
      expect(rule.enabled).toBe(false);
    });

    it('should throw for empty name', () => {
      const input: AlertRuleInput = {
        name: '',
        metric: 'test',
        operator: '>',
        threshold: 0,
        severity: 'low',
      };

      expect(() => createAlertRule(input)).toThrow('name is required');
    });

    it('should throw for empty metric', () => {
      const input: AlertRuleInput = {
        name: 'Test',
        metric: '',
        operator: '>',
        threshold: 0,
        severity: 'low',
      };

      expect(() => createAlertRule(input)).toThrow('Metric is required');
    });

    it('should throw for invalid operator', () => {
      const input = {
        name: 'Test',
        metric: 'test',
        operator: '~' as any,
        threshold: 0,
        severity: 'low',
      };

      expect(() => createAlertRule(input)).toThrow('Invalid operator');
    });

    it('should throw for invalid severity', () => {
      const input = {
        name: 'Test',
        metric: 'test',
        operator: '>',
        threshold: 0,
        severity: 'extreme' as any,
      };

      expect(() => createAlertRule(input)).toThrow('Invalid severity');
    });
  });

  describe('evaluateAlertRule', () => {
    const baseInput: AlertRuleInput = {
      name: 'Test Rule',
      metric: 'temperature',
      operator: '>',
      threshold: 30,
      severity: 'high',
    };

    it('should evaluate > operator correctly', () => {
      const rule = createAlertRule({ ...baseInput, operator: '>' });
      expect(evaluateAlertRule(rule, 31)).toBe(true);
      expect(evaluateAlertRule(rule, 30)).toBe(false);
      expect(evaluateAlertRule(rule, 29)).toBe(false);
    });

    it('should evaluate >= operator correctly', () => {
      const rule = createAlertRule({ ...baseInput, operator: '>=' });
      expect(evaluateAlertRule(rule, 31)).toBe(true);
      expect(evaluateAlertRule(rule, 30)).toBe(true);
      expect(evaluateAlertRule(rule, 29)).toBe(false);
    });

    it('should evaluate < operator correctly', () => {
      const rule = createAlertRule({ ...baseInput, operator: '<' });
      expect(evaluateAlertRule(rule, 29)).toBe(true);
      expect(evaluateAlertRule(rule, 30)).toBe(false);
      expect(evaluateAlertRule(rule, 31)).toBe(false);
    });

    it('should evaluate <= operator correctly', () => {
      const rule = createAlertRule({ ...baseInput, operator: '<=' });
      expect(evaluateAlertRule(rule, 29)).toBe(true);
      expect(evaluateAlertRule(rule, 30)).toBe(true);
      expect(evaluateAlertRule(rule, 31)).toBe(false);
    });

    it('should evaluate == operator correctly', () => {
      const rule = createAlertRule({ ...baseInput, operator: '==' });
      expect(evaluateAlertRule(rule, 30)).toBe(true);
      expect(evaluateAlertRule(rule, 29)).toBe(false);
      expect(evaluateAlertRule(rule, 31)).toBe(false);
    });

    it('should evaluate != operator correctly', () => {
      const rule = createAlertRule({ ...baseInput, operator: '!=' });
      expect(evaluateAlertRule(rule, 29)).toBe(true);
      expect(evaluateAlertRule(rule, 31)).toBe(true);
      expect(evaluateAlertRule(rule, 30)).toBe(false);
    });

    it('should not trigger if rule is disabled', () => {
      const rule = createAlertRule({ ...baseInput, enabled: false });
      expect(evaluateAlertRule(rule, 100)).toBe(false);
    });
  });

  describe('createAlert', () => {
    it('should create alert from triggered rule', () => {
      const rule = createAlertRule({
        name: 'High Temp',
        metric: 'temperature',
        operator: '>',
        threshold: 30,
        severity: 'critical',
      });

      const deviceId = { value: 'DEV-20250106-001' };
      const alert = createAlert(rule, deviceId, 35);

      expect(alert.id.value).toMatch(/^ALERT-/);
      expect(alert.ruleId).toBe(rule.id);
      expect(alert.deviceId.value).toBe('DEV-20250106-001');
      expect(alert.severity).toBe('critical');
      expect(alert.status).toBe('active');
      expect(alert.value).toBe(35);
      expect(alert.threshold).toBe(30);
      expect(alert.message).toContain('temperature');
      expect(alert.message).toContain('35');
    });
  });

  describe('acknowledgeAlert', () => {
    it('should acknowledge active alert', () => {
      const rule = createAlertRule({
        name: 'Test',
        metric: 'test',
        operator: '>',
        threshold: 0,
        severity: 'low',
      });
      const alert = createAlert(rule, { value: 'DEV-20250106-001' }, 10);

      const acknowledged = acknowledgeAlert(alert, 'user-123');

      expect(acknowledged.status).toBe('acknowledged');
      expect(acknowledged.acknowledgedBy).toBe('user-123');
      expect(acknowledged.acknowledgedAt).toBeInstanceOf(Date);
      expect(acknowledged.version).toBe(2);
    });

    it('should throw if alert is not active', () => {
      const rule = createAlertRule({
        name: 'Test',
        metric: 'test',
        operator: '>',
        threshold: 0,
        severity: 'low',
      });
      const alert = createAlert(rule, { value: 'DEV-20250106-001' }, 10);
      const acknowledged = acknowledgeAlert(alert, 'user-123');

      expect(() => acknowledgeAlert(acknowledged, 'user-456')).toThrow(
        "Cannot acknowledge alert in 'acknowledged' status"
      );
    });
  });

  describe('resolveAlert', () => {
    it('should resolve active alert', () => {
      const rule = createAlertRule({
        name: 'Test',
        metric: 'test',
        operator: '>',
        threshold: 0,
        severity: 'low',
      });
      const alert = createAlert(rule, { value: 'DEV-20250106-001' }, 10);

      const resolved = resolveAlert(alert);

      expect(resolved.status).toBe('resolved');
      expect(resolved.resolvedAt).toBeInstanceOf(Date);
      expect(resolved.version).toBe(2);
    });

    it('should resolve acknowledged alert', () => {
      const rule = createAlertRule({
        name: 'Test',
        metric: 'test',
        operator: '>',
        threshold: 0,
        severity: 'low',
      });
      const alert = createAlert(rule, { value: 'DEV-20250106-001' }, 10);
      const acknowledged = acknowledgeAlert(alert, 'user-123');

      const resolved = resolveAlert(acknowledged);

      expect(resolved.status).toBe('resolved');
      expect(resolved.version).toBe(3);
    });

    it('should throw if alert is already resolved', () => {
      const rule = createAlertRule({
        name: 'Test',
        metric: 'test',
        operator: '>',
        threshold: 0,
        severity: 'low',
      });
      const alert = createAlert(rule, { value: 'DEV-20250106-001' }, 10);
      const resolved = resolveAlert(alert);

      expect(() => resolveAlert(resolved)).toThrow(
        "Cannot resolve alert in 'resolved' status"
      );
    });
  });
});
