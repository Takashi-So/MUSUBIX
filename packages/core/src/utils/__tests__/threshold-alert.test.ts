/**
 * ThresholdAlert Tests
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  ThresholdAlert,
  MultiThresholdAlert,
  resourceUsageThreshold,
  inventoryThreshold,
  responseTimeThreshold,
  errorRateThreshold,
  capacityThreshold,
  batteryThreshold,
} from '../threshold-alert.js';

describe('ThresholdAlert', () => {
  describe('above direction (リソース使用率など)', () => {
    let alert: ThresholdAlert;

    beforeEach(() => {
      alert = new ThresholdAlert({
        warningThreshold: 80,
        criticalThreshold: 95,
        direction: 'above',
        name: 'CPU使用率',
        unit: '%',
      });
    });

    it('should return normal when below warning threshold', () => {
      expect(alert.check(50)).toBe('normal');
      expect(alert.check(79)).toBe('normal');
    });

    it('should return warning when at or above warning threshold', () => {
      expect(alert.check(80)).toBe('warning');
      expect(alert.check(85)).toBe('warning');
      expect(alert.check(94)).toBe('warning');
    });

    it('should return critical when at or above critical threshold', () => {
      expect(alert.check(95)).toBe('critical');
      expect(alert.check(100)).toBe('critical');
    });

    it('should evaluate with detailed result', () => {
      const result = alert.evaluate(85);
      expect(result.level).toBe('warning');
      expect(result.value).toBe(85);
      expect(result.threshold).toBe(80);
      expect(result.exceeded).toBe(true);
      expect(result.direction).toBe('above');
      expect(result.marginToWarning).toBe(-5); // 5超過
      expect(result.marginToCritical).toBe(10); // 10残り
      expect(result.message).toContain('WARNING');
    });

    it('should calculate percentage correctly', () => {
      const result = alert.evaluate(95);
      expect(result.percentage).toBe(100); // 95/95 = 100%
    });

    it('should generate appropriate messages', () => {
      expect(alert.evaluate(50).message).toContain('[OK]');
      expect(alert.evaluate(85).message).toContain('[WARNING]');
      expect(alert.evaluate(98).message).toContain('[CRITICAL]');
    });
  });

  describe('below direction (在庫数など)', () => {
    let alert: ThresholdAlert;

    beforeEach(() => {
      alert = new ThresholdAlert({
        warningThreshold: 10,
        criticalThreshold: 5,
        direction: 'below',
        name: '在庫数',
        unit: '個',
      });
    });

    it('should return normal when above warning threshold', () => {
      expect(alert.check(100)).toBe('normal');
      expect(alert.check(11)).toBe('normal');
    });

    it('should return warning when at or below warning threshold', () => {
      expect(alert.check(10)).toBe('warning');
      expect(alert.check(8)).toBe('warning');
      expect(alert.check(6)).toBe('warning');
    });

    it('should return critical when at or below critical threshold', () => {
      expect(alert.check(5)).toBe('critical');
      expect(alert.check(3)).toBe('critical');
      expect(alert.check(0)).toBe('critical');
    });

    it('should evaluate with detailed result', () => {
      const result = alert.evaluate(7);
      expect(result.level).toBe('warning');
      expect(result.value).toBe(7);
      expect(result.threshold).toBe(10);
      expect(result.exceeded).toBe(true);
      expect(result.direction).toBe('below');
      expect(result.marginToWarning).toBe(-3); // 3下回り
      expect(result.marginToCritical).toBe(2); // 2残り
    });
  });

  describe('isExceeded / isWarningOrAbove / isCritical', () => {
    const alert = new ThresholdAlert({
      warningThreshold: 80,
      criticalThreshold: 95,
      direction: 'above',
    });

    it('should check exceeded correctly', () => {
      expect(alert.isExceeded(50)).toBe(false);
      expect(alert.isExceeded(80)).toBe(true);
      expect(alert.isExceeded(95)).toBe(true);
    });

    it('should check warning or above correctly', () => {
      expect(alert.isWarningOrAbove(50)).toBe(false);
      expect(alert.isWarningOrAbove(80)).toBe(true);
      expect(alert.isWarningOrAbove(95)).toBe(true);
    });

    it('should check critical correctly', () => {
      expect(alert.isCritical(50)).toBe(false);
      expect(alert.isCritical(85)).toBe(false);
      expect(alert.isCritical(95)).toBe(true);
    });
  });

  describe('hysteresis (チャタリング防止)', () => {
    it('should apply hysteresis when level drops', () => {
      const alert = new ThresholdAlert({
        warningThreshold: 80,
        criticalThreshold: 95,
        direction: 'above',
        hysteresis: 5,
      });

      // 最初は警告レベル
      expect(alert.check(85)).toBe('warning');

      // ヒステリシスがあるので、75未満にならないと正常に戻らない
      expect(alert.check(78)).toBe('warning'); // 80-5=75より上なので維持
      expect(alert.check(74)).toBe('normal'); // 75未満なので正常に
    });
  });

  describe('validation', () => {
    it('should throw error for invalid above thresholds', () => {
      expect(() => {
        new ThresholdAlert({
          warningThreshold: 95,
          criticalThreshold: 80, // warning > critical は不正
          direction: 'above',
        });
      }).toThrow();
    });

    it('should throw error for invalid below thresholds', () => {
      expect(() => {
        new ThresholdAlert({
          warningThreshold: 5,
          criticalThreshold: 10, // warning < critical は不正
          direction: 'below',
        });
      }).toThrow();
    });
  });

  describe('getConfig', () => {
    it('should return current configuration', () => {
      const alert = new ThresholdAlert({
        warningThreshold: 80,
        criticalThreshold: 95,
        direction: 'above',
        name: 'test',
        unit: '%',
      });

      const config = alert.getConfig();
      expect(config.warningThreshold).toBe(80);
      expect(config.criticalThreshold).toBe(95);
      expect(config.direction).toBe('above');
      expect(config.name).toBe('test');
      expect(config.unit).toBe('%');
    });
  });
});

describe('MultiThresholdAlert', () => {
  let multi: MultiThresholdAlert;

  beforeEach(() => {
    multi = new MultiThresholdAlert();
    multi.register('cpu', {
      warningThreshold: 80,
      criticalThreshold: 95,
      direction: 'above',
    });
    multi.register('memory', {
      warningThreshold: 70,
      criticalThreshold: 90,
      direction: 'above',
    });
    multi.register('inventory', {
      warningThreshold: 10,
      criticalThreshold: 5,
      direction: 'below',
    });
  });

  it('should check individual alerts', () => {
    expect(multi.check('cpu', 50)).toBe('normal');
    expect(multi.check('cpu', 85)).toBe('warning');
    expect(multi.check('memory', 95)).toBe('critical');
  });

  it('should throw error for unregistered alert', () => {
    expect(() => multi.check('unknown', 50)).toThrow();
  });

  it('should evaluate all alerts with Map', () => {
    const values = new Map([
      ['cpu', 85],
      ['memory', 95],
      ['inventory', 7],
    ]);

    const result = multi.evaluateAll(values);

    expect(result.overallLevel).toBe('critical');
    expect(result.warningCount).toBe(2); // cpu + inventory
    expect(result.criticalCount).toBe(1); // memory
    expect(result.details.get('cpu')?.level).toBe('warning');
    expect(result.details.get('memory')?.level).toBe('critical');
    expect(result.details.get('inventory')?.level).toBe('warning');
  });

  it('should evaluate all alerts with object', () => {
    const values = {
      cpu: 50,
      memory: 60,
      inventory: 20,
    };

    const result = multi.evaluateAll(values);

    expect(result.overallLevel).toBe('normal');
    expect(result.warningCount).toBe(0);
    expect(result.criticalCount).toBe(0);
    expect(result.summary).toBe('All systems normal');
  });

  it('should return registered names', () => {
    const names = multi.getRegisteredNames();
    expect(names).toContain('cpu');
    expect(names).toContain('memory');
    expect(names).toContain('inventory');
    expect(names.length).toBe(3);
  });

  it('should unregister alerts', () => {
    multi.unregister('cpu');
    const names = multi.getRegisteredNames();
    expect(names).not.toContain('cpu');
    expect(names.length).toBe(2);
  });

  it('should generate appropriate summary', () => {
    const criticalResult = multi.evaluateAll({ cpu: 50, memory: 95 });
    expect(criticalResult.summary).toContain('critical');

    const warningResult = multi.evaluateAll({ cpu: 85, memory: 60 });
    expect(warningResult.summary).toContain('warning');
  });
});

describe('Preset Thresholds', () => {
  it('should have correct resourceUsageThreshold', () => {
    const alert = new ThresholdAlert(resourceUsageThreshold);
    expect(alert.check(50)).toBe('normal');
    expect(alert.check(85)).toBe('warning');
    expect(alert.check(98)).toBe('critical');
  });

  it('should have correct inventoryThreshold', () => {
    const alert = new ThresholdAlert(inventoryThreshold);
    expect(alert.check(50)).toBe('normal');
    expect(alert.check(8)).toBe('warning');
    expect(alert.check(3)).toBe('critical');
  });

  it('should have correct responseTimeThreshold', () => {
    const alert = new ThresholdAlert(responseTimeThreshold);
    expect(alert.check(500)).toBe('normal');
    expect(alert.check(1500)).toBe('warning');
    expect(alert.check(5000)).toBe('critical');
  });

  it('should have correct errorRateThreshold', () => {
    const alert = new ThresholdAlert(errorRateThreshold);
    expect(alert.check(0.5)).toBe('normal');
    expect(alert.check(2)).toBe('warning');
    expect(alert.check(10)).toBe('critical');
  });

  it('should have correct capacityThreshold', () => {
    const alert = new ThresholdAlert(capacityThreshold);
    expect(alert.check(50)).toBe('normal');
    expect(alert.check(85)).toBe('warning');
    expect(alert.check(98)).toBe('critical');
  });

  it('should have correct batteryThreshold', () => {
    const alert = new ThresholdAlert(batteryThreshold);
    expect(alert.check(50)).toBe('normal');
    expect(alert.check(15)).toBe('warning');
    expect(alert.check(3)).toBe('critical');
  });
});
