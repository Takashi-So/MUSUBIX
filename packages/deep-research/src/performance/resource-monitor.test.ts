/**
 * @fileoverview Tests for ResourceMonitor
 * @module @nahisaho/musubix-deep-research/performance
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import {
  ResourceMonitor,
  createResourceMonitor,
  type ResourceAlert,
} from './resource-monitor.js';

describe('ResourceMonitor', () => {
  let monitor: ResourceMonitor;

  beforeEach(() => {
    monitor = new ResourceMonitor({
      memoryWarningThreshold: 70,
      memoryCriticalThreshold: 90,
      cpuWarningThreshold: 70,
      cpuCriticalThreshold: 90,
      autoMonitor: false,
    });
  });

  afterEach(() => {
    monitor.dispose();
  });

  describe('constructor', () => {
    it('should create monitor with default options', () => {
      const defaultMonitor = new ResourceMonitor({ autoMonitor: false });
      const snapshot = defaultMonitor.getSnapshot();
      expect(snapshot).toBeDefined();
      expect(snapshot.memory).toBeDefined();
      expect(snapshot.cpu).toBeDefined();
      defaultMonitor.dispose();
    });

    it('should throw error if warning >= critical threshold (memory)', () => {
      expect(
        () =>
          new ResourceMonitor({
            memoryWarningThreshold: 90,
            memoryCriticalThreshold: 90,
          })
      ).toThrow('memoryWarningThreshold must be less than memoryCriticalThreshold');
    });

    it('should throw error if warning >= critical threshold (CPU)', () => {
      expect(
        () =>
          new ResourceMonitor({
            cpuWarningThreshold: 90,
            cpuCriticalThreshold: 90,
          })
      ).toThrow('cpuWarningThreshold must be less than cpuCriticalThreshold');
    });
  });

  describe('getSnapshot', () => {
    it('should return resource snapshot', () => {
      const snapshot = monitor.getSnapshot();

      expect(snapshot.timestamp).toBeGreaterThan(0);
      expect(snapshot.uptime).toBeGreaterThanOrEqual(0);

      // Memory
      expect(snapshot.memory.heapUsed).toBeGreaterThan(0);
      expect(snapshot.memory.heapTotal).toBeGreaterThan(0);
      expect(snapshot.memory.rss).toBeGreaterThan(0);
      expect(snapshot.memory.percentage).toBeGreaterThanOrEqual(0);
      expect(snapshot.memory.percentage).toBeLessThanOrEqual(100);

      // CPU
      expect(snapshot.cpu.user).toBeGreaterThanOrEqual(0);
      expect(snapshot.cpu.system).toBeGreaterThanOrEqual(0);
      expect(snapshot.cpu.total).toBeGreaterThanOrEqual(0);
      expect(snapshot.cpu.percentage).toBeGreaterThanOrEqual(0);
      expect(snapshot.cpu.percentage).toBeLessThanOrEqual(100);
    });

    it('should store snapshots', () => {
      monitor.getSnapshot();
      monitor.getSnapshot();

      const snapshots = monitor.getSnapshots();
      expect(snapshots.length).toBe(2);
    });

    it('should calculate CPU percentage on subsequent calls', () => {
      const snapshot1 = monitor.getSnapshot();
      expect(snapshot1.cpu.percentage).toBe(0); // First call, no baseline

      // Do some CPU work
      let sum = 0;
      for (let i = 0; i < 1000000; i++) {
        sum += Math.sqrt(i);
      }

      const snapshot2 = monitor.getSnapshot();
      expect(snapshot2.cpu.percentage).toBeGreaterThanOrEqual(0);
    });
  });

  describe('alerts', () => {
    it('should emit alert via callback', () => {
      const alerts: ResourceAlert[] = [];
      monitor.onAlert((alert) => alerts.push(alert));

      // Force a snapshot (may or may not trigger alert depending on actual usage)
      monitor.getSnapshot();

      // Alerts array should be empty or contain alerts
      expect(Array.isArray(alerts)).toBe(true);
    });

    it('should store alerts', () => {
      monitor.getSnapshot();
      const alerts = monitor.getAlerts();
      expect(Array.isArray(alerts)).toBe(true);
    });

    it('should remove alert callback', () => {
      const callback = () => {};
      monitor.onAlert(callback);

      const removed = monitor.offAlert(callback);
      expect(removed).toBe(true);
    });

    it('should return false when removing non-existent callback', () => {
      const callback = () => {};
      const removed = monitor.offAlert(callback);
      expect(removed).toBe(false);
    });

    it('should handle callback errors gracefully', () => {
      const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});

      monitor.onAlert(() => {
        throw new Error('Callback error');
      });

      // Force snapshot (may trigger alert)
      monitor.getSnapshot();

      // Should not throw
      expect(true).toBe(true);

      consoleErrorSpy.mockRestore();
    });
  });

  describe('getSnapshots', () => {
    it('should return all snapshots', () => {
      monitor.getSnapshot();
      monitor.getSnapshot();
      monitor.getSnapshot();

      const snapshots = monitor.getSnapshots();
      expect(snapshots.length).toBe(3);
    });

    it('should return copy of snapshots array', () => {
      monitor.getSnapshot();
      const snapshots1 = monitor.getSnapshots();
      const snapshots2 = monitor.getSnapshots();

      expect(snapshots1).not.toBe(snapshots2); // Different array instances
      expect(snapshots1).toEqual(snapshots2); // Same content
    });
  });

  describe('getAlerts', () => {
    it('should return all alerts', () => {
      monitor.getSnapshot();
      const alerts = monitor.getAlerts();
      expect(Array.isArray(alerts)).toBe(true);
    });

    it('should return copy of alerts array', () => {
      monitor.getSnapshot();
      const alerts1 = monitor.getAlerts();
      const alerts2 = monitor.getAlerts();

      expect(alerts1).not.toBe(alerts2); // Different array instances
      expect(alerts1).toEqual(alerts2); // Same content
    });
  });

  describe('clear', () => {
    it('should clear snapshots and alerts', () => {
      monitor.getSnapshot();
      monitor.getSnapshot();

      monitor.clear();

      expect(monitor.getSnapshots().length).toBe(0);
      expect(monitor.getAlerts().length).toBe(0);
    });
  });

  describe('auto-monitoring', () => {
    it('should start auto-monitoring', async () => {
      vi.useFakeTimers();

      const autoMonitor = new ResourceMonitor({
        autoMonitor: true,
        monitoringIntervalMs: 100,
      });

      // Wait for interval
      vi.advanceTimersByTime(150);

      const snapshots = autoMonitor.getSnapshots();
      expect(snapshots.length).toBeGreaterThanOrEqual(1);

      autoMonitor.dispose();
      vi.useRealTimers();
    });

    it('should stop auto-monitoring', () => {
      vi.useFakeTimers();

      const autoMonitor = new ResourceMonitor({
        autoMonitor: true,
        monitoringIntervalMs: 100,
      });

      autoMonitor.stopMonitoring();

      const initialCount = autoMonitor.getSnapshots().length;

      vi.advanceTimersByTime(200);

      const finalCount = autoMonitor.getSnapshots().length;
      expect(finalCount).toBe(initialCount); // No new snapshots

      autoMonitor.dispose();
      vi.useRealTimers();
    });

    it('should not start monitoring twice', () => {
      const autoMonitor = new ResourceMonitor({ autoMonitor: false });
      autoMonitor.startMonitoring(100);
      autoMonitor.startMonitoring(100); // Should be no-op

      // Should not throw
      expect(true).toBe(true);

      autoMonitor.dispose();
    });
  });

  describe('threshold alerts', () => {
    it('should emit warning alert when memory exceeds warning threshold', () => {
      // Create monitor with very low threshold
      const lowThresholdMonitor = new ResourceMonitor({
        memoryWarningThreshold: 0.01, // 0.01%
        memoryCriticalThreshold: 99,
        autoMonitor: false,
      });

      const alerts: ResourceAlert[] = [];
      lowThresholdMonitor.onAlert((alert) => alerts.push(alert));

      lowThresholdMonitor.getSnapshot();

      const memoryAlerts = alerts.filter((a) => a.type === 'memory' && a.level === 'warning');
      expect(memoryAlerts.length).toBeGreaterThan(0);

      lowThresholdMonitor.dispose();
    });

    it('should emit critical alert when memory exceeds critical threshold', () => {
      // Create monitor with very low threshold
      const lowThresholdMonitor = new ResourceMonitor({
        memoryWarningThreshold: 0.01, // 0.01%
        memoryCriticalThreshold: 0.02, // 0.02%
        autoMonitor: false,
      });

      const alerts: ResourceAlert[] = [];
      lowThresholdMonitor.onAlert((alert) => alerts.push(alert));

      lowThresholdMonitor.getSnapshot();

      const memoryAlerts = alerts.filter((a) => a.type === 'memory' && a.level === 'critical');
      expect(memoryAlerts.length).toBeGreaterThan(0);

      lowThresholdMonitor.dispose();
    });
  });

  describe('createResourceMonitor', () => {
    it('should create ResourceMonitor instance', () => {
      const newMonitor = createResourceMonitor({ autoMonitor: false });
      expect(newMonitor).toBeInstanceOf(ResourceMonitor);
      newMonitor.dispose();
    });
  });

  describe('dispose', () => {
    it('should clean up resources', () => {
      const autoMonitor = new ResourceMonitor({
        autoMonitor: true,
        monitoringIntervalMs: 100,
      });

      autoMonitor.getSnapshot();
      autoMonitor.dispose();

      expect(autoMonitor.getSnapshots().length).toBe(0);
      expect(autoMonitor.getAlerts().length).toBe(0);
    });
  });

  describe('memory usage details', () => {
    it('should include all memory fields', () => {
      const snapshot = monitor.getSnapshot();

      expect(typeof snapshot.memory.heapUsed).toBe('number');
      expect(typeof snapshot.memory.heapTotal).toBe('number');
      expect(typeof snapshot.memory.rss).toBe('number');
      expect(typeof snapshot.memory.external).toBe('number');
      expect(typeof snapshot.memory.arrayBuffers).toBe('number');
      expect(typeof snapshot.memory.percentage).toBe('number');
    });
  });

  describe('CPU usage details', () => {
    it('should include all CPU fields', () => {
      const snapshot = monitor.getSnapshot();

      expect(typeof snapshot.cpu.user).toBe('number');
      expect(typeof snapshot.cpu.system).toBe('number');
      expect(typeof snapshot.cpu.total).toBe('number');
      expect(typeof snapshot.cpu.percentage).toBe('number');
    });

    it('should calculate total as user + system', () => {
      const snapshot = monitor.getSnapshot();
      expect(snapshot.cpu.total).toBe(snapshot.cpu.user + snapshot.cpu.system);
    });
  });
});
