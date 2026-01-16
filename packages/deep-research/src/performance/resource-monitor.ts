/**
 * @fileoverview ResourceMonitor - Monitor memory and CPU usage
 * @module @nahisaho/musubix-deep-research/performance
 * @version 1.0.0
 * 
 * REQ: REQ-DR-NFR-004 (Performance Requirements)
 * TSK: TSK-DR-018 (ResourceMonitor Implementation)
 * ADR: ADR-v3.4.0-001 (Performance Optimization)
 */

import * as process from 'node:process';
import * as os from 'node:os';

/**
 * Memory usage snapshot
 */
export interface MemoryUsage {
  /** Heap used in bytes */
  heapUsed: number;
  /** Heap total in bytes */
  heapTotal: number;
  /** Resident set size in bytes */
  rss: number;
  /** External memory in bytes */
  external: number;
  /** Array buffers in bytes */
  arrayBuffers: number;
  /** Memory usage percentage (0-100) */
  percentage: number;
}

/**
 * CPU usage snapshot
 */
export interface CPUUsage {
  /** User CPU time in microseconds */
  user: number;
  /** System CPU time in microseconds */
  system: number;
  /** Total CPU time in microseconds */
  total: number;
  /** CPU usage percentage (0-100) */
  percentage: number;
}

/**
 * Resource snapshot
 */
export interface ResourceSnapshot {
  /** Timestamp of snapshot */
  timestamp: number;
  /** Memory usage */
  memory: MemoryUsage;
  /** CPU usage */
  cpu: CPUUsage;
  /** Uptime in seconds */
  uptime: number;
}

/**
 * Resource alert
 */
export interface ResourceAlert {
  /** Alert type */
  type: 'memory' | 'cpu';
  /** Alert level */
  level: 'warning' | 'critical';
  /** Current value */
  value: number;
  /** Threshold */
  threshold: number;
  /** Alert message */
  message: string;
  /** Timestamp */
  timestamp: number;
}

/**
 * ResourceMonitor options
 */
export interface ResourceMonitorOptions {
  /** Memory warning threshold (percentage, 0-100, default: 70) */
  memoryWarningThreshold?: number;
  /** Memory critical threshold (percentage, 0-100, default: 90) */
  memoryCriticalThreshold?: number;
  /** CPU warning threshold (percentage, 0-100, default: 70) */
  cpuWarningThreshold?: number;
  /** CPU critical threshold (percentage, 0-100, default: 90) */
  cpuCriticalThreshold?: number;
  /** Enable auto-monitoring (default: false) */
  autoMonitor?: boolean;
  /** Monitoring interval in milliseconds (default: 5000) */
  monitoringIntervalMs?: number;
}

/**
 * Alert callback
 */
export type AlertCallback = (alert: ResourceAlert) => void;

/**
 * ResourceMonitor - Monitor system resource usage
 * 
 * Features:
 * - Real-time memory monitoring
 * - CPU usage tracking
 * - Configurable thresholds
 * - Alert system
 * - Historical snapshots
 * 
 * @example
 * ```typescript
 * const monitor = new ResourceMonitor({
 *   memoryWarningThreshold: 70,
 *   memoryCriticalThreshold: 90,
 * });
 * 
 * monitor.onAlert((alert) => {
 *   console.warn(`⚠️  ${alert.message}`);
 * });
 * 
 * const snapshot = monitor.getSnapshot();
 * console.log(`Memory: ${snapshot.memory.percentage.toFixed(1)}%`);
 * console.log(`CPU: ${snapshot.cpu.percentage.toFixed(1)}%`);
 * ```
 */
export class ResourceMonitor {
  private readonly memoryWarningThreshold: number;
  private readonly memoryCriticalThreshold: number;
  private readonly cpuWarningThreshold: number;
  private readonly cpuCriticalThreshold: number;
  private readonly snapshots: ResourceSnapshot[] = [];
  private readonly alerts: ResourceAlert[] = [];
  private alertCallbacks: AlertCallback[] = [];
  private monitoringTimer?: NodeJS.Timeout;
  private previousCpuUsage?: NodeJS.CpuUsage;
  private previousTimestamp?: number;

  constructor(options: ResourceMonitorOptions = {}) {
    this.memoryWarningThreshold = options.memoryWarningThreshold ?? 70;
    this.memoryCriticalThreshold = options.memoryCriticalThreshold ?? 90;
    this.cpuWarningThreshold = options.cpuWarningThreshold ?? 70;
    this.cpuCriticalThreshold = options.cpuCriticalThreshold ?? 90;

    // Validate thresholds
    if (this.memoryWarningThreshold >= this.memoryCriticalThreshold) {
      throw new Error('memoryWarningThreshold must be less than memoryCriticalThreshold');
    }
    if (this.cpuWarningThreshold >= this.cpuCriticalThreshold) {
      throw new Error('cpuWarningThreshold must be less than cpuCriticalThreshold');
    }

    // Start auto-monitoring if enabled
    if (options.autoMonitor) {
      const interval = options.monitoringIntervalMs ?? 5000;
      this.startMonitoring(interval);
    }
  }

  /**
   * Get current resource snapshot
   */
  getSnapshot(): ResourceSnapshot {
    const timestamp = Date.now();
    const memory = this.getMemoryUsage();
    const cpu = this.getCPUUsage();
    const uptime = process.uptime();

    const snapshot: ResourceSnapshot = {
      timestamp,
      memory,
      cpu,
      uptime,
    };

    // Store snapshot
    this.snapshots.push(snapshot);

    // Check thresholds and emit alerts
    this.checkThresholds(snapshot);

    return snapshot;
  }

  /**
   * Get memory usage
   */
  private getMemoryUsage(): MemoryUsage {
    const memUsage = process.memoryUsage();
    const totalMemory = os.totalmem();
    const percentage = (memUsage.rss / totalMemory) * 100;

    return {
      heapUsed: memUsage.heapUsed,
      heapTotal: memUsage.heapTotal,
      rss: memUsage.rss,
      external: memUsage.external,
      arrayBuffers: memUsage.arrayBuffers,
      percentage,
    };
  }

  /**
   * Get CPU usage
   */
  private getCPUUsage(): CPUUsage {
    const currentUsage = process.cpuUsage(this.previousCpuUsage);
    const currentTime = Date.now();

    let percentage = 0;
    if (this.previousTimestamp) {
      const elapsedMs = currentTime - this.previousTimestamp;
      const elapsedUs = elapsedMs * 1000;
      const totalCpuUs = currentUsage.user + currentUsage.system;
      const cpuCount = os.cpus().length;
      percentage = (totalCpuUs / (elapsedUs * cpuCount)) * 100;
      percentage = Math.min(100, Math.max(0, percentage)); // Clamp to 0-100
    }

    this.previousCpuUsage = process.cpuUsage();
    this.previousTimestamp = currentTime;

    return {
      user: currentUsage.user,
      system: currentUsage.system,
      total: currentUsage.user + currentUsage.system,
      percentage,
    };
  }

  /**
   * Check resource thresholds and emit alerts
   */
  private checkThresholds(snapshot: ResourceSnapshot): void {
    // Check memory thresholds
    if (snapshot.memory.percentage >= this.memoryCriticalThreshold) {
      this.emitAlert({
        type: 'memory',
        level: 'critical',
        value: snapshot.memory.percentage,
        threshold: this.memoryCriticalThreshold,
        message: `Critical memory usage: ${snapshot.memory.percentage.toFixed(1)}% (threshold: ${this.memoryCriticalThreshold}%)`,
        timestamp: snapshot.timestamp,
      });
    } else if (snapshot.memory.percentage >= this.memoryWarningThreshold) {
      this.emitAlert({
        type: 'memory',
        level: 'warning',
        value: snapshot.memory.percentage,
        threshold: this.memoryWarningThreshold,
        message: `High memory usage: ${snapshot.memory.percentage.toFixed(1)}% (threshold: ${this.memoryWarningThreshold}%)`,
        timestamp: snapshot.timestamp,
      });
    }

    // Check CPU thresholds (skip if percentage is 0 due to first measurement)
    if (snapshot.cpu.percentage > 0) {
      if (snapshot.cpu.percentage >= this.cpuCriticalThreshold) {
        this.emitAlert({
          type: 'cpu',
          level: 'critical',
          value: snapshot.cpu.percentage,
          threshold: this.cpuCriticalThreshold,
          message: `Critical CPU usage: ${snapshot.cpu.percentage.toFixed(1)}% (threshold: ${this.cpuCriticalThreshold}%)`,
          timestamp: snapshot.timestamp,
        });
      } else if (snapshot.cpu.percentage >= this.cpuWarningThreshold) {
        this.emitAlert({
          type: 'cpu',
          level: 'warning',
          value: snapshot.cpu.percentage,
          threshold: this.cpuWarningThreshold,
          message: `High CPU usage: ${snapshot.cpu.percentage.toFixed(1)}% (threshold: ${this.cpuWarningThreshold}%)`,
          timestamp: snapshot.timestamp,
        });
      }
    }
  }

  /**
   * Emit alert to registered callbacks
   */
  private emitAlert(alert: ResourceAlert): void {
    this.alerts.push(alert);
    for (const callback of this.alertCallbacks) {
      try {
        callback(alert);
      } catch (error) {
        console.error('Alert callback error:', error);
      }
    }
  }

  /**
   * Register alert callback
   */
  onAlert(callback: AlertCallback): void {
    this.alertCallbacks.push(callback);
  }

  /**
   * Remove alert callback
   */
  offAlert(callback: AlertCallback): boolean {
    const index = this.alertCallbacks.indexOf(callback);
    if (index !== -1) {
      this.alertCallbacks.splice(index, 1);
      return true;
    }
    return false;
  }

  /**
   * Get all historical snapshots
   */
  getSnapshots(): ResourceSnapshot[] {
    return [...this.snapshots];
  }

  /**
   * Get all alerts
   */
  getAlerts(): ResourceAlert[] {
    return [...this.alerts];
  }

  /**
   * Clear historical data
   */
  clear(): void {
    this.snapshots.length = 0;
    this.alerts.length = 0;
  }

  /**
   * Start automatic monitoring
   */
  startMonitoring(intervalMs: number = 5000): void {
    if (this.monitoringTimer) {
      return; // Already monitoring
    }

    this.monitoringTimer = setInterval(() => {
      this.getSnapshot();
    }, intervalMs);

    // Prevent timer from keeping process alive
    if (this.monitoringTimer.unref) {
      this.monitoringTimer.unref();
    }
  }

  /**
   * Stop automatic monitoring
   */
  stopMonitoring(): void {
    if (this.monitoringTimer) {
      clearInterval(this.monitoringTimer);
      this.monitoringTimer = undefined;
    }
  }

  /**
   * Clean up resources
   */
  dispose(): void {
    this.stopMonitoring();
    this.alertCallbacks.length = 0;
    this.clear();
  }
}

/**
 * Create a ResourceMonitor instance
 */
export function createResourceMonitor(
  options?: ResourceMonitorOptions
): ResourceMonitor {
  return new ResourceMonitor(options);
}
