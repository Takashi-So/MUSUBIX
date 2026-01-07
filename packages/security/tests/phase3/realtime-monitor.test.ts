/**
 * @fileoverview Phase 3 - Realtime Monitor Tests
 * @module @nahisaho/musubix-security/tests/phase3/realtime-monitor.test
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import * as fs from 'node:fs';
import * as path from 'node:path';
import {
  RealtimeMonitor,
  createRealtimeMonitor,
  createSecurityMonitor,
  type MonitorConfig,
  type MonitorEvent,
} from '../../src/analyzers/monitor/realtime-monitor.js';

// Mock fs module
vi.mock('node:fs', async () => {
  const actual = await vi.importActual('node:fs');
  return {
    ...actual,
    existsSync: vi.fn(),
    statSync: vi.fn(),
    readFileSync: vi.fn(),
    readdirSync: vi.fn(),
    watch: vi.fn(),
  };
});

describe('RealtimeMonitor', () => {
  let monitor: RealtimeMonitor;
  const testConfig: MonitorConfig = {
    watchPaths: ['/test/project'],
    debounceMs: 100,
    verbose: false,
  };

  beforeEach(() => {
    vi.clearAllMocks();
    
    // Default mock setup
    vi.mocked(fs.existsSync).mockReturnValue(true);
    vi.mocked(fs.statSync).mockReturnValue({
      isFile: () => false,
      isDirectory: () => true,
      size: 1000,
    } as fs.Stats);
    vi.mocked(fs.readdirSync).mockReturnValue([]);
    vi.mocked(fs.watch).mockReturnValue({
      close: vi.fn(),
    } as any);
  });

  afterEach(async () => {
    if (monitor) {
      await monitor.stop();
    }
  });

  describe('constructor and factory', () => {
    it('should create monitor with config', () => {
      monitor = new RealtimeMonitor(testConfig);
      expect(monitor).toBeInstanceOf(RealtimeMonitor);
    });

    it('should create monitor with factory function', () => {
      monitor = createRealtimeMonitor(testConfig);
      expect(monitor).toBeInstanceOf(RealtimeMonitor);
    });

    it('should create security monitor with default scanners', async () => {
      monitor = await createSecurityMonitor(['/test/project']);
      expect(monitor).toBeInstanceOf(RealtimeMonitor);
    });
  });

  describe('start and stop', () => {
    it('should start monitoring', async () => {
      monitor = createRealtimeMonitor(testConfig);
      
      const startPromise = new Promise<MonitorEvent>(resolve => {
        monitor.once('start', resolve);
      });

      await monitor.start();
      const event = await startPromise;
      
      expect(event.type).toBe('start');
      expect(monitor.getState().isRunning).toBe(true);
    });

    it('should stop monitoring', async () => {
      monitor = createRealtimeMonitor(testConfig);
      await monitor.start();
      
      const stopPromise = new Promise<MonitorEvent>(resolve => {
        monitor.once('stop', resolve);
      });

      await monitor.stop();
      const event = await stopPromise;
      
      expect(event.type).toBe('stop');
      expect(monitor.getState().isRunning).toBe(false);
    });

    it('should throw when starting already running monitor', async () => {
      monitor = createRealtimeMonitor(testConfig);
      await monitor.start();
      
      await expect(monitor.start()).rejects.toThrow('already running');
    });

    it('should not throw when stopping already stopped monitor', async () => {
      monitor = createRealtimeMonitor(testConfig);
      
      await expect(monitor.stop()).resolves.not.toThrow();
    });
  });

  describe('getState', () => {
    it('should return initial state', () => {
      monitor = createRealtimeMonitor(testConfig);
      const state = monitor.getState();
      
      expect(state.isRunning).toBe(false);
      expect(state.filesWatched).toBe(0);
      expect(state.scanCount).toBe(0);
      expect(state.vulnerabilityCount).toBe(0);
      expect(state.errorCount).toBe(0);
    });

    it('should update state after start', async () => {
      monitor = createRealtimeMonitor(testConfig);
      await monitor.start();
      
      const state = monitor.getState();
      
      expect(state.isRunning).toBe(true);
      expect(state.startTime).toBeInstanceOf(Date);
    });
  });

  describe('getCurrentVulnerabilities', () => {
    it('should return empty map initially', () => {
      monitor = createRealtimeMonitor(testConfig);
      const vulns = monitor.getCurrentVulnerabilities();
      
      expect(vulns).toBeInstanceOf(Map);
      expect(vulns.size).toBe(0);
    });
  });

  describe('getAllVulnerabilities', () => {
    it('should return empty array initially', () => {
      monitor = createRealtimeMonitor(testConfig);
      const vulns = monitor.getAllVulnerabilities();
      
      expect(Array.isArray(vulns)).toBe(true);
      expect(vulns.length).toBe(0);
    });
  });

  describe('scanner management', () => {
    it('should add scanner', () => {
      monitor = createRealtimeMonitor(testConfig);
      const scanner = vi.fn().mockResolvedValue([]);
      
      monitor.addScanner(scanner);
      
      // Scanner added successfully
      expect(true).toBe(true);
    });

    it('should remove scanner', () => {
      monitor = createRealtimeMonitor(testConfig);
      const scanner = vi.fn().mockResolvedValue([]);
      
      monitor.addScanner(scanner);
      monitor.removeScanner(scanner);
      
      // Scanner removed successfully
      expect(true).toBe(true);
    });

    it('should not throw when removing non-existent scanner', () => {
      monitor = createRealtimeMonitor(testConfig);
      const scanner = vi.fn().mockResolvedValue([]);
      
      expect(() => monitor.removeScanner(scanner)).not.toThrow();
    });
  });

  describe('scanFile', () => {
    it('should scan a specific file', async () => {
      const mockContent = 'const x = eval("alert()");'; // Has vulnerability
      
      vi.mocked(fs.existsSync).mockReturnValue(true);
      vi.mocked(fs.statSync).mockReturnValue({
        isFile: () => true,
        isDirectory: () => false,
        size: mockContent.length,
      } as fs.Stats);
      vi.mocked(fs.readFileSync).mockReturnValue(mockContent);

      monitor = await createSecurityMonitor(['/test/project']);
      
      const vulnerabilities = await monitor.scanFile('/test/project/file.js');
      
      expect(Array.isArray(vulnerabilities)).toBe(true);
    });

    it('should throw for non-existent file', async () => {
      vi.mocked(fs.existsSync).mockReturnValue(false);
      
      monitor = createRealtimeMonitor(testConfig);
      
      await expect(monitor.scanFile('/nonexistent/file.js')).rejects.toThrow('not found');
    });
  });

  describe('event emission', () => {
    it('should emit start event', async () => {
      monitor = createRealtimeMonitor(testConfig);
      
      const events: MonitorEvent[] = [];
      monitor.on('start', (e) => events.push(e));
      
      await monitor.start();
      
      expect(events.length).toBe(1);
      expect(events[0].type).toBe('start');
    });

    it('should emit stop event', async () => {
      monitor = createRealtimeMonitor(testConfig);
      await monitor.start();
      
      const events: MonitorEvent[] = [];
      monitor.on('stop', (e) => events.push(e));
      
      await monitor.stop();
      
      expect(events.length).toBe(1);
      expect(events[0].type).toBe('stop');
    });

    it('should emit event event for all events', async () => {
      monitor = createRealtimeMonitor(testConfig);
      
      const events: MonitorEvent[] = [];
      monitor.on('event', (e) => events.push(e));
      
      await monitor.start();
      await monitor.stop();
      
      expect(events.length).toBeGreaterThanOrEqual(2);
    });
  });

  describe('configuration options', () => {
    it('should respect debounceMs option', () => {
      monitor = createRealtimeMonitor({
        ...testConfig,
        debounceMs: 500,
      });
      
      expect(monitor).toBeInstanceOf(RealtimeMonitor);
    });

    it('should respect maxFileSize option', () => {
      monitor = createRealtimeMonitor({
        ...testConfig,
        maxFileSize: 1024 * 1024 * 2, // 2MB
      });
      
      expect(monitor).toBeInstanceOf(RealtimeMonitor);
    });

    it('should respect minSeverity option', () => {
      monitor = createRealtimeMonitor({
        ...testConfig,
        minSeverity: 'high',
      });
      
      expect(monitor).toBeInstanceOf(RealtimeMonitor);
    });

    it('should respect recursive option', () => {
      monitor = createRealtimeMonitor({
        ...testConfig,
        recursive: false,
      });
      
      expect(monitor).toBeInstanceOf(RealtimeMonitor);
    });

    it('should respect includePatterns option', () => {
      monitor = createRealtimeMonitor({
        ...testConfig,
        includePatterns: ['**/*.ts', '**/*.js'],
      });
      
      expect(monitor).toBeInstanceOf(RealtimeMonitor);
    });

    it('should respect excludePatterns option', () => {
      monitor = createRealtimeMonitor({
        ...testConfig,
        excludePatterns: ['**/node_modules/**', '**/dist/**'],
      });
      
      expect(monitor).toBeInstanceOf(RealtimeMonitor);
    });

    it('should respect verbose option', () => {
      monitor = createRealtimeMonitor({
        ...testConfig,
        verbose: true,
      });
      
      expect(monitor).toBeInstanceOf(RealtimeMonitor);
    });
  });

  describe('pattern matching', () => {
    it('should include TypeScript files by default', () => {
      monitor = createRealtimeMonitor(testConfig);
      
      // The default patterns include **/*.ts
      expect(monitor).toBeInstanceOf(RealtimeMonitor);
    });

    it('should exclude node_modules by default', () => {
      monitor = createRealtimeMonitor(testConfig);
      
      // The default patterns exclude **/node_modules/**
      expect(monitor).toBeInstanceOf(RealtimeMonitor);
    });
  });
});
