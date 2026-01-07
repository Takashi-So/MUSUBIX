/**
 * @fileoverview Realtime Security Monitor - File watching with continuous scanning
 * @module @nahisaho/musubix-security/analyzers/monitor/realtime-monitor
 * @trace DES-SEC3-MON-001, REQ-SEC3-MON-001
 */

import { EventEmitter } from 'node:events';
import * as fs from 'node:fs';
import * as path from 'node:path';
import type { Vulnerability, Severity } from '../../types/vulnerability.js';

/**
 * Monitor-specific scan result (simplified for realtime monitoring)
 */
export interface MonitorScanResult {
  scannedAt: Date;
  filesScanned: number;
  vulnerabilities: Vulnerability[];
  errors: Error[];
  summary: {
    critical: number;
    high: number;
    medium: number;
    low: number;
    info: number;
    total: number;
  };
}

/**
 * Monitor event types
 */
export type MonitorEventType =
  | 'start'
  | 'stop'
  | 'file-change'
  | 'file-add'
  | 'file-remove'
  | 'scan-start'
  | 'scan-complete'
  | 'vulnerability-found'
  | 'vulnerability-resolved'
  | 'error';

/**
 * Monitor event data
 */
export interface MonitorEvent {
  type: MonitorEventType;
  timestamp: Date;
  file?: string;
  vulnerability?: Vulnerability;
  scanResult?: MonitorScanResult;
  error?: Error;
  message?: string;
}

/**
 * File change event
 */
export interface FileChangeEvent {
  type: 'add' | 'change' | 'unlink';
  path: string;
  stats?: fs.Stats;
}

/**
 * Scanner function type
 */
export type ScannerFunction = (
  filePath: string,
  content: string
) => Promise<Vulnerability[]>;

/**
 * Monitor configuration
 */
export interface MonitorConfig {
  /** Directories to watch */
  watchPaths: string[];
  /** File patterns to include (glob-like) */
  includePatterns?: string[];
  /** File patterns to exclude */
  excludePatterns?: string[];
  /** Debounce time in milliseconds */
  debounceMs?: number;
  /** Enable recursive watching */
  recursive?: boolean;
  /** Maximum file size to scan (bytes) */
  maxFileSize?: number;
  /** Scanner functions to run */
  scanners?: ScannerFunction[];
  /** Report only these severity levels or higher */
  minSeverity?: Severity;
  /** Enable verbose logging */
  verbose?: boolean;
}

/**
 * Monitor state
 */
export interface MonitorState {
  isRunning: boolean;
  startTime?: Date;
  filesWatched: number;
  scanCount: number;
  vulnerabilityCount: number;
  lastScanTime?: Date;
  errorCount: number;
}

/**
 * Scan queue item
 */
interface QueueItem {
  filePath: string;
  changeType: 'add' | 'change';
  timestamp: Date;
}

/**
 * Vulnerability tracking
 */
interface VulnerabilityTracker {
  vulnerabilities: Map<string, Vulnerability[]>;
  lastScan: Map<string, Date>;
}

/**
 * Default patterns
 */
const DEFAULT_INCLUDE_PATTERNS = [
  '**/*.ts',
  '**/*.tsx',
  '**/*.js',
  '**/*.jsx',
  '**/*.py',
  '**/*.java',
  '**/*.cs',
  '**/*.go',
  '**/*.rb',
  '**/*.php',
  '**/*.yml',
  '**/*.yaml',
  '**/*.json',
  '**/*.tf',
  '**/*.hcl',
];

const DEFAULT_EXCLUDE_PATTERNS = [
  '**/node_modules/**',
  '**/.git/**',
  '**/dist/**',
  '**/build/**',
  '**/coverage/**',
  '**/*.min.js',
  '**/*.map',
  '**/vendor/**',
  '**/__pycache__/**',
  '**/target/**',
];

/**
 * Severity order for filtering
 */
const SEVERITY_ORDER: Record<Severity, number> = {
  critical: 4,
  high: 3,
  medium: 2,
  low: 1,
  info: 0,
};

/**
 * Realtime Security Monitor
 * @trace DES-SEC3-MON-001
 */
export class RealtimeMonitor extends EventEmitter {
  private config: Required<MonitorConfig>;
  private state: MonitorState;
  private watchers: fs.FSWatcher[] = [];
  private scanQueue: QueueItem[] = [];
  private debounceTimers: Map<string, NodeJS.Timeout> = new Map();
  private tracker: VulnerabilityTracker;
  private isProcessing = false;

  constructor(config: MonitorConfig) {
    super();
    this.config = {
      watchPaths: config.watchPaths,
      includePatterns: config.includePatterns ?? DEFAULT_INCLUDE_PATTERNS,
      excludePatterns: config.excludePatterns ?? DEFAULT_EXCLUDE_PATTERNS,
      debounceMs: config.debounceMs ?? 500,
      recursive: config.recursive ?? true,
      maxFileSize: config.maxFileSize ?? 1024 * 1024, // 1MB
      scanners: config.scanners ?? [],
      minSeverity: config.minSeverity ?? 'low',
      verbose: config.verbose ?? false,
    };

    this.state = {
      isRunning: false,
      filesWatched: 0,
      scanCount: 0,
      vulnerabilityCount: 0,
      errorCount: 0,
    };

    this.tracker = {
      vulnerabilities: new Map(),
      lastScan: new Map(),
    };
  }

  /**
   * Start monitoring
   * @trace REQ-SEC3-MON-001
   */
  async start(): Promise<void> {
    if (this.state.isRunning) {
      throw new Error('Monitor is already running');
    }

    this.state.isRunning = true;
    this.state.startTime = new Date();
    this.state.filesWatched = 0;

    // Setup watchers for each path
    for (const watchPath of this.config.watchPaths) {
      await this.setupWatcher(watchPath);
    }

    this.emitEvent('start', { message: `Started monitoring ${this.state.filesWatched} files` });

    // Process initial scan of existing files
    await this.performInitialScan();
  }

  /**
   * Stop monitoring
   */
  async stop(): Promise<void> {
    if (!this.state.isRunning) {
      return;
    }

    // Clear all timers
    for (const timer of this.debounceTimers.values()) {
      clearTimeout(timer);
    }
    this.debounceTimers.clear();

    // Close all watchers
    for (const watcher of this.watchers) {
      watcher.close();
    }
    this.watchers = [];

    this.state.isRunning = false;

    this.emitEvent('stop', { message: 'Stopped monitoring' });
  }

  /**
   * Get current state
   */
  getState(): MonitorState {
    return { ...this.state };
  }

  /**
   * Get current vulnerabilities
   */
  getCurrentVulnerabilities(): Map<string, Vulnerability[]> {
    return new Map(this.tracker.vulnerabilities);
  }

  /**
   * Get all vulnerabilities as flat array
   */
  getAllVulnerabilities(): Vulnerability[] {
    const all: Vulnerability[] = [];
    for (const vulns of this.tracker.vulnerabilities.values()) {
      all.push(...vulns);
    }
    return all;
  }

  /**
   * Add scanner function
   */
  addScanner(scanner: ScannerFunction): void {
    this.config.scanners.push(scanner);
  }

  /**
   * Remove scanner function
   */
  removeScanner(scanner: ScannerFunction): void {
    const index = this.config.scanners.indexOf(scanner);
    if (index !== -1) {
      this.config.scanners.splice(index, 1);
    }
  }

  /**
   * Force scan a specific file
   */
  async scanFile(filePath: string): Promise<Vulnerability[]> {
    const absolutePath = path.resolve(filePath);
    
    if (!fs.existsSync(absolutePath)) {
      throw new Error(`File not found: ${absolutePath}`);
    }

    return this.performScan(absolutePath);
  }

  /**
   * Setup watcher for a directory
   */
  private async setupWatcher(watchPath: string): Promise<void> {
    const absolutePath = path.resolve(watchPath);
    
    if (!fs.existsSync(absolutePath)) {
      this.log(`Path does not exist: ${absolutePath}`);
      return;
    }

    const stats = fs.statSync(absolutePath);
    
    if (stats.isFile()) {
      this.watchFile(absolutePath);
    } else if (stats.isDirectory()) {
      await this.watchDirectory(absolutePath);
    }
  }

  /**
   * Watch a single file
   */
  private watchFile(filePath: string): void {
    try {
      const watcher = fs.watch(filePath, { persistent: true }, (eventType) => {
        if (eventType === 'change') {
          this.handleFileChange(filePath, 'change');
        }
      });

      this.watchers.push(watcher);
      this.state.filesWatched++;
    } catch (error) {
      this.handleError(error as Error, `Failed to watch file: ${filePath}`);
    }
  }

  /**
   * Watch a directory recursively
   */
  private async watchDirectory(dirPath: string): Promise<void> {
    try {
      const watcher = fs.watch(
        dirPath,
        { recursive: this.config.recursive, persistent: true },
        (eventType, filename) => {
          if (!filename) return;
          
          const fullPath = path.join(dirPath, filename);
          
          // Check if file matches patterns
          if (!this.shouldProcessFile(fullPath)) return;

          if (eventType === 'change' || eventType === 'rename') {
            // Check if file exists (rename could be delete)
            if (fs.existsSync(fullPath)) {
              const stats = fs.statSync(fullPath);
              if (stats.isFile()) {
                this.handleFileChange(fullPath, eventType === 'rename' ? 'add' : 'change');
              }
            } else {
              this.handleFileRemove(fullPath);
            }
          }
        }
      );

      this.watchers.push(watcher);

      // Count files in directory
      await this.countFiles(dirPath);
    } catch (error) {
      this.handleError(error as Error, `Failed to watch directory: ${dirPath}`);
    }
  }

  /**
   * Count files in directory
   */
  private async countFiles(dirPath: string): Promise<void> {
    const entries = fs.readdirSync(dirPath, { withFileTypes: true });
    
    for (const entry of entries) {
      const fullPath = path.join(dirPath, entry.name);
      
      if (entry.isDirectory() && this.config.recursive) {
        // Skip excluded directories
        if (!this.isExcluded(fullPath)) {
          await this.countFiles(fullPath);
        }
      } else if (entry.isFile() && this.shouldProcessFile(fullPath)) {
        this.state.filesWatched++;
      }
    }
  }

  /**
   * Handle file change event
   */
  private handleFileChange(filePath: string, changeType: 'add' | 'change'): void {
    // Clear existing debounce timer
    const existingTimer = this.debounceTimers.get(filePath);
    if (existingTimer) {
      clearTimeout(existingTimer);
    }

    // Set new debounce timer
    const timer = setTimeout(() => {
      this.debounceTimers.delete(filePath);
      this.queueScan(filePath, changeType);
    }, this.config.debounceMs);

    this.debounceTimers.set(filePath, timer);

    this.emitEvent(changeType === 'add' ? 'file-add' : 'file-change', { file: filePath });
  }

  /**
   * Handle file removal
   */
  private handleFileRemove(filePath: string): void {
    // Clear debounce timer if exists
    const timer = this.debounceTimers.get(filePath);
    if (timer) {
      clearTimeout(timer);
      this.debounceTimers.delete(filePath);
    }

    // Check for resolved vulnerabilities
    const previousVulns = this.tracker.vulnerabilities.get(filePath) ?? [];
    if (previousVulns.length > 0) {
      this.tracker.vulnerabilities.delete(filePath);
      this.state.vulnerabilityCount -= previousVulns.length;
      
      for (const vuln of previousVulns) {
        this.emitEvent('vulnerability-resolved', { vulnerability: vuln, file: filePath });
      }
    }

    this.tracker.lastScan.delete(filePath);
    this.emitEvent('file-remove', { file: filePath });
  }

  /**
   * Queue file for scanning
   */
  private queueScan(filePath: string, changeType: 'add' | 'change'): void {
    this.scanQueue.push({
      filePath,
      changeType,
      timestamp: new Date(),
    });

    this.processQueue();
  }

  /**
   * Process scan queue
   */
  private async processQueue(): Promise<void> {
    if (this.isProcessing || this.scanQueue.length === 0) {
      return;
    }

    this.isProcessing = true;

    while (this.scanQueue.length > 0) {
      const item = this.scanQueue.shift()!;
      
      try {
        await this.performScan(item.filePath);
      } catch (error) {
        this.handleError(error as Error, `Scan failed: ${item.filePath}`);
      }
    }

    this.isProcessing = false;
  }

  /**
   * Perform scan on a file
   */
  private async performScan(filePath: string): Promise<Vulnerability[]> {
    // Check file size
    const stats = fs.statSync(filePath);
    if (stats.size > this.config.maxFileSize) {
      this.log(`Skipping large file: ${filePath} (${stats.size} bytes)`);
      return [];
    }

    const content = fs.readFileSync(filePath, 'utf-8');
    
    this.emitEvent('scan-start', { file: filePath });
    this.state.scanCount++;

    const allVulns: Vulnerability[] = [];

    // Run all scanners
    for (const scanner of this.config.scanners) {
      try {
        const vulns = await scanner(filePath, content);
        allVulns.push(...vulns);
      } catch (error) {
        this.handleError(error as Error, `Scanner failed on: ${filePath}`);
      }
    }

    // Filter by severity
    const filteredVulns = allVulns.filter(
      v => SEVERITY_ORDER[v.severity] >= SEVERITY_ORDER[this.config.minSeverity]
    );

    // Track vulnerability changes
    const previousVulns = this.tracker.vulnerabilities.get(filePath) ?? [];
    const previousIds = new Set(previousVulns.map(v => v.id));
    const currentIds = new Set(filteredVulns.map(v => v.id));

    // Detect new vulnerabilities
    for (const vuln of filteredVulns) {
      if (!previousIds.has(vuln.id)) {
        this.state.vulnerabilityCount++;
        this.emitEvent('vulnerability-found', { vulnerability: vuln, file: filePath });
      }
    }

    // Detect resolved vulnerabilities
    for (const vuln of previousVulns) {
      if (!currentIds.has(vuln.id)) {
        this.state.vulnerabilityCount--;
        this.emitEvent('vulnerability-resolved', { vulnerability: vuln, file: filePath });
      }
    }

    // Update tracker
    this.tracker.vulnerabilities.set(filePath, filteredVulns);
    this.tracker.lastScan.set(filePath, new Date());
    this.state.lastScanTime = new Date();

    this.emitEvent('scan-complete', {
      file: filePath,
      scanResult: {
        scannedAt: new Date(),
        filesScanned: 1,
        vulnerabilities: filteredVulns,
        errors: [],
        summary: {
          critical: filteredVulns.filter(v => v.severity === 'critical').length,
          high: filteredVulns.filter(v => v.severity === 'high').length,
          medium: filteredVulns.filter(v => v.severity === 'medium').length,
          low: filteredVulns.filter(v => v.severity === 'low').length,
          info: filteredVulns.filter(v => v.severity === 'info').length,
          total: filteredVulns.length,
        },
      },
    });

    return filteredVulns;
  }

  /**
   * Perform initial scan of all files
   */
  private async performInitialScan(): Promise<void> {
    for (const watchPath of this.config.watchPaths) {
      await this.scanDirectory(watchPath);
    }
  }

  /**
   * Scan directory recursively
   */
  private async scanDirectory(dirPath: string): Promise<void> {
    const absolutePath = path.resolve(dirPath);
    
    if (!fs.existsSync(absolutePath)) return;
    
    const stats = fs.statSync(absolutePath);
    
    if (stats.isFile() && this.shouldProcessFile(absolutePath)) {
      this.queueScan(absolutePath, 'add');
      return;
    }

    if (!stats.isDirectory()) return;

    const entries = fs.readdirSync(absolutePath, { withFileTypes: true });

    for (const entry of entries) {
      const fullPath = path.join(absolutePath, entry.name);

      if (entry.isDirectory() && this.config.recursive && !this.isExcluded(fullPath)) {
        await this.scanDirectory(fullPath);
      } else if (entry.isFile() && this.shouldProcessFile(fullPath)) {
        this.queueScan(fullPath, 'add');
      }
    }
  }

  /**
   * Check if file should be processed
   */
  private shouldProcessFile(filePath: string): boolean {
    if (this.isExcluded(filePath)) return false;
    return this.isIncluded(filePath);
  }

  /**
   * Check if file is excluded
   */
  private isExcluded(filePath: string): boolean {
    return this.config.excludePatterns.some(pattern => 
      this.matchGlob(filePath, pattern)
    );
  }

  /**
   * Check if file is included
   */
  private isIncluded(filePath: string): boolean {
    return this.config.includePatterns.some(pattern => 
      this.matchGlob(filePath, pattern)
    );
  }

  /**
   * Simple glob matching
   */
  private matchGlob(filePath: string, pattern: string): boolean {
    // Convert glob to regex
    const regexPattern = pattern
      .replace(/\*\*/g, '___DOUBLESTAR___')
      .replace(/\*/g, '[^/]*')
      .replace(/___DOUBLESTAR___/g, '.*')
      .replace(/\?/g, '.')
      .replace(/\./g, '\\.');

    const regex = new RegExp(`(^|/)${regexPattern}$`);
    return regex.test(filePath);
  }

  /**
   * Emit monitor event
   */
  private emitEvent(
    type: MonitorEventType,
    data: Partial<Omit<MonitorEvent, 'type' | 'timestamp'>>
  ): void {
    const event: MonitorEvent = {
      type,
      timestamp: new Date(),
      ...data,
    };

    this.emit(type, event);
    this.emit('event', event);
  }

  /**
   * Handle error
   */
  private handleError(error: Error, message: string): void {
    this.state.errorCount++;
    this.emitEvent('error', { error, message });
    this.log(`Error: ${message} - ${error.message}`);
  }

  /**
   * Log message (if verbose)
   */
  private log(message: string): void {
    if (this.config.verbose) {
      console.log(`[RealtimeMonitor] ${message}`);
    }
  }
}

/**
 * Create realtime monitor instance
 */
export function createRealtimeMonitor(config: MonitorConfig): RealtimeMonitor {
  return new RealtimeMonitor(config);
}

/**
 * Create monitor with common security scanners
 */
export async function createSecurityMonitor(
  watchPaths: string[],
  options: Partial<MonitorConfig> = {}
): Promise<RealtimeMonitor> {
  const monitor = new RealtimeMonitor({
    watchPaths,
    ...options,
  });

  // Add basic pattern-based scanner for common vulnerabilities
  monitor.addScanner(createPatternScanner());

  return monitor;
}

/**
 * Create a simple pattern-based scanner
 */
function createPatternScanner(): ScannerFunction {
  const patterns: Array<{
    pattern: RegExp;
    type: string;
    severity: Severity;
    message: string;
    cwe: string[];
  }> = [
    {
      pattern: /eval\s*\(/gi,
      type: 'code-injection',
      severity: 'high',
      message: 'Use of eval() is dangerous and can lead to code injection',
      cwe: ['CWE-94'],
    },
    {
      pattern: /new\s+Function\s*\(/gi,
      type: 'code-injection',
      severity: 'high',
      message: 'Dynamic Function construction can lead to code injection',
      cwe: ['CWE-94'],
    },
    {
      pattern: /innerHTML\s*=/gi,
      type: 'xss',
      severity: 'medium',
      message: 'Setting innerHTML directly can lead to XSS vulnerabilities',
      cwe: ['CWE-79'],
    },
    {
      pattern: /(password|secret|api[_-]?key|token)\s*[=:]\s*['"][^'"]+['"]/gi,
      type: 'hardcoded-secret',
      severity: 'high',
      message: 'Potential hardcoded secret or credential',
      cwe: ['CWE-798'],
    },
    {
      pattern: /https?:\/\/[^\s'"]+\?.*=(process\.env|config)/gi,
      type: 'ssrf',
      severity: 'medium',
      message: 'Potential Server-Side Request Forgery (SSRF) vulnerability',
      cwe: ['CWE-918'],
    },
    {
      pattern: /exec\s*\(\s*[`'"].*\$\{/gi,
      type: 'command-injection',
      severity: 'critical',
      message: 'Potential command injection via string interpolation',
      cwe: ['CWE-78'],
    },
    {
      pattern: /document\.write\s*\(/gi,
      type: 'xss',
      severity: 'medium',
      message: 'document.write can introduce XSS vulnerabilities',
      cwe: ['CWE-79'],
    },
  ];

  return async (filePath: string, content: string): Promise<Vulnerability[]> => {
    const vulnerabilities: Vulnerability[] = [];
    const lines = content.split('\n');

    for (const { pattern, type, severity, message, cwe } of patterns) {
      let match;
      pattern.lastIndex = 0;

      while ((match = pattern.exec(content)) !== null) {
        // Find line number
        const beforeMatch = content.substring(0, match.index);
        const lineNumber = beforeMatch.split('\n').length;
        const line = lines[lineNumber - 1] ?? '';
        const column = match.index - beforeMatch.lastIndexOf('\n') - 1;

        vulnerabilities.push({
          id: `${type}-${filePath}-${lineNumber}-${column}`,
          type: type as any,
          severity,
          cwes: cwe,
          owasp: [],
          location: {
            file: filePath,
            startLine: lineNumber,
            endLine: lineNumber,
            startColumn: column,
            endColumn: column + match[0].length,
          },
          description: message,
          recommendation: `Review and fix the ${type} issue at line ${lineNumber}`,
          confidence: 0.7,
          ruleId: `PATTERN-${type.toUpperCase()}`,
          codeSnippet: line.trim(),
          detectedAt: new Date(),
        });
      }
    }

    return vulnerabilities;
  };
}
