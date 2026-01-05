/**
 * FileWatcher - Real-time File Change Monitoring
 *
 * Monitors file system changes and emits events for pattern analysis.
 * Uses Node.js fs.watch API (no external dependencies per ADR-0001).
 *
 * @see REQ-LEARN-010 - Real-time Pattern Learning
 * @see REQ-LEARN-011 - 500ms Analysis Latency
 * @see DES-LEARN-010 - FileWatcher Component
 * @see ADR-0001 - fs.watch + EventEmitter decision
 * @module @musubix/core/learning/realtime
 */

import { EventEmitter } from 'events';
import * as fs from 'fs';
import * as path from 'path';
import {
  type FileChangeEvent,
  type FileWatcherConfig,
  DEFAULT_FILE_WATCHER_CONFIG,
} from './types.js';

/**
 * FileWatcher events
 */
export interface FileWatcherEvents {
  change: (event: FileChangeEvent) => void;
  error: (error: Error) => void;
  ready: () => void;
  close: () => void;
}

/**
 * FileWatcher - Monitors file system changes
 *
 * @example
 * ```typescript
 * const watcher = new FileWatcher({ paths: ['src'] });
 * watcher.on('change', (event) => {
 *   console.log(`File changed: ${event.path}`);
 * });
 * await watcher.start();
 * ```
 */
export class FileWatcher extends EventEmitter {
  private readonly config: FileWatcherConfig;
  private watchers: Map<string, fs.FSWatcher> = new Map();
  private debounceTimers: Map<string, NodeJS.Timeout> = new Map();
  private _isWatching = false;
  private _watchedPaths: Set<string> = new Set();

  constructor(config: Partial<FileWatcherConfig> = {}) {
    super();
    this.config = { ...DEFAULT_FILE_WATCHER_CONFIG, ...config };
  }

  /**
   * Start watching configured paths
   * @traceability REQ-LEARN-010
   */
  async start(): Promise<void> {
    if (this._isWatching) {
      return;
    }

    for (const watchPath of this.config.paths) {
      await this.watchPath(watchPath);
    }

    this._isWatching = true;
    this.emit('ready');
  }

  /**
   * Watch specific paths
   * @traceability REQ-LEARN-010
   */
  async watch(paths: string[]): Promise<void> {
    for (const watchPath of paths) {
      if (!this._watchedPaths.has(watchPath)) {
        await this.watchPath(watchPath);
      }
    }
    this._isWatching = true;
  }

  /**
   * Register file change callback
   * @traceability REQ-LEARN-010
   */
  onFileChange(callback: (event: FileChangeEvent) => void): void {
    this.on('change', callback);
  }

  /**
   * Stop watching all paths
   */
  stop(): void {
    for (const [, watcher] of this.watchers) {
      watcher.close();
    }
    this.watchers.clear();

    for (const [, timer] of this.debounceTimers) {
      clearTimeout(timer);
    }
    this.debounceTimers.clear();

    this._watchedPaths.clear();
    this._isWatching = false;
    this.emit('close');
  }

  /**
   * Check if watcher is active
   */
  isWatching(): boolean {
    return this._isWatching;
  }

  /**
   * Get currently watched paths
   */
  getWatchedPaths(): string[] {
    return Array.from(this._watchedPaths);
  }

  /**
   * Watch a single path (file or directory)
   */
  private async watchPath(targetPath: string): Promise<void> {
    const absolutePath = path.resolve(targetPath);

    try {
      const stats = await fs.promises.stat(absolutePath);

      if (stats.isDirectory()) {
        await this.watchDirectory(absolutePath);
      } else if (stats.isFile()) {
        this.watchFile(absolutePath);
      }
    } catch (error) {
      this.emit('error', new Error(`Failed to watch path: ${absolutePath}`));
    }
  }

  /**
   * Watch a directory recursively
   */
  private async watchDirectory(dirPath: string): Promise<void> {
    if (this.shouldIgnore(dirPath)) {
      return;
    }

    try {
      const watcher = fs.watch(dirPath, { persistent: true }, (eventType, filename) => {
        if (filename) {
          const fullPath = path.join(dirPath, filename);
          this.handleFileChange(fullPath, eventType);
        }
      });

      watcher.on('error', (error) => {
        this.emit('error', error);
      });

      this.watchers.set(dirPath, watcher);
      this._watchedPaths.add(dirPath);

      // Watch subdirectories
      const entries = await fs.promises.readdir(dirPath, { withFileTypes: true });
      for (const entry of entries) {
        if (entry.isDirectory()) {
          const subPath = path.join(dirPath, entry.name);
          await this.watchDirectory(subPath);
        }
      }
    } catch (error) {
      this.emit('error', new Error(`Failed to watch directory: ${dirPath}`));
    }
  }

  /**
   * Watch a single file
   */
  private watchFile(filePath: string): void {
    if (this.shouldIgnore(filePath)) {
      return;
    }

    if (!this.hasValidExtension(filePath)) {
      return;
    }

    try {
      const watcher = fs.watch(filePath, { persistent: true }, (eventType) => {
        this.handleFileChange(filePath, eventType);
      });

      watcher.on('error', (error) => {
        this.emit('error', error);
      });

      this.watchers.set(filePath, watcher);
      this._watchedPaths.add(filePath);
    } catch (error) {
      this.emit('error', new Error(`Failed to watch file: ${filePath}`));
    }
  }

  /**
   * Handle file change event with debouncing
   * @traceability REQ-LEARN-011 - Minimize processing overhead
   */
  private handleFileChange(filePath: string, eventType: string): void {
    if (!this.hasValidExtension(filePath)) {
      return;
    }

    if (this.shouldIgnore(filePath)) {
      return;
    }

    // Clear existing debounce timer
    const existingTimer = this.debounceTimers.get(filePath);
    if (existingTimer) {
      clearTimeout(existingTimer);
    }

    // Set new debounce timer
    const timer = setTimeout(() => {
      this.emitChangeEvent(filePath, eventType);
      this.debounceTimers.delete(filePath);
    }, this.config.debounceMs);

    this.debounceTimers.set(filePath, timer);
  }

  /**
   * Emit file change event
   */
  private async emitChangeEvent(filePath: string, eventType: string): Promise<void> {
    const changeType = this.mapEventType(eventType, filePath);
    let content: string | undefined;

    if (changeType !== 'delete') {
      try {
        content = await fs.promises.readFile(filePath, 'utf-8');
      } catch {
        // File might have been deleted
        return;
      }
    }

    const event: FileChangeEvent = {
      path: filePath,
      type: changeType,
      timestamp: Date.now(),
      content,
    };

    this.emit('change', event);
  }

  /**
   * Map fs.watch event type to FileChangeType
   */
  private mapEventType(
    eventType: string,
    filePath: string
  ): 'create' | 'modify' | 'delete' {
    if (eventType === 'rename') {
      // Check if file exists to determine create or delete
      try {
        fs.accessSync(filePath);
        return 'create';
      } catch {
        return 'delete';
      }
    }
    return 'modify';
  }

  /**
   * Check if path should be ignored
   */
  private shouldIgnore(targetPath: string): boolean {
    const relativePath = path.relative(process.cwd(), targetPath);

    for (const pattern of this.config.ignore) {
      if (this.matchGlob(relativePath, pattern)) {
        return true;
      }
    }

    return false;
  }

  /**
   * Check if file has valid extension
   */
  private hasValidExtension(filePath: string): boolean {
    const ext = path.extname(filePath);
    return this.config.extensions.includes(ext);
  }

  /**
   * Simple glob matching (supports ** and *)
   */
  private matchGlob(str: string, pattern: string): boolean {
    const regexPattern = pattern
      .replace(/\*\*/g, '.*')
      .replace(/\*/g, '[^/]*')
      .replace(/\./g, '\\.');

    return new RegExp(`^${regexPattern}$`).test(str);
  }
}
