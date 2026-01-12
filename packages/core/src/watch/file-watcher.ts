/**
 * FileWatcher - File system watcher with debounce and ignore patterns
 * 
 * Implements: TSK-WATCH-001, DES-WATCH-001, REQ-WATCH-001
 */

import { watch, type FSWatcher } from 'node:fs';
import { readFile, stat } from 'node:fs/promises';
import { join, relative, resolve } from 'node:path';
import { EventEmitter } from 'node:events';

/**
 * Watch configuration
 */
export interface WatchConfig {
  /** Paths to watch */
  paths: string[];
  /** Glob patterns to ignore */
  ignore: string[];
  /** Debounce time in milliseconds */
  debounceMs: number;
  /** File extensions to watch (e.g., ['.ts', '.js']) */
  extensions: string[];
}

/**
 * File change event
 */
export interface FileChangeEvent {
  /** Event type */
  type: 'add' | 'change' | 'unlink';
  /** Absolute file path */
  path: string;
  /** Event timestamp */
  timestamp: Date;
}

/**
 * Default configuration
 */
const DEFAULT_CONFIG: WatchConfig = {
  paths: ['.'],
  ignore: [
    'node_modules/**',
    'dist/**',
    '.git/**',
    'coverage/**',
    '*.log',
  ],
  debounceMs: 300,
  extensions: ['.ts', '.js', '.tsx', '.jsx', '.py', '.md'],
};

/**
 * FileWatcher class
 * Watches file system for changes and emits debounced events
 */
export class FileWatcher extends EventEmitter {
  private config: WatchConfig;
  private watchers: FSWatcher[] = [];
  private ignorePatterns: RegExp[] = [];
  private pendingEvents: Map<string, FileChangeEvent> = new Map();
  private debounceTimer: NodeJS.Timeout | null = null;
  private isRunning = false;

  constructor(config: Partial<WatchConfig> = {}) {
    super();
    this.config = { ...DEFAULT_CONFIG, ...config };
    this.buildIgnorePatterns();
  }

  /**
   * Build ignore patterns from config and .gitignore/.musubixignore
   */
  private buildIgnorePatterns(): void {
    this.ignorePatterns = this.config.ignore.map(pattern => {
      // Convert glob to regex
      const regexStr = pattern
        .replace(/\./g, '\\.')
        .replace(/\*\*/g, '.*')
        .replace(/\*/g, '[^/]*')
        .replace(/\?/g, '.');
      return new RegExp(`^${regexStr}$`);
    });
  }

  /**
   * Load additional ignore patterns from files
   */
  private async loadIgnoreFiles(basePath: string): Promise<void> {
    const ignoreFiles = ['.gitignore', '.musubixignore'];
    
    for (const file of ignoreFiles) {
      try {
        const content = await readFile(join(basePath, file), 'utf-8');
        const patterns = content
          .split('\n')
          .map(line => line.trim())
          .filter(line => line && !line.startsWith('#'));
        
        for (const pattern of patterns) {
          const regexStr = pattern
            .replace(/\./g, '\\.')
            .replace(/\*\*/g, '.*')
            .replace(/\*/g, '[^/]*')
            .replace(/\?/g, '.');
          this.ignorePatterns.push(new RegExp(`^${regexStr}$`));
        }
      } catch {
        // Ignore if file doesn't exist
      }
    }
  }

  /**
   * Check if a path should be ignored
   */
  private shouldIgnore(filePath: string): boolean {
    const relativePath = relative(process.cwd(), filePath);
    return this.ignorePatterns.some(pattern => pattern.test(relativePath));
  }

  /**
   * Check if file has a watched extension
   */
  private hasWatchedExtension(filePath: string): boolean {
    if (this.config.extensions.length === 0) return true;
    return this.config.extensions.some(ext => filePath.endsWith(ext));
  }

  /**
   * Handle file system event
   */
  private handleFsEvent(eventType: string, filename: string | null, watchPath: string): void {
    if (!filename) return;
    
    const fullPath = resolve(watchPath, filename);
    
    if (this.shouldIgnore(fullPath)) return;
    if (!this.hasWatchedExtension(fullPath)) return;

    const event: FileChangeEvent = {
      type: eventType === 'rename' ? 'change' : 'change',
      path: fullPath,
      timestamp: new Date(),
    };

    // Check if file exists to determine event type
    stat(fullPath)
      .then(() => {
        event.type = 'change';
        this.queueEvent(event);
      })
      .catch(() => {
        event.type = 'unlink';
        this.queueEvent(event);
      });
  }

  /**
   * Queue event for debounced emission
   */
  private queueEvent(event: FileChangeEvent): void {
    this.pendingEvents.set(event.path, event);

    if (this.debounceTimer) {
      clearTimeout(this.debounceTimer);
    }

    this.debounceTimer = setTimeout(() => {
      this.flushEvents();
    }, this.config.debounceMs);
  }

  /**
   * Flush pending events
   */
  private flushEvents(): void {
    const events = Array.from(this.pendingEvents.values());
    this.pendingEvents.clear();

    for (const event of events) {
      this.emit('change', event);
    }

    if (events.length > 0) {
      this.emit('batch', events);
    }
  }

  /**
   * Start watching
   */
  async start(): Promise<void> {
    if (this.isRunning) return;

    for (const watchPath of this.config.paths) {
      const absolutePath = resolve(watchPath);
      
      await this.loadIgnoreFiles(absolutePath);

      try {
        const watcher = watch(
          absolutePath,
          { recursive: true },
          (eventType, filename) => {
            this.handleFsEvent(eventType, filename, absolutePath);
          }
        );

        watcher.on('error', (error) => {
          this.emit('error', error);
        });

        this.watchers.push(watcher);
      } catch (error) {
        this.emit('error', error);
      }
    }

    this.isRunning = true;
    this.emit('ready');
  }

  /**
   * Stop watching
   */
  async stop(): Promise<void> {
    if (!this.isRunning) return;

    if (this.debounceTimer) {
      clearTimeout(this.debounceTimer);
      this.debounceTimer = null;
    }

    for (const watcher of this.watchers) {
      watcher.close();
    }

    this.watchers = [];
    this.pendingEvents.clear();
    this.isRunning = false;
    this.emit('close');
  }

  /**
   * Check if watcher is running
   */
  get running(): boolean {
    return this.isRunning;
  }

  /**
   * Get current configuration
   */
  getConfig(): WatchConfig {
    return { ...this.config };
  }

  /**
   * Update configuration (requires restart)
   */
  updateConfig(config: Partial<WatchConfig>): void {
    this.config = { ...this.config, ...config };
    this.buildIgnorePatterns();
  }
}

/**
 * Create a FileWatcher instance
 */
export function createFileWatcher(config?: Partial<WatchConfig>): FileWatcher {
  return new FileWatcher(config);
}
