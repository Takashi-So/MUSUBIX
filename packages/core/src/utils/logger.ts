/**
 * Logger Utility
 * 
 * Provides structured logging with levels, formatting, and output options
 * 
 * @packageDocumentation
 * @module utils/logger
 * 
 * @see REQ-MNT-001 - Logger
 * @see DES-MUSUBIX-001 Section 16.1 - Logger Design
 */

import { appendFile, mkdir } from 'fs/promises';
import { dirname } from 'path';

/**
 * Log levels
 */
export type LogLevel = 'debug' | 'info' | 'warn' | 'error' | 'fatal';

/**
 * Log level priority (lower = more verbose)
 */
const LOG_LEVEL_PRIORITY: Record<LogLevel, number> = {
  debug: 0,
  info: 1,
  warn: 2,
  error: 3,
  fatal: 4,
};

/**
 * Log entry structure
 */
export interface LogEntry {
  timestamp: string;
  level: LogLevel;
  message: string;
  context?: string;
  data?: Record<string, unknown>;
  error?: {
    name: string;
    message: string;
    stack?: string;
  };
}

/**
 * Logger configuration
 */
export interface LoggerConfig {
  /** Minimum log level */
  level: LogLevel;
  /** Enable console output */
  console: boolean;
  /** Enable file output */
  file: boolean;
  /** Log file path */
  filePath?: string;
  /** Enable JSON format */
  json: boolean;
  /** Enable colors in console */
  colors: boolean;
  /** Include timestamps */
  timestamps: boolean;
  /** Context prefix */
  context?: string;
}

/**
 * Default logger configuration
 */
const DEFAULT_CONFIG: LoggerConfig = {
  level: 'info',
  console: true,
  file: false,
  json: false,
  colors: true,
  timestamps: true,
};

/**
 * ANSI color codes
 */
const COLORS = {
  reset: '\x1b[0m',
  dim: '\x1b[2m',
  bold: '\x1b[1m',
  debug: '\x1b[36m',  // cyan
  info: '\x1b[32m',   // green
  warn: '\x1b[33m',   // yellow
  error: '\x1b[31m',  // red
  fatal: '\x1b[35m',  // magenta
} as const;

/**
 * Logger class
 */
export class Logger {
  private config: LoggerConfig;
  private context: string;

  constructor(context?: string, config?: Partial<LoggerConfig>) {
    this.context = context ?? 'musubix';
    this.config = { ...DEFAULT_CONFIG, ...config };
    if (context) {
      this.config.context = context;
    }
  }

  /**
   * Create a child logger with additional context
   */
  child(context: string): Logger {
    const childContext = this.context ? `${this.context}:${context}` : context;
    return new Logger(childContext, this.config);
  }

  /**
   * Update configuration
   */
  configure(config: Partial<LoggerConfig>): void {
    this.config = { ...this.config, ...config };
  }

  /**
   * Log debug message
   */
  debug(message: string, data?: Record<string, unknown>): void {
    this.log('debug', message, data);
  }

  /**
   * Log info message
   */
  info(message: string, data?: Record<string, unknown>): void {
    this.log('info', message, data);
  }

  /**
   * Log warning message
   */
  warn(message: string, data?: Record<string, unknown>): void {
    this.log('warn', message, data);
  }

  /**
   * Log error message
   */
  error(message: string, error?: Error, data?: Record<string, unknown>): void {
    this.log('error', message, data, error);
  }

  /**
   * Log fatal message
   */
  fatal(message: string, error?: Error, data?: Record<string, unknown>): void {
    this.log('fatal', message, data, error);
  }

  /**
   * Log with timing
   */
  time(label: string): () => void {
    const start = performance.now();
    return () => {
      const duration = performance.now() - start;
      this.debug(`${label} completed`, { durationMs: duration.toFixed(2) });
    };
  }

  /**
   * Core logging method
   */
  private log(
    level: LogLevel,
    message: string,
    data?: Record<string, unknown>,
    error?: Error
  ): void {
    // Check log level
    if (LOG_LEVEL_PRIORITY[level] < LOG_LEVEL_PRIORITY[this.config.level]) {
      return;
    }

    const entry: LogEntry = {
      timestamp: new Date().toISOString(),
      level,
      message,
      context: this.context,
      data,
      error: error ? {
        name: error.name,
        message: error.message,
        stack: error.stack,
      } : undefined,
    };

    // Console output
    if (this.config.console) {
      this.writeConsole(entry);
    }

    // File output
    if (this.config.file && this.config.filePath) {
      this.writeFile(entry).catch(() => {
        // Silently fail file writes
      });
    }
  }

  /**
   * Write to console
   */
  private writeConsole(entry: LogEntry): void {
    const output = this.config.json
      ? this.formatJson(entry)
      : this.formatText(entry);

    switch (entry.level) {
      case 'error':
      case 'fatal':
        console.error(output);
        break;
      case 'warn':
        console.warn(output);
        break;
      default:
        console.log(output);
    }
  }

  /**
   * Write to file
   */
  private async writeFile(entry: LogEntry): Promise<void> {
    if (!this.config.filePath) {
      return;
    }

    const line = this.formatJson(entry) + '\n';
    
    try {
      await mkdir(dirname(this.config.filePath), { recursive: true });
      await appendFile(this.config.filePath, line);
    } catch {
      // Silently fail
    }
  }

  /**
   * Format entry as JSON
   */
  private formatJson(entry: LogEntry): string {
    return JSON.stringify(entry);
  }

  /**
   * Format entry as text
   */
  private formatText(entry: LogEntry): string {
    const parts: string[] = [];

    // Timestamp
    if (this.config.timestamps) {
      const time = this.config.colors
        ? `${COLORS.dim}${entry.timestamp}${COLORS.reset}`
        : entry.timestamp;
      parts.push(time);
    }

    // Level
    const levelUpper = entry.level.toUpperCase().padEnd(5);
    const level = this.config.colors
      ? `${COLORS[entry.level]}${levelUpper}${COLORS.reset}`
      : levelUpper;
    parts.push(level);

    // Context
    if (entry.context) {
      const ctx = this.config.colors
        ? `${COLORS.dim}[${entry.context}]${COLORS.reset}`
        : `[${entry.context}]`;
      parts.push(ctx);
    }

    // Message
    parts.push(entry.message);

    // Data
    if (entry.data && Object.keys(entry.data).length > 0) {
      parts.push(JSON.stringify(entry.data));
    }

    // Error
    if (entry.error) {
      parts.push(`\n  ${entry.error.name}: ${entry.error.message}`);
      if (entry.error.stack) {
        parts.push(`\n${entry.error.stack}`);
      }
    }

    return parts.join(' ');
  }
}

/**
 * Global logger instance
 */
export const logger = new Logger();

/**
 * Create a new logger with context
 */
export function createLogger(context: string, config?: Partial<LoggerConfig>): Logger {
  return new Logger(context, config);
}
