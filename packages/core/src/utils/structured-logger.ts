/**
 * Structured Logger (Extended)
 * 
 * Advanced structured logging with context, correlation, and output formatting
 * 
 * @packageDocumentation
 * @module utils/structured-logger
 * 
 * @see REQ-MNT-001 - Logging & Monitoring
 * @see Article VI - Decision Transparency
 */

/**
 * Log level
 */
export type LogLevel = 'trace' | 'debug' | 'info' | 'warn' | 'error' | 'fatal';

/**
 * Log level values
 */
export const LOG_LEVEL_VALUES: Record<LogLevel, number> = {
  trace: 10,
  debug: 20,
  info: 30,
  warn: 40,
  error: 50,
  fatal: 60,
};

/**
 * Output format
 */
export type OutputFormat = 'json' | 'pretty' | 'compact' | 'logfmt';

/**
 * Log transport
 */
export type TransportType = 'console' | 'file' | 'http' | 'memory' | 'custom';

/**
 * Log entry
 */
export interface LogEntry {
  /** Timestamp */
  timestamp: Date;
  /** Level */
  level: LogLevel;
  /** Message */
  message: string;
  /** Logger name */
  logger: string;
  /** Correlation ID */
  correlationId?: string;
  /** Request ID */
  requestId?: string;
  /** User ID */
  userId?: string;
  /** Context data */
  context?: Record<string, unknown>;
  /** Error info */
  error?: {
    name: string;
    message: string;
    stack?: string;
    code?: string;
  };
  /** Duration (ms) */
  duration?: number;
  /** Tags */
  tags?: string[];
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Transport interface
 */
export interface LogTransport {
  /** Transport name */
  name: string;
  /** Transport type */
  type: TransportType;
  /** Log entry */
  log(entry: LogEntry): void | Promise<void>;
  /** Flush */
  flush?(): void | Promise<void>;
  /** Close */
  close?(): void | Promise<void>;
}

/**
 * Logger config
 */
export interface StructuredLoggerConfig {
  /** Logger name */
  name: string;
  /** Minimum level */
  level: LogLevel;
  /** Output format */
  format: OutputFormat;
  /** Include timestamp */
  includeTimestamp: boolean;
  /** Include caller info */
  includeCaller: boolean;
  /** Pretty print objects */
  prettyPrint: boolean;
  /** Color output */
  colorOutput: boolean;
  /** Default context */
  defaultContext?: Record<string, unknown>;
  /** Redact fields */
  redactFields?: string[];
  /** Max context depth */
  maxContextDepth: number;
}

/**
 * Default configuration
 */
export const DEFAULT_LOGGER_CONFIG: StructuredLoggerConfig = {
  name: 'app',
  level: 'info',
  format: 'pretty',
  includeTimestamp: true,
  includeCaller: false,
  prettyPrint: true,
  colorOutput: true,
  redactFields: ['password', 'secret', 'token', 'apiKey', 'authorization'],
  maxContextDepth: 5,
};

/**
 * Color codes for pretty output
 */
const COLORS = {
  reset: '\x1b[0m',
  bright: '\x1b[1m',
  dim: '\x1b[2m',
  red: '\x1b[31m',
  green: '\x1b[32m',
  yellow: '\x1b[33m',
  blue: '\x1b[34m',
  magenta: '\x1b[35m',
  cyan: '\x1b[36m',
  white: '\x1b[37m',
  gray: '\x1b[90m',
};

/**
 * Level colors
 */
const LEVEL_COLORS: Record<LogLevel, string> = {
  trace: COLORS.gray,
  debug: COLORS.cyan,
  info: COLORS.green,
  warn: COLORS.yellow,
  error: COLORS.red,
  fatal: COLORS.red + COLORS.bright,
};

/**
 * Level icons
 */
const LEVEL_ICONS: Record<LogLevel, string> = {
  trace: '🔍',
  debug: '🐛',
  info: 'ℹ️',
  warn: '⚠️',
  error: '❌',
  fatal: '💀',
};

/**
 * Console transport
 */
export class ConsoleTransport implements LogTransport {
  name = 'console';
  type: TransportType = 'console';
  private config: StructuredLoggerConfig;

  constructor(config: StructuredLoggerConfig) {
    this.config = config;
  }

  log(entry: LogEntry): void {
    const output = this.format(entry);
    
    if (LOG_LEVEL_VALUES[entry.level] >= LOG_LEVEL_VALUES.error) {
      console.error(output);
    } else if (entry.level === 'warn') {
      console.warn(output);
    } else {
      console.log(output);
    }
  }

  private format(entry: LogEntry): string {
    switch (this.config.format) {
      case 'json':
        return JSON.stringify(this.toJSON(entry));
      case 'compact':
        return this.toCompact(entry);
      case 'logfmt':
        return this.toLogfmt(entry);
      case 'pretty':
      default:
        return this.toPretty(entry);
    }
  }

  private toJSON(entry: LogEntry): Record<string, unknown> {
    return {
      timestamp: entry.timestamp.toISOString(),
      level: entry.level,
      logger: entry.logger,
      message: entry.message,
      ...(entry.correlationId && { correlationId: entry.correlationId }),
      ...(entry.requestId && { requestId: entry.requestId }),
      ...(entry.userId && { userId: entry.userId }),
      ...(entry.duration !== undefined && { duration: entry.duration }),
      ...(entry.tags?.length && { tags: entry.tags }),
      ...(entry.context && { context: entry.context }),
      ...(entry.error && { error: entry.error }),
      ...(entry.metadata && { metadata: entry.metadata }),
    };
  }

  private toPretty(entry: LogEntry): string {
    const parts: string[] = [];
    const useColor = this.config.colorOutput;

    // Timestamp
    if (this.config.includeTimestamp) {
      const time = entry.timestamp.toISOString().substring(11, 23);
      parts.push(useColor ? `${COLORS.gray}${time}${COLORS.reset}` : time);
    }

    // Level
    const levelStr = entry.level.toUpperCase().padEnd(5);
    const icon = LEVEL_ICONS[entry.level];
    if (useColor) {
      parts.push(`${LEVEL_COLORS[entry.level]}${icon} ${levelStr}${COLORS.reset}`);
    } else {
      parts.push(`${icon} ${levelStr}`);
    }

    // Logger name
    if (useColor) {
      parts.push(`${COLORS.magenta}[${entry.logger}]${COLORS.reset}`);
    } else {
      parts.push(`[${entry.logger}]`);
    }

    // Message
    parts.push(entry.message);

    // Duration
    if (entry.duration !== undefined) {
      const durationStr = `${entry.duration}ms`;
      parts.push(useColor ? `${COLORS.cyan}(${durationStr})${COLORS.reset}` : `(${durationStr})`);
    }

    // Correlation ID
    if (entry.correlationId) {
      const idStr = `cid:${entry.correlationId.substring(0, 8)}`;
      parts.push(useColor ? `${COLORS.gray}${idStr}${COLORS.reset}` : idStr);
    }

    let result = parts.join(' ');

    // Context
    if (entry.context && Object.keys(entry.context).length > 0) {
      const contextStr = this.config.prettyPrint
        ? JSON.stringify(entry.context, null, 2)
        : JSON.stringify(entry.context);
      result += '\n  ' + (useColor ? `${COLORS.gray}${contextStr}${COLORS.reset}` : contextStr);
    }

    // Error
    if (entry.error) {
      const errorStr = entry.error.stack ?? `${entry.error.name}: ${entry.error.message}`;
      result += '\n  ' + (useColor ? `${COLORS.red}${errorStr}${COLORS.reset}` : errorStr);
    }

    return result;
  }

  private toCompact(entry: LogEntry): string {
    const time = entry.timestamp.toISOString().substring(11, 23);
    const level = entry.level.charAt(0).toUpperCase();
    let result = `${time} ${level} [${entry.logger}] ${entry.message}`;
    
    if (entry.duration !== undefined) {
      result += ` (${entry.duration}ms)`;
    }
    
    return result;
  }

  private toLogfmt(entry: LogEntry): string {
    const parts: string[] = [
      `time=${entry.timestamp.toISOString()}`,
      `level=${entry.level}`,
      `logger=${entry.logger}`,
      `msg="${this.escapeLogfmt(entry.message)}"`,
    ];

    if (entry.correlationId) {
      parts.push(`correlation_id=${entry.correlationId}`);
    }
    if (entry.requestId) {
      parts.push(`request_id=${entry.requestId}`);
    }
    if (entry.userId) {
      parts.push(`user_id=${entry.userId}`);
    }
    if (entry.duration !== undefined) {
      parts.push(`duration=${entry.duration}`);
    }
    if (entry.error) {
      parts.push(`error="${this.escapeLogfmt(entry.error.message)}"`);
    }

    return parts.join(' ');
  }

  private escapeLogfmt(str: string): string {
    return str.replace(/"/g, '\\"').replace(/\n/g, '\\n');
  }
}

/**
 * Memory transport (for testing)
 */
export class MemoryTransport implements LogTransport {
  name = 'memory';
  type: TransportType = 'memory';
  entries: LogEntry[] = [];
  maxEntries: number;

  constructor(maxEntries = 1000) {
    this.maxEntries = maxEntries;
  }

  log(entry: LogEntry): void {
    this.entries.push(entry);
    if (this.entries.length > this.maxEntries) {
      this.entries.shift();
    }
  }

  clear(): void {
    this.entries = [];
  }

  getEntries(filter?: { level?: LogLevel; logger?: string }): LogEntry[] {
    let result = this.entries;
    
    if (filter?.level) {
      const minLevel = LOG_LEVEL_VALUES[filter.level];
      result = result.filter((e) => LOG_LEVEL_VALUES[e.level] >= minLevel);
    }
    
    if (filter?.logger) {
      result = result.filter((e) => e.logger === filter.logger);
    }
    
    return result;
  }
}

/**
 * Structured Logger
 */
export class StructuredLogger {
  private config: StructuredLoggerConfig;
  private transports: LogTransport[] = [];
  private contextStack: Array<Record<string, unknown>> = [];
  private correlationId?: string;
  private requestId?: string;
  private userId?: string;

  constructor(config?: Partial<StructuredLoggerConfig>) {
    this.config = { ...DEFAULT_LOGGER_CONFIG, ...config };
    
    // Add default console transport
    this.transports.push(new ConsoleTransport(this.config));
  }

  /**
   * Add transport
   */
  addTransport(transport: LogTransport): void {
    this.transports.push(transport);
  }

  /**
   * Remove transport
   */
  removeTransport(name: string): void {
    this.transports = this.transports.filter((t) => t.name !== name);
  }

  /**
   * Create child logger with additional context
   */
  child(context: Record<string, unknown>): StructuredLogger {
    const child = new StructuredLogger(this.config);
    child.transports = this.transports;
    child.contextStack = [...this.contextStack, context];
    child.correlationId = this.correlationId;
    child.requestId = this.requestId;
    child.userId = this.userId;
    return child;
  }

  /**
   * Set correlation ID
   */
  setCorrelationId(id: string): void {
    this.correlationId = id;
  }

  /**
   * Set request ID
   */
  setRequestId(id: string): void {
    this.requestId = id;
  }

  /**
   * Set user ID
   */
  setUserId(id: string): void {
    this.userId = id;
  }

  /**
   * Push context
   */
  pushContext(context: Record<string, unknown>): void {
    this.contextStack.push(context);
  }

  /**
   * Pop context
   */
  popContext(): Record<string, unknown> | undefined {
    return this.contextStack.pop();
  }

  /**
   * Log at trace level
   */
  trace(message: string, context?: Record<string, unknown>): void {
    this.log('trace', message, context);
  }

  /**
   * Log at debug level
   */
  debug(message: string, context?: Record<string, unknown>): void {
    this.log('debug', message, context);
  }

  /**
   * Log at info level
   */
  info(message: string, context?: Record<string, unknown>): void {
    this.log('info', message, context);
  }

  /**
   * Log at warn level
   */
  warn(message: string, context?: Record<string, unknown>): void {
    this.log('warn', message, context);
  }

  /**
   * Log at error level
   */
  error(message: string, error?: Error | Record<string, unknown>, context?: Record<string, unknown>): void {
    if (error instanceof Error) {
      this.log('error', message, context, error);
    } else {
      this.log('error', message, error);
    }
  }

  /**
   * Log at fatal level
   */
  fatal(message: string, error?: Error | Record<string, unknown>, context?: Record<string, unknown>): void {
    if (error instanceof Error) {
      this.log('fatal', message, context, error);
    } else {
      this.log('fatal', message, error);
    }
  }

  /**
   * Log with timing
   */
  timed<T>(level: LogLevel, message: string, fn: () => T, context?: Record<string, unknown>): T {
    const start = Date.now();
    try {
      const result = fn();
      const duration = Date.now() - start;
      this.log(level, message, { ...context, duration });
      return result;
    } catch (error) {
      const duration = Date.now() - start;
      this.log('error', `${message} (failed)`, { ...context, duration }, error as Error);
      throw error;
    }
  }

  /**
   * Log with async timing
   */
  async timedAsync<T>(
    level: LogLevel, 
    message: string, 
    fn: () => Promise<T>, 
    context?: Record<string, unknown>
  ): Promise<T> {
    const start = Date.now();
    try {
      const result = await fn();
      const duration = Date.now() - start;
      this.log(level, message, { ...context, duration });
      return result;
    } catch (error) {
      const duration = Date.now() - start;
      this.log('error', `${message} (failed)`, { ...context, duration }, error as Error);
      throw error;
    }
  }

  /**
   * Create scoped logger for a specific operation
   */
  scope(operation: string, metadata?: Record<string, unknown>): ScopedLogger {
    return new ScopedLogger(this, operation, metadata);
  }

  /**
   * Core log method
   */
  private log(
    level: LogLevel,
    message: string,
    context?: Record<string, unknown>,
    error?: Error
  ): void {
    // Check level
    if (LOG_LEVEL_VALUES[level] < LOG_LEVEL_VALUES[this.config.level]) {
      return;
    }

    // Build merged context
    const mergedContext = this.buildContext(context);

    // Redact sensitive fields
    const redactedContext = this.redactSensitive(mergedContext);

    // Build entry
    const entry: LogEntry = {
      timestamp: new Date(),
      level,
      message,
      logger: this.config.name,
      correlationId: this.correlationId,
      requestId: this.requestId,
      userId: this.userId,
      context: redactedContext,
    };

    // Add error info
    if (error) {
      entry.error = {
        name: error.name,
        message: error.message,
        stack: error.stack,
        code: (error as any).code,
      };
    }

    // Extract duration from context
    if (context?.duration !== undefined) {
      entry.duration = context.duration as number;
      if (entry.context) {
        delete entry.context.duration;
      }
    }

    // Send to transports
    for (const transport of this.transports) {
      try {
        transport.log(entry);
      } catch (e) {
        console.error(`Logger transport error: ${e}`);
      }
    }
  }

  /**
   * Build merged context
   */
  private buildContext(context?: Record<string, unknown>): Record<string, unknown> | undefined {
    const parts = [
      this.config.defaultContext,
      ...this.contextStack,
      context,
    ].filter(Boolean) as Record<string, unknown>[];

    if (parts.length === 0) return undefined;

    return parts.reduce((acc, part) => ({ ...acc, ...part }), {});
  }

  /**
   * Redact sensitive fields
   */
  private redactSensitive(obj?: Record<string, unknown>): Record<string, unknown> | undefined {
    if (!obj || !this.config.redactFields?.length) return obj;

    const redact = (value: unknown, depth: number): unknown => {
      if (depth > this.config.maxContextDepth) return '[MAX_DEPTH]';

      if (typeof value !== 'object' || value === null) return value;

      if (Array.isArray(value)) {
        return value.map((v) => redact(v, depth + 1));
      }

      const result: Record<string, unknown> = {};
      for (const [key, val] of Object.entries(value)) {
        if (this.config.redactFields?.some((f) => 
          key.toLowerCase().includes(f.toLowerCase())
        )) {
          result[key] = '[REDACTED]';
        } else {
          result[key] = redact(val, depth + 1);
        }
      }
      return result;
    };

    return redact(obj, 0) as Record<string, unknown>;
  }

  /**
   * Flush all transports
   */
  async flush(): Promise<void> {
    for (const transport of this.transports) {
      if (transport.flush) {
        await transport.flush();
      }
    }
  }

  /**
   * Close all transports
   */
  async close(): Promise<void> {
    for (const transport of this.transports) {
      if (transport.close) {
        await transport.close();
      }
    }
  }

  /**
   * Set log level
   */
  setLevel(level: LogLevel): void {
    this.config.level = level;
  }

  /**
   * Get log level
   */
  getLevel(): LogLevel {
    return this.config.level;
  }

  /**
   * Check if level is enabled
   */
  isLevelEnabled(level: LogLevel): boolean {
    return LOG_LEVEL_VALUES[level] >= LOG_LEVEL_VALUES[this.config.level];
  }
}

/**
 * Scoped logger for operations
 */
export class ScopedLogger {
  private logger: StructuredLogger;
  private operation: string;
  private metadata?: Record<string, unknown>;
  private startTime: number;
  private steps: Array<{ name: string; duration: number }> = [];
  private lastStepTime: number;

  constructor(logger: StructuredLogger, operation: string, metadata?: Record<string, unknown>) {
    this.logger = logger;
    this.operation = operation;
    this.metadata = metadata;
    this.startTime = Date.now();
    this.lastStepTime = this.startTime;

    this.logger.info(`Starting: ${operation}`, { ...metadata, event: 'start' });
  }

  /**
   * Log a step
   */
  step(name: string, context?: Record<string, unknown>): void {
    const now = Date.now();
    const stepDuration = now - this.lastStepTime;
    this.steps.push({ name, duration: stepDuration });
    this.lastStepTime = now;

    this.logger.debug(`${this.operation} > ${name}`, {
      ...this.metadata,
      ...context,
      step: name,
      stepDuration,
      event: 'step',
    });
  }

  /**
   * Log success
   */
  success(result?: unknown, context?: Record<string, unknown>): void {
    const duration = Date.now() - this.startTime;

    this.logger.info(`Completed: ${this.operation}`, {
      ...this.metadata,
      ...context,
      duration,
      steps: this.steps,
      result: result !== undefined ? result : undefined,
      event: 'success',
    });
  }

  /**
   * Log failure
   */
  failure(error: Error, context?: Record<string, unknown>): void {
    const duration = Date.now() - this.startTime;

    this.logger.error(`Failed: ${this.operation}`, error, {
      ...this.metadata,
      ...context,
      duration,
      steps: this.steps,
      event: 'failure',
    });
  }

  /**
   * Log progress
   */
  progress(current: number, total: number, message?: string): void {
    const percentage = Math.round((current / total) * 100);

    this.logger.debug(`${this.operation} progress: ${percentage}%`, {
      ...this.metadata,
      current,
      total,
      percentage,
      message,
      event: 'progress',
    });
  }
}

/**
 * Create structured logger instance
 */
export function createStructuredLogger(config?: Partial<StructuredLoggerConfig>): StructuredLogger {
  return new StructuredLogger(config);
}

/**
 * Global logger instance
 */
export const logger = new StructuredLogger({ name: 'musubix' });

/**
 * Request context helper
 */
export function withRequestContext<T>(
  logger: StructuredLogger,
  correlationId: string,
  requestId: string,
  fn: (logger: StructuredLogger) => T
): T {
  const contextLogger = logger.child({});
  contextLogger.setCorrelationId(correlationId);
  contextLogger.setRequestId(requestId);
  return fn(contextLogger);
}

/**
 * Generate correlation ID
 */
export function generateCorrelationId(): string {
  return `${Date.now().toString(36)}-${Math.random().toString(36).substring(2, 10)}`;
}
