/**
 * Knowledge Graph Pull Request (KGPR) - Notification Service
 *
 * Multi-channel notification system for KGPR events
 *
 * @packageDocumentation
 * @module @nahisaho/yata-global/kgpr
 *
 * @see REQ-KGPR-003
 * @see TSK-KGPR-005
 */

import { EventEmitter } from 'events';
import * as fs from 'fs';
import * as path from 'path';

/**
 * Notification event types
 */
export type NotificationEventType =
  | 'KGPR_CREATED'
  | 'KGPR_SUBMITTED'
  | 'KGPR_REVIEWED'
  | 'KGPR_APPROVED'
  | 'KGPR_CHANGES_REQUESTED'
  | 'KGPR_MERGED'
  | 'KGPR_CLOSED'
  | 'KGPR_COMMENTED';

/**
 * Notification payload
 */
export interface NotificationPayload {
  /** Event type */
  type: NotificationEventType;
  /** KGPR ID */
  kgprId: string;
  /** KGPR title */
  title?: string;
  /** Event message */
  message?: string;
  /** Author ID */
  authorId?: string;
  /** Author name */
  authorName?: string;
  /** Additional metadata */
  metadata?: Record<string, unknown>;
  /** Event timestamp */
  timestamp?: Date;
}

/**
 * Notification channel interface
 */
export interface NotificationChannel {
  /** Channel name */
  readonly name: string;
  /** Send notification */
  send(payload: NotificationPayload): Promise<NotificationResult>;
  /** Check if channel is enabled */
  isEnabled(): boolean;
}

/**
 * Notification result
 */
export interface NotificationResult {
  /** Whether notification was sent successfully */
  success: boolean;
  /** Channel name */
  channel: string;
  /** Error message (if failed) */
  error?: string;
  /** Response data (if available) */
  response?: unknown;
}

/**
 * Notification service configuration
 */
export interface NotificationServiceConfig {
  /** Webhook URL for HTTP notifications */
  webhookUrl?: string;
  /** Webhook headers */
  webhookHeaders?: Record<string, string>;
  /** File path for file-based notifications */
  filePath?: string;
  /** Enable CLI output */
  cliEnabled?: boolean;
  /** CLI output stream (default: process.stdout) */
  cliStream?: NodeJS.WritableStream;
  /** Enable colored CLI output */
  cliColored?: boolean;
}

// ============================================================================
// CLI Notification Channel
// ============================================================================

/**
 * CLI Notification Channel
 *
 * Outputs notifications to the terminal/console
 */
export class CLINotificationChannel implements NotificationChannel {
  readonly name = 'cli';
  private enabled: boolean;
  private stream: NodeJS.WritableStream;
  private colored: boolean;

  constructor(options: {
    enabled?: boolean;
    stream?: NodeJS.WritableStream;
    colored?: boolean;
  } = {}) {
    this.enabled = options.enabled ?? true;
    this.stream = options.stream ?? process.stdout;
    this.colored = options.colored ?? true;
  }

  isEnabled(): boolean {
    return this.enabled;
  }

  async send(payload: NotificationPayload): Promise<NotificationResult> {
    if (!this.enabled) {
      return { success: false, channel: this.name, error: 'Channel disabled' };
    }

    try {
      const message = this.formatMessage(payload);
      this.stream.write(message + '\n');
      return { success: true, channel: this.name };
    } catch (error) {
      return {
        success: false,
        channel: this.name,
        error: error instanceof Error ? error.message : 'Unknown error',
      };
    }
  }

  private formatMessage(payload: NotificationPayload): string {
    const timestamp = (payload.timestamp ?? new Date()).toISOString();
    const typeLabel = this.formatEventType(payload.type);
    const titlePart = payload.title ? ` - ${payload.title}` : '';
    const messagePart = payload.message ? `\n  ${payload.message}` : '';

    if (this.colored) {
      const color = this.getTypeColor(payload.type);
      return `${this.dim(timestamp)} ${color}[${typeLabel}]${this.reset()} ${payload.kgprId}${titlePart}${messagePart}`;
    }

    return `${timestamp} [${typeLabel}] ${payload.kgprId}${titlePart}${messagePart}`;
  }

  private formatEventType(type: NotificationEventType): string {
    return type.replace('KGPR_', '').replace(/_/g, ' ');
  }

  private getTypeColor(type: NotificationEventType): string {
    switch (type) {
      case 'KGPR_CREATED':
        return '\x1b[36m'; // Cyan
      case 'KGPR_SUBMITTED':
        return '\x1b[33m'; // Yellow
      case 'KGPR_REVIEWED':
        return '\x1b[34m'; // Blue
      case 'KGPR_APPROVED':
        return '\x1b[32m'; // Green
      case 'KGPR_CHANGES_REQUESTED':
        return '\x1b[31m'; // Red
      case 'KGPR_MERGED':
        return '\x1b[35m'; // Magenta
      case 'KGPR_CLOSED':
        return '\x1b[90m'; // Gray
      case 'KGPR_COMMENTED':
        return '\x1b[37m'; // White
      default:
        return '\x1b[0m'; // Reset
    }
  }

  private dim(text: string): string {
    return `\x1b[2m${text}\x1b[22m`;
  }

  private reset(): string {
    return '\x1b[0m';
  }
}

// ============================================================================
// Webhook Notification Channel
// ============================================================================

/**
 * Webhook Notification Channel
 *
 * Sends notifications via HTTP webhook
 */
export class WebhookNotificationChannel implements NotificationChannel {
  readonly name = 'webhook';
  private url: string;
  private headers: Record<string, string>;
  private enabled: boolean;

  constructor(options: {
    url: string;
    headers?: Record<string, string>;
    enabled?: boolean;
  }) {
    this.url = options.url;
    this.headers = options.headers ?? {};
    this.enabled = options.enabled ?? true;
  }

  isEnabled(): boolean {
    return this.enabled && !!this.url;
  }

  async send(payload: NotificationPayload): Promise<NotificationResult> {
    if (!this.isEnabled()) {
      return { success: false, channel: this.name, error: 'Channel disabled or URL not configured' };
    }

    try {
      const body = JSON.stringify({
        ...payload,
        timestamp: (payload.timestamp ?? new Date()).toISOString(),
      });

      const response = await fetch(this.url, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          ...this.headers,
        },
        body,
      });

      if (!response.ok) {
        return {
          success: false,
          channel: this.name,
          error: `HTTP ${response.status}: ${response.statusText}`,
          response: { status: response.status, statusText: response.statusText },
        };
      }

      let responseData: unknown;
      try {
        responseData = await response.json();
      } catch {
        responseData = await response.text();
      }

      return {
        success: true,
        channel: this.name,
        response: responseData,
      };
    } catch (error) {
      return {
        success: false,
        channel: this.name,
        error: error instanceof Error ? error.message : 'Unknown error',
      };
    }
  }
}

// ============================================================================
// File Notification Channel
// ============================================================================

/**
 * File Notification Channel
 *
 * Appends notifications to a log file
 */
export class FileNotificationChannel implements NotificationChannel {
  readonly name = 'file';
  private filePath: string;
  private enabled: boolean;

  constructor(options: {
    filePath: string;
    enabled?: boolean;
  }) {
    this.filePath = options.filePath;
    this.enabled = options.enabled ?? true;
  }

  isEnabled(): boolean {
    return this.enabled && !!this.filePath;
  }

  async send(payload: NotificationPayload): Promise<NotificationResult> {
    if (!this.isEnabled()) {
      return { success: false, channel: this.name, error: 'Channel disabled or file path not configured' };
    }

    try {
      // Ensure directory exists
      const dir = path.dirname(this.filePath);
      if (!fs.existsSync(dir)) {
        fs.mkdirSync(dir, { recursive: true });
      }

      const entry = this.formatEntry(payload);
      fs.appendFileSync(this.filePath, entry + '\n', 'utf-8');

      return { success: true, channel: this.name };
    } catch (error) {
      return {
        success: false,
        channel: this.name,
        error: error instanceof Error ? error.message : 'Unknown error',
      };
    }
  }

  private formatEntry(payload: NotificationPayload): string {
    const timestamp = (payload.timestamp ?? new Date()).toISOString();
    return JSON.stringify({
      timestamp,
      type: payload.type,
      kgprId: payload.kgprId,
      title: payload.title,
      message: payload.message,
      authorId: payload.authorId,
      authorName: payload.authorName,
      metadata: payload.metadata,
    });
  }
}

// ============================================================================
// Notification Service
// ============================================================================

/**
 * NotificationService events
 */
export interface NotificationServiceEvents {
  'notification:sent': { payload: NotificationPayload; results: NotificationResult[] };
  'notification:failed': { payload: NotificationPayload; errors: NotificationResult[] };
  'error': Error;
}

/**
 * Notification Service
 *
 * Multi-channel notification system for KGPR events
 *
 * @example
 * ```typescript
 * const service = new NotificationService({
 *   webhookUrl: 'https://example.com/webhook',
 *   cliEnabled: true,
 *   filePath: './notifications.log',
 * });
 *
 * await service.notify({
 *   type: 'KGPR_SUBMITTED',
 *   kgprId: 'KGPR-20260106-001',
 *   title: 'Add user authentication',
 * });
 * ```
 */
export class NotificationService extends EventEmitter {
  private channels: Map<string, NotificationChannel> = new Map();

  constructor(config: NotificationServiceConfig = {}) {
    super();

    // Initialize CLI channel
    if (config.cliEnabled !== false) {
      this.addChannel(new CLINotificationChannel({
        enabled: config.cliEnabled ?? true,
        stream: config.cliStream,
        colored: config.cliColored ?? true,
      }));
    }

    // Initialize Webhook channel
    if (config.webhookUrl) {
      this.addChannel(new WebhookNotificationChannel({
        url: config.webhookUrl,
        headers: config.webhookHeaders,
      }));
    }

    // Initialize File channel
    if (config.filePath) {
      this.addChannel(new FileNotificationChannel({
        filePath: config.filePath,
      }));
    }
  }

  /**
   * Add a notification channel
   */
  addChannel(channel: NotificationChannel): void {
    this.channels.set(channel.name, channel);
  }

  /**
   * Remove a notification channel
   */
  removeChannel(name: string): boolean {
    return this.channels.delete(name);
  }

  /**
   * Get a notification channel by name
   */
  getChannel(name: string): NotificationChannel | undefined {
    return this.channels.get(name);
  }

  /**
   * List all registered channels
   */
  listChannels(): NotificationChannel[] {
    return Array.from(this.channels.values());
  }

  /**
   * Send notification to all enabled channels
   */
  async notify(payload: NotificationPayload): Promise<NotificationResult[]> {
    const results: NotificationResult[] = [];
    const enabledChannels = Array.from(this.channels.values()).filter((ch) => ch.isEnabled());

    if (enabledChannels.length === 0) {
      return results;
    }

    // Ensure timestamp
    const payloadWithTimestamp: NotificationPayload = {
      ...payload,
      timestamp: payload.timestamp ?? new Date(),
    };

    // Send to all channels in parallel
    const promises = enabledChannels.map(async (channel) => {
      try {
        return await channel.send(payloadWithTimestamp);
      } catch (error) {
        return {
          success: false,
          channel: channel.name,
          error: error instanceof Error ? error.message : 'Unknown error',
        };
      }
    });

    const allResults = await Promise.all(promises);
    results.push(...allResults);

    // Emit events
    const failures = results.filter((r) => !r.success);
    if (failures.length > 0) {
      this.emit('notification:failed', { payload: payloadWithTimestamp, errors: failures });
    }

    const successes = results.filter((r) => r.success);
    if (successes.length > 0) {
      this.emit('notification:sent', { payload: payloadWithTimestamp, results: successes });
    }

    return results;
  }

  /**
   * Send notification to specific channel only
   */
  async notifyChannel(channelName: string, payload: NotificationPayload): Promise<NotificationResult> {
    const channel = this.channels.get(channelName);
    if (!channel) {
      return {
        success: false,
        channel: channelName,
        error: `Channel '${channelName}' not found`,
      };
    }

    if (!channel.isEnabled()) {
      return {
        success: false,
        channel: channelName,
        error: `Channel '${channelName}' is disabled`,
      };
    }

    const payloadWithTimestamp: NotificationPayload = {
      ...payload,
      timestamp: payload.timestamp ?? new Date(),
    };

    return channel.send(payloadWithTimestamp);
  }

  // ============================================================================
  // Convenience methods for specific events
  // ============================================================================

  /**
   * Notify KGPR created
   */
  async notifyCreated(kgprId: string, title: string, authorName?: string): Promise<NotificationResult[]> {
    return this.notify({
      type: 'KGPR_CREATED',
      kgprId,
      title,
      authorName,
      message: `New KGPR created: ${title}`,
    });
  }

  /**
   * Notify KGPR submitted
   */
  async notifySubmitted(kgprId: string, title: string, authorName?: string): Promise<NotificationResult[]> {
    return this.notify({
      type: 'KGPR_SUBMITTED',
      kgprId,
      title,
      authorName,
      message: `KGPR submitted for review: ${title}`,
    });
  }

  /**
   * Notify KGPR approved
   */
  async notifyApproved(kgprId: string, title: string, reviewerName?: string): Promise<NotificationResult[]> {
    return this.notify({
      type: 'KGPR_APPROVED',
      kgprId,
      title,
      authorName: reviewerName,
      message: `KGPR approved by ${reviewerName ?? 'reviewer'}`,
    });
  }

  /**
   * Notify changes requested
   */
  async notifyChangesRequested(kgprId: string, title: string, reviewerName?: string, comment?: string): Promise<NotificationResult[]> {
    return this.notify({
      type: 'KGPR_CHANGES_REQUESTED',
      kgprId,
      title,
      authorName: reviewerName,
      message: comment ?? `Changes requested by ${reviewerName ?? 'reviewer'}`,
    });
  }

  /**
   * Notify KGPR merged
   */
  async notifyMerged(kgprId: string, title: string): Promise<NotificationResult[]> {
    return this.notify({
      type: 'KGPR_MERGED',
      kgprId,
      title,
      message: `KGPR merged successfully`,
    });
  }

  /**
   * Notify KGPR closed
   */
  async notifyClosed(kgprId: string, title: string, reason?: string): Promise<NotificationResult[]> {
    return this.notify({
      type: 'KGPR_CLOSED',
      kgprId,
      title,
      message: reason ?? `KGPR closed`,
    });
  }

  /**
   * Notify new comment
   */
  async notifyCommented(kgprId: string, title: string, commenterName: string, comment: string): Promise<NotificationResult[]> {
    return this.notify({
      type: 'KGPR_COMMENTED',
      kgprId,
      title,
      authorName: commenterName,
      message: `${commenterName}: ${comment.substring(0, 100)}${comment.length > 100 ? '...' : ''}`,
    });
  }
}
