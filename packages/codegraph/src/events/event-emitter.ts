/**
 * @nahisaho/musubix-codegraph - Event System
 *
 * Type-safe event emitter for CodeGraph events
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-codegraph/events
 *
 * @see REQ-CG-API-006
 * @see DES-CG-001
 */

import { EventEmitter } from 'events';
import type { CodeGraphEvents } from '../types.js';

/**
 * Type-safe event emitter for CodeGraph
 *
 * @example
 * ```typescript
 * const emitter = new TypedEventEmitter<CodeGraphEvents>();
 *
 * emitter.on('indexing:progress', (data) => {
 *   console.log(`Progress: ${data.processed}/${data.total}`);
 * });
 *
 * emitter.emit('indexing:progress', { processed: 10, total: 100, currentFile: 'src/index.ts' });
 * ```
 */
export class TypedEventEmitter<TEvents extends Record<string, unknown>> {
  private emitter: EventEmitter;

  constructor() {
    this.emitter = new EventEmitter();
    // Increase max listeners for complex applications
    this.emitter.setMaxListeners(50);
  }

  /**
   * Register an event listener
   */
  on<K extends keyof TEvents>(event: K, listener: (data: TEvents[K]) => void): this {
    this.emitter.on(event as string, listener as (...args: unknown[]) => void);
    return this;
  }

  /**
   * Register a one-time event listener
   */
  once<K extends keyof TEvents>(event: K, listener: (data: TEvents[K]) => void): this {
    this.emitter.once(event as string, listener as (...args: unknown[]) => void);
    return this;
  }

  /**
   * Remove an event listener
   */
  off<K extends keyof TEvents>(event: K, listener: (data: TEvents[K]) => void): this {
    this.emitter.off(event as string, listener as (...args: unknown[]) => void);
    return this;
  }

  /**
   * Remove all listeners for an event
   */
  removeAllListeners<K extends keyof TEvents>(event?: K): this {
    if (event) {
      this.emitter.removeAllListeners(event as string);
    } else {
      this.emitter.removeAllListeners();
    }
    return this;
  }

  /**
   * Emit an event
   */
  emit<K extends keyof TEvents>(event: K, data: TEvents[K]): boolean {
    return this.emitter.emit(event as string, data);
  }

  /**
   * Get listener count for an event
   */
  listenerCount<K extends keyof TEvents>(event: K): number {
    return this.emitter.listenerCount(event as string);
  }

  /**
   * Get all listeners for an event
   */
  listeners<K extends keyof TEvents>(event: K): ((data: TEvents[K]) => void)[] {
    return this.emitter.listeners(event as string) as ((data: TEvents[K]) => void)[];
  }

  /**
   * Wait for an event (Promise-based)
   */
  waitFor<K extends keyof TEvents>(event: K, timeout?: number): Promise<TEvents[K]> {
    return new Promise((resolve, reject) => {
      let timeoutId: NodeJS.Timeout | undefined;

      const listener = (data: TEvents[K]) => {
        if (timeoutId) {
          clearTimeout(timeoutId);
        }
        resolve(data);
      };

      this.once(event, listener);

      if (timeout) {
        timeoutId = setTimeout(() => {
          this.off(event, listener);
          reject(new Error(`Timeout waiting for event: ${String(event)}`));
        }, timeout);
      }
    });
  }
}

/**
 * CodeGraph event emitter with pre-defined event types
 */
export class CodeGraphEventEmitter extends TypedEventEmitter<CodeGraphEvents> {
  /**
   * Emit indexing start event
   */
  emitIndexingStart(path: string): void {
    this.emit('indexing:start', { path, timestamp: new Date() });
  }

  /**
   * Emit indexing progress event
   */
  emitIndexingProgress(processed: number, total: number, currentFile: string): void {
    this.emit('indexing:progress', { processed, total, currentFile });
  }

  /**
   * Emit indexing complete event
   */
  emitIndexingComplete(result: CodeGraphEvents['indexing:complete']): void {
    this.emit('indexing:complete', result);
  }

  /**
   * Emit indexing error event
   */
  emitIndexingError(error: Error, file?: string): void {
    this.emit('indexing:error', { error, file });
  }

  /**
   * Emit query start event
   */
  emitQueryStart(query: CodeGraphEvents['query:start']['query']): void {
    this.emit('query:start', { query });
  }

  /**
   * Emit query complete event
   */
  emitQueryComplete(result: CodeGraphEvents['query:complete']['result'], durationMs: number): void {
    this.emit('query:complete', { result, durationMs });
  }
}

// Export default instance factory
export function createEventEmitter(): CodeGraphEventEmitter {
  return new CodeGraphEventEmitter();
}
