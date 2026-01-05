/**
 * History Manager - Manages command history persistence
 *
 * @module cli/repl/history-manager
 * @traces DES-CLI-003, REQ-CLI-003
 * @pattern Repository - Abstracts history storage
 */

import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';

/**
 * History manager for REPL commands
 *
 * Persists command history to disk and provides navigation.
 */
export class HistoryManager {
  private history: string[] = [];
  private position: number = -1;
  private readonly maxSize: number;
  private readonly filePath: string;
  private tempLine: string = '';

  /**
   * Create a new history manager
   * @param options - Configuration options
   */
  constructor(options: { maxSize?: number; filePath?: string } = {}) {
    this.maxSize = options.maxSize ?? 1000;
    this.filePath = this.expandPath(options.filePath ?? '~/.musubix/history');
  }

  /**
   * Expand ~ to home directory
   */
  private expandPath(filePath: string): string {
    if (filePath.startsWith('~')) {
      return path.join(os.homedir(), filePath.slice(1));
    }
    return filePath;
  }

  /**
   * Load history from persistent storage
   */
  async load(): Promise<void> {
    try {
      if (fs.existsSync(this.filePath)) {
        const content = await fs.promises.readFile(this.filePath, 'utf-8');
        this.history = content
          .split('\n')
          .filter((line) => line.trim().length > 0)
          .slice(-this.maxSize);
      }
    } catch {
      // If file doesn't exist or can't be read, start with empty history
      this.history = [];
    }
    this.position = this.history.length;
  }

  /**
   * Save current history to persistent storage
   */
  async save(): Promise<void> {
    try {
      const dir = path.dirname(this.filePath);
      if (!fs.existsSync(dir)) {
        await fs.promises.mkdir(dir, { recursive: true });
      }
      const content = this.history.slice(-this.maxSize).join('\n');
      await fs.promises.writeFile(this.filePath, content, 'utf-8');
    } catch (error) {
      // Silently fail on save errors
      console.error('Failed to save history:', error);
    }
  }

  /**
   * Add command to history
   * @param command - The command to add
   */
  add(command: string): void {
    const trimmed = command.trim();
    if (!trimmed) {
      return;
    }

    // Don't add duplicate consecutive commands
    if (this.history.length > 0 && this.history[this.history.length - 1] === trimmed) {
      this.position = this.history.length;
      return;
    }

    this.history.push(trimmed);

    // Trim to max size
    if (this.history.length > this.maxSize) {
      this.history = this.history.slice(-this.maxSize);
    }

    this.position = this.history.length;
    this.tempLine = '';
  }

  /**
   * Get previous command (UP arrow)
   * @param currentLine - Current input line (to save when navigating)
   */
  previous(currentLine?: string): string | undefined {
    if (this.history.length === 0) {
      return undefined;
    }

    // Save current line when first pressing UP
    if (this.position === this.history.length && currentLine !== undefined) {
      this.tempLine = currentLine;
    }

    if (this.position > 0) {
      this.position--;
      return this.history[this.position];
    }

    return this.history[0];
  }

  /**
   * Get next command (DOWN arrow)
   */
  next(): string | undefined {
    if (this.position >= this.history.length - 1) {
      this.position = this.history.length;
      return this.tempLine;
    }

    this.position++;
    return this.history[this.position];
  }

  /**
   * Reset position to end of history
   */
  resetPosition(): void {
    this.position = this.history.length;
    this.tempLine = '';
  }

  /**
   * Search history for matching commands
   * @param query - Search query
   */
  search(query: string): string[] {
    if (!query) {
      return [];
    }

    const lowerQuery = query.toLowerCase();
    return this.history.filter((cmd) => cmd.toLowerCase().includes(lowerQuery)).reverse();
  }

  /**
   * Get all history entries
   */
  getAll(): string[] {
    return [...this.history];
  }

  /**
   * Clear all history
   */
  clear(): void {
    this.history = [];
    this.position = 0;
    this.tempLine = '';
  }

  /**
   * Get history size
   */
  get size(): number {
    return this.history.length;
  }
}

/**
 * Create a new history manager
 */
export function createHistoryManager(options?: {
  maxSize?: number;
  filePath?: string;
}): HistoryManager {
  return new HistoryManager(options);
}
