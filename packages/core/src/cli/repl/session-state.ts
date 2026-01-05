/**
 * Session State - Manages REPL session variables
 *
 * @module cli/repl/session-state
 * @traces DES-CLI-007, REQ-CLI-007
 * @pattern State - Encapsulates session state
 */

import type { CommandResult } from './types.js';

/**
 * Session state manager for REPL
 *
 * Manages session variables and last command result.
 * Variables can be set with `set VAR=value` and accessed with `$VAR`.
 */
export class SessionState {
  private variables: Map<string, string> = new Map();
  private lastResult: CommandResult | undefined;

  /**
   * Set a session variable
   * @param key - Variable name
   * @param value - Variable value
   */
  set(key: string, value: string): void {
    if (!key || typeof key !== 'string') {
      throw new Error('Variable name must be a non-empty string');
    }
    this.variables.set(key.toUpperCase(), value);
  }

  /**
   * Get a session variable
   * @param key - Variable name
   * @returns Variable value or undefined
   */
  get(key: string): string | undefined {
    if (key === '_') {
      return this.lastResult?.output;
    }
    return this.variables.get(key.toUpperCase());
  }

  /**
   * Check if a variable exists
   * @param key - Variable name
   */
  has(key: string): boolean {
    if (key === '_') {
      return this.lastResult !== undefined;
    }
    return this.variables.has(key.toUpperCase());
  }

  /**
   * Delete a session variable
   * @param key - Variable name
   */
  delete(key: string): boolean {
    return this.variables.delete(key.toUpperCase());
  }

  /**
   * Get all variables as object
   */
  getAll(): Record<string, string> {
    const result: Record<string, string> = {};
    for (const [key, value] of this.variables) {
      result[key] = value;
    }
    if (this.lastResult) {
      result['_'] = this.lastResult.output;
    }
    return result;
  }

  /**
   * Set last command result
   * @param result - Command result
   */
  setLastResult(result: CommandResult): void {
    this.lastResult = result;
  }

  /**
   * Get last command result
   */
  getLastResult(): CommandResult | undefined {
    return this.lastResult;
  }

  /**
   * Expand variables in a string
   * Replaces $VAR with variable value
   * @param input - Input string
   */
  expand(input: string): string {
    return input.replace(/\$([A-Z_][A-Z0-9_]*)/gi, (match, varName) => {
      const value = this.get(varName);
      return value !== undefined ? value : match;
    });
  }

  /**
   * Clear all session state
   */
  clear(): void {
    this.variables.clear();
    this.lastResult = undefined;
  }

  /**
   * Get number of variables
   */
  get size(): number {
    return this.variables.size;
  }
}

/**
 * Create a new session state instance
 */
export function createSessionState(): SessionState {
  return new SessionState();
}
