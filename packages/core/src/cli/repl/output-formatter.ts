/**
 * Output Formatter - Formats command output
 *
 * @module cli/repl/output-formatter
 * @traces DES-CLI-008, REQ-CLI-008
 * @pattern Strategy - Different formatting strategies
 */

import type { OutputFormat } from './types.js';

/**
 * Output formatter for REPL results
 *
 * Formats data in various formats: JSON, table, YAML.
 */
export class OutputFormatter {
  private defaultFormat: OutputFormat;
  private _useColor: boolean;

  constructor(options: { defaultFormat?: OutputFormat; useColor?: boolean } = {}) {
    this.defaultFormat = options.defaultFormat ?? 'table';
    this._useColor = options.useColor ?? true;
  }

  /**
   * Get whether colors are enabled
   */
  get useColor(): boolean {
    return this._useColor;
  }

  /**
   * Format data according to specified format
   */
  format(data: unknown, format?: OutputFormat): string {
    const fmt = format ?? this.defaultFormat;

    switch (fmt) {
      case 'json':
        return this.formatJson(data);
      case 'yaml':
        return this.formatYaml(data);
      case 'table':
        return this.formatTable(data);
      case 'auto':
      default:
        return this.autoFormat(data);
    }
  }

  /**
   * Format data as JSON
   */
  formatJson(data: unknown): string {
    try {
      return JSON.stringify(data, null, 2);
    } catch {
      return String(data);
    }
  }

  /**
   * Format data as table
   */
  formatTable(data: unknown): string {
    if (!data) {
      return '';
    }

    // Array of objects - display as table
    if (Array.isArray(data) && data.length > 0 && typeof data[0] === 'object') {
      return this.renderTable(data as Record<string, unknown>[]);
    }

    // Single object - display as key-value pairs
    if (typeof data === 'object' && !Array.isArray(data)) {
      return this.renderKeyValue(data as Record<string, unknown>);
    }

    // Array of primitives - display as list
    if (Array.isArray(data)) {
      return data.map((item, i) => `${i + 1}. ${item}`).join('\n');
    }

    // Primitive - display as string
    return String(data);
  }

  /**
   * Format data as YAML
   */
  formatYaml(data: unknown): string {
    return this.toYaml(data, 0);
  }

  /**
   * Auto-detect best format
   */
  autoFormat(data: unknown): string {
    if (!data) {
      return '';
    }

    // Array of objects - use table
    if (Array.isArray(data) && data.length > 0 && typeof data[0] === 'object') {
      return this.formatTable(data);
    }

    // Complex object - use YAML
    if (typeof data === 'object' && !Array.isArray(data)) {
      const depth = this.getObjectDepth(data as Record<string, unknown>);
      if (depth > 2) {
        return this.formatYaml(data);
      }
      return this.formatTable(data);
    }

    return this.formatTable(data);
  }

  /**
   * Render table from array of objects
   */
  private renderTable(rows: Record<string, unknown>[]): string {
    if (rows.length === 0) {
      return '(empty)';
    }

    // Get all unique keys
    const keys = new Set<string>();
    for (const row of rows) {
      for (const key of Object.keys(row)) {
        keys.add(key);
      }
    }
    const columns = Array.from(keys);

    // Calculate column widths
    const widths: Record<string, number> = {};
    for (const col of columns) {
      widths[col] = col.length;
      for (const row of rows) {
        const value = String(row[col] ?? '');
        widths[col] = Math.max(widths[col], value.length);
      }
    }

    // Render header
    const header = columns.map((col) => this.pad(col, widths[col])).join(' │ ');
    const separator = columns.map((col) => '─'.repeat(widths[col])).join('─┼─');

    // Render rows
    const dataRows = rows.map((row) => {
      return columns.map((col) => this.pad(String(row[col] ?? ''), widths[col])).join(' │ ');
    });

    return [header, separator, ...dataRows].join('\n');
  }

  /**
   * Render key-value pairs
   */
  private renderKeyValue(obj: Record<string, unknown>): string {
    const entries = Object.entries(obj);
    if (entries.length === 0) {
      return '(empty)';
    }

    const maxKeyLen = Math.max(...entries.map(([k]) => k.length));
    return entries.map(([key, value]) => {
      const paddedKey = this.pad(key, maxKeyLen);
      const valueStr = typeof value === 'object' ? JSON.stringify(value) : String(value);
      return `${paddedKey}: ${valueStr}`;
    }).join('\n');
  }

  /**
   * Convert to YAML-like format
   */
  private toYaml(data: unknown, indent: number): string {
    const spaces = '  '.repeat(indent);

    if (data === null || data === undefined) {
      return 'null';
    }

    if (typeof data === 'string') {
      return data.includes('\n') ? `|\n${data.split('\n').map(l => spaces + '  ' + l).join('\n')}` : data;
    }

    if (typeof data === 'number' || typeof data === 'boolean') {
      return String(data);
    }

    if (Array.isArray(data)) {
      if (data.length === 0) {
        return '[]';
      }
      return data.map((item) => {
        const itemYaml = this.toYaml(item, indent + 1);
        if (typeof item === 'object' && item !== null) {
          return `${spaces}- ${itemYaml.trim()}`;
        }
        return `${spaces}- ${itemYaml}`;
      }).join('\n');
    }

    if (typeof data === 'object') {
      const entries = Object.entries(data as Record<string, unknown>);
      if (entries.length === 0) {
        return '{}';
      }
      return entries.map(([key, value]) => {
        const valueYaml = this.toYaml(value, indent + 1);
        if (typeof value === 'object' && value !== null && !Array.isArray(value)) {
          return `${spaces}${key}:\n${valueYaml}`;
        }
        if (Array.isArray(value)) {
          return `${spaces}${key}:\n${valueYaml}`;
        }
        return `${spaces}${key}: ${valueYaml}`;
      }).join('\n');
    }

    return String(data);
  }

  /**
   * Pad string to width
   */
  private pad(str: string, width: number): string {
    return str.padEnd(width);
  }

  /**
   * Get object depth
   */
  private getObjectDepth(obj: Record<string, unknown>, depth = 0): number {
    let maxDepth = depth;
    for (const value of Object.values(obj)) {
      if (typeof value === 'object' && value !== null && !Array.isArray(value)) {
        maxDepth = Math.max(maxDepth, this.getObjectDepth(value as Record<string, unknown>, depth + 1));
      }
    }
    return maxDepth;
  }

  /**
   * Set default format
   */
  setDefaultFormat(format: OutputFormat): void {
    this.defaultFormat = format;
  }

  /**
   * Set color mode
   */
  setColorMode(useColor: boolean): void {
    this._useColor = useColor;
  }
}

/**
 * Create a new output formatter
 */
export function createOutputFormatter(options?: {
  defaultFormat?: OutputFormat;
  useColor?: boolean;
}): OutputFormatter {
  return new OutputFormatter(options);
}
