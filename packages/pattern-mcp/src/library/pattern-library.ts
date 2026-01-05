/**
 * @fileoverview Pattern library with local persistence
 * @traceability TSK-PATTERN-005, REQ-PATTERN-001-F005
 */

import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';
import type { Pattern, PatternLibraryConfig } from '../types.js';

/**
 * Pattern library manager with JSON persistence
 * 
 * @description
 * Manages pattern storage locally (no external communication).
 * Supports CRUD operations and import/export.
 */
export class PatternLibrary {
  private patterns: Map<string, Pattern> = new Map();
  private config: PatternLibraryConfig;
  private dirty = false;

  constructor(config: Partial<PatternLibraryConfig> = {}) {
    this.config = {
      storagePath: config.storagePath ?? './storage/patterns/library.json',
      maxPatterns: config.maxPatterns ?? 10000,
      enablePrivacyFilter: config.enablePrivacyFilter ?? true,
    };
  }

  /**
   * Load library from disk
   */
  async load(): Promise<void> {
    try {
      const data = await readFile(this.config.storagePath, 'utf-8');
      const parsed = JSON.parse(data) as { patterns: Pattern[] };
      this.patterns.clear();
      for (const pattern of parsed.patterns) {
        this.patterns.set(pattern.id, pattern);
      }
      this.dirty = false;
    } catch {
      // File doesn't exist yet - start with empty library
      this.patterns.clear();
    }
  }

  /**
   * Save library to disk
   */
  async save(): Promise<void> {
    if (!this.dirty) return;

    const dir = dirname(this.config.storagePath);
    await mkdir(dir, { recursive: true });

    const data = {
      version: '1.0.0',
      updatedAt: new Date().toISOString(),
      patterns: Array.from(this.patterns.values()),
    };

    await writeFile(this.config.storagePath, JSON.stringify(data, null, 2), 'utf-8');
    this.dirty = false;
  }

  /**
   * Add pattern to library
   */
  add(pattern: Pattern): boolean {
    if (this.patterns.size >= this.config.maxPatterns) {
      return false;
    }
    this.patterns.set(pattern.id, pattern);
    this.dirty = true;
    return true;
  }

  /**
   * Get pattern by ID
   */
  get(id: string): Pattern | undefined {
    return this.patterns.get(id);
  }

  /**
   * Update existing pattern
   */
  update(id: string, updates: Partial<Pattern>): boolean {
    const existing = this.patterns.get(id);
    if (!existing) return false;

    const updated: Pattern = {
      ...existing,
      ...updates,
      id: existing.id, // ID cannot be changed
      updatedAt: new Date().toISOString(),
    };
    this.patterns.set(id, updated);
    this.dirty = true;
    return true;
  }

  /**
   * Delete pattern
   */
  delete(id: string): boolean {
    const deleted = this.patterns.delete(id);
    if (deleted) {
      this.dirty = true;
    }
    return deleted;
  }

  /**
   * List all patterns
   */
  list(): Pattern[] {
    return Array.from(this.patterns.values());
  }

  /**
   * Get pattern count
   */
  get size(): number {
    return this.patterns.size;
  }

  /**
   * Export library to JSON string
   */
  export(): string {
    return JSON.stringify({
      version: '1.0.0',
      exportedAt: new Date().toISOString(),
      patterns: Array.from(this.patterns.values()),
    }, null, 2);
  }

  /**
   * Import patterns from JSON string
   */
  import(json: string): number {
    const data = JSON.parse(json) as { patterns: Pattern[] };
    let imported = 0;
    for (const pattern of data.patterns) {
      if (this.add(pattern)) {
        imported++;
      }
    }
    return imported;
  }
}
