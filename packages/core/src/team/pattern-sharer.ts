/**
 * Pattern Sharer - Share patterns with team via Git
 *
 * Implements: TSK-TEAM-002〜004, REQ-TEAM-003〜005, DES-TEAM-002
 */

import { readFile, writeFile, mkdir, readdir, unlink } from 'node:fs/promises';
import { join } from 'node:path';
import type { SharedPattern, GitResult, SyncStatus } from './types.js';
import { GitClient } from './git-client.js';

/**
 * Pattern Sharer configuration
 */
export interface PatternSharerConfig {
  /** Git client instance */
  gitClient: GitClient;

  /** Auto-commit on share */
  autoCommit?: boolean;

  /** Auto-push after commit */
  autoPush?: boolean;

  /** Include timestamp in pattern file */
  includeTimestamp?: boolean;
}

/**
 * Pattern Sharer class
 */
export class PatternSharer {
  private config: Required<PatternSharerConfig>;
  private gitClient: GitClient;

  constructor(config: PatternSharerConfig) {
    this.config = {
      autoCommit: true,
      autoPush: false,
      includeTimestamp: true,
      ...config,
    };
    this.gitClient = config.gitClient;
  }

  /**
   * Initialize patterns directory
   */
  async init(): Promise<GitResult> {
    const patternsDir = this.gitClient.getPatternsDir();

    try {
      await mkdir(patternsDir, { recursive: true });

      // Create index file
      const indexPath = join(patternsDir, 'index.json');
      await writeFile(
        indexPath,
        JSON.stringify({
          version: '1.0.0',
          patterns: [],
          lastUpdated: new Date().toISOString(),
        }, null, 2)
      );

      return {
        success: true,
        message: 'Patterns directory initialized',
        affectedFiles: [patternsDir, indexPath],
      };
    } catch (error) {
      return {
        success: false,
        message: 'Failed to initialize patterns directory',
        error: error instanceof Error ? error.message : String(error),
      };
    }
  }

  /**
   * Share a pattern with the team
   */
  async sharePattern(pattern: Omit<SharedPattern, 'id'>): Promise<GitResult> {
    const patternsDir = this.gitClient.getPatternsDir();

    // Ensure directory exists
    await mkdir(patternsDir, { recursive: true });

    // Generate pattern ID
    const id = this.generatePatternId(pattern.name);

    const fullPattern: SharedPattern = {
      ...pattern,
      id,
      sharedBy: {
        ...pattern.sharedBy,
        date: new Date(),
      },
    };

    // Write pattern file
    const patternPath = join(patternsDir, `${id}.json`);
    await writeFile(patternPath, JSON.stringify(fullPattern, null, 2));

    // Update index
    await this.updateIndex(fullPattern, 'add');

    // Auto-commit if enabled
    if (this.config.autoCommit) {
      await this.gitClient.add([patternPath]);
      const commitResult = await this.gitClient.commit(
        `[musubix-team] Share pattern: ${pattern.name}`
      );

      if (!commitResult.success) {
        return commitResult;
      }

      // Auto-push if enabled
      if (this.config.autoPush) {
        const pushResult = await this.gitClient.push();
        if (!pushResult.success) {
          return {
            success: false,
            message: 'Pattern shared locally but failed to push',
            error: 'Push failed',
          };
        }
      }
    }

    return {
      success: true,
      message: `Pattern ${pattern.name} shared successfully`,
      affectedFiles: [patternPath],
    };
  }

  /**
   * Get a pattern by ID
   */
  async getPattern(id: string): Promise<SharedPattern | null> {
    const patternPath = join(this.gitClient.getPatternsDir(), `${id}.json`);

    try {
      const content = await readFile(patternPath, 'utf-8');
      return JSON.parse(content);
    } catch {
      return null;
    }
  }

  /**
   * List all patterns
   */
  async listPatterns(): Promise<SharedPattern[]> {
    const patternsDir = this.gitClient.getPatternsDir();
    const patterns: SharedPattern[] = [];

    try {
      const files = await readdir(patternsDir);

      for (const file of files) {
        if (file.endsWith('.json') && file !== 'index.json') {
          const content = await readFile(join(patternsDir, file), 'utf-8');
          patterns.push(JSON.parse(content));
        }
      }
    } catch {
      // Directory doesn't exist
    }

    return patterns;
  }

  /**
   * Search patterns
   */
  async searchPatterns(query: string, filters?: {
    type?: SharedPattern['type'];
    tags?: string[];
    applicableTo?: string[];
  }): Promise<SharedPattern[]> {
    const patterns = await this.listPatterns();
    const queryLower = query.toLowerCase();

    return patterns.filter((pattern) => {
      // Text search
      const matchesQuery =
        pattern.name.toLowerCase().includes(queryLower) ||
        pattern.description.toLowerCase().includes(queryLower) ||
        pattern.content.toLowerCase().includes(queryLower);

      if (!matchesQuery) return false;

      // Type filter
      if (filters?.type && pattern.type !== filters.type) return false;

      // Tags filter
      if (filters?.tags && filters.tags.length > 0) {
        const patternTags = pattern.tags ?? [];
        if (!filters.tags.some((tag) => patternTags.includes(tag))) return false;
      }

      // ApplicableTo filter
      if (filters?.applicableTo && filters.applicableTo.length > 0) {
        const applicable = pattern.applicableTo ?? [];
        if (!filters.applicableTo.some((a) => applicable.includes(a))) return false;
      }

      return true;
    });
  }

  /**
   * Adopt a pattern (increment counter)
   */
  async adoptPattern(id: string): Promise<GitResult> {
    const pattern = await this.getPattern(id);

    if (!pattern) {
      return {
        success: false,
        message: `Pattern ${id} not found`,
      };
    }

    pattern.adoptionCount = (pattern.adoptionCount ?? 0) + 1;

    const patternPath = join(this.gitClient.getPatternsDir(), `${id}.json`);
    await writeFile(patternPath, JSON.stringify(pattern, null, 2));

    if (this.config.autoCommit) {
      await this.gitClient.add([patternPath]);
      await this.gitClient.commit(`[musubix-team] Adopt pattern: ${pattern.name}`);
    }

    return {
      success: true,
      message: `Pattern ${pattern.name} adopted (count: ${pattern.adoptionCount})`,
    };
  }

  /**
   * Rate a pattern
   */
  async ratePattern(id: string, rating: number): Promise<GitResult> {
    if (rating < 1 || rating > 5) {
      return {
        success: false,
        message: 'Rating must be between 1 and 5',
      };
    }

    const pattern = await this.getPattern(id);

    if (!pattern) {
      return {
        success: false,
        message: `Pattern ${id} not found`,
      };
    }

    // Simple average (in real impl, would track individual ratings)
    const oldRating = pattern.rating ?? 3;
    const oldCount = pattern.adoptionCount ?? 1;
    pattern.rating = (oldRating * oldCount + rating) / (oldCount + 1);

    const patternPath = join(this.gitClient.getPatternsDir(), `${id}.json`);
    await writeFile(patternPath, JSON.stringify(pattern, null, 2));

    if (this.config.autoCommit) {
      await this.gitClient.add([patternPath]);
      await this.gitClient.commit(`[musubix-team] Rate pattern: ${pattern.name}`);
    }

    return {
      success: true,
      message: `Pattern ${pattern.name} rated ${rating}/5`,
    };
  }

  /**
   * Delete a pattern
   */
  async deletePattern(id: string): Promise<GitResult> {
    const pattern = await this.getPattern(id);

    if (!pattern) {
      return {
        success: false,
        message: `Pattern ${id} not found`,
      };
    }

    const patternPath = join(this.gitClient.getPatternsDir(), `${id}.json`);

    try {
      await unlink(patternPath);
      await this.updateIndex(pattern, 'remove');

      if (this.config.autoCommit) {
        await this.gitClient.add([patternPath]);
        await this.gitClient.commit(`[musubix-team] Remove pattern: ${pattern.name}`);
      }

      return {
        success: true,
        message: `Pattern ${pattern.name} deleted`,
      };
    } catch (error) {
      return {
        success: false,
        message: 'Failed to delete pattern',
        error: error instanceof Error ? error.message : String(error),
      };
    }
  }

  /**
   * Sync patterns with remote
   */
  async sync(): Promise<SyncStatus> {
    // Fetch latest
    const fetchResult = await this.gitClient.fetch();
    if (!fetchResult.success) {
      return {
        status: 'error',
        pendingChanges: 0,
        error: fetchResult.error,
      };
    }

    // Pull changes
    const pullResult = await this.gitClient.pull();
    if (!pullResult.success) {
      if (pullResult.conflicts && pullResult.conflicts.length > 0) {
        return {
          status: 'conflict',
          pendingChanges: pullResult.conflicts.length,
          conflicts: pullResult.conflicts.map((c) => ({
            path: c,
            type: 'modified' as const,
          })),
        };
      }
      return {
        status: 'error',
        pendingChanges: 0,
        error: 'Pull failed',
      };
    }

    // Check for pending changes
    const status = await this.gitClient.status();
    const pendingChanges = status.length;

    // Push if there are local changes
    if (pendingChanges > 0 && this.config.autoPush) {
      const pushResult = await this.gitClient.push();
      if (!pushResult.success) {
        return {
          status: 'pending',
          pendingChanges,
          error: 'Push failed',
        };
      }
    }

    return {
      status: pendingChanges > 0 ? 'pending' : 'synced',
      pendingChanges,
      lastSync: new Date(),
    };
  }

  /**
   * Generate pattern ID
   */
  private generatePatternId(name: string): string {
    const slug = name
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, '-')
      .replace(/^-|-$/g, '');
    const timestamp = Date.now().toString(36);
    return `${slug}-${timestamp}`;
  }

  /**
   * Update patterns index
   */
  private async updateIndex(
    pattern: SharedPattern,
    action: 'add' | 'remove'
  ): Promise<void> {
    const indexPath = join(this.gitClient.getPatternsDir(), 'index.json');

    let index: {
      version: string;
      patterns: Array<{ id: string; name: string; type: string }>;
      lastUpdated: string;
    };

    try {
      const content = await readFile(indexPath, 'utf-8');
      index = JSON.parse(content);
    } catch {
      index = { version: '1.0.0', patterns: [], lastUpdated: '' };
    }

    if (action === 'add') {
      // Remove existing entry if any
      index.patterns = index.patterns.filter((p) => p.id !== pattern.id);
      // Add new entry
      index.patterns.push({
        id: pattern.id,
        name: pattern.name,
        type: pattern.type,
      });
    } else {
      index.patterns = index.patterns.filter((p) => p.id !== pattern.id);
    }

    index.lastUpdated = new Date().toISOString();
    await writeFile(indexPath, JSON.stringify(index, null, 2));
  }
}

/**
 * Create a Pattern Sharer instance
 */
export function createPatternSharer(config: PatternSharerConfig): PatternSharer {
  return new PatternSharer(config);
}
