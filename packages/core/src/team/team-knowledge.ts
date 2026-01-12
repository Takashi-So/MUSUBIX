/**
 * Team Knowledge - Shared knowledge graph via Git
 *
 * Implements: TSK-TEAM-005〜007, REQ-TEAM-006〜008, DES-TEAM-003
 */

import { readFile, writeFile, mkdir, readdir } from 'node:fs/promises';
import { join } from 'node:path';
import type { TeamKnowledgeEntry, GitResult, SyncStatus, TeamMember } from './types.js';
import { GitClient } from './git-client.js';

/**
 * Team Knowledge configuration
 */
export interface TeamKnowledgeConfig {
  /** Git client instance */
  gitClient: GitClient;

  /** Auto-commit on changes */
  autoCommit?: boolean;

  /** Auto-push after commit */
  autoPush?: boolean;

  /** Knowledge graph version */
  version?: string;
}

/**
 * Knowledge Query options
 */
export interface KnowledgeQueryOptions {
  /** Filter by entity type */
  type?: string;

  /** Filter by category */
  category?: string;

  /** Filter by tags */
  tags?: string[];

  /** Filter by contributor */
  contributorId?: string;

  /** Date range filter */
  dateRange?: {
    start?: Date;
    end?: Date;
  };

  /** Maximum results */
  limit?: number;
}

/**
 * Knowledge Statistics
 */
export interface KnowledgeStats {
  /** Total entries */
  totalEntries: number;

  /** Entries by type */
  byType: Record<string, number>;

  /** Entries by category */
  byCategory: Record<string, number>;

  /** Top contributors */
  topContributors: Array<{
    member: TeamMember | { id: string; name: string; email: string };
    count: number;
  }>;

  /** Recent activity */
  recentActivity: Array<{
    entry: TeamKnowledgeEntry;
    action: 'add' | 'update';
    date: Date;
  }>;

  /** Last sync */
  lastSync?: Date;
}

/**
 * Team Knowledge Manager class
 */
export class TeamKnowledge {
  private config: Required<TeamKnowledgeConfig>;
  private gitClient: GitClient;
  private cache: Map<string, TeamKnowledgeEntry> = new Map();

  constructor(config: TeamKnowledgeConfig) {
    this.config = {
      autoCommit: true,
      autoPush: false,
      version: '1.0.0',
      ...config,
    };
    this.gitClient = config.gitClient;
  }

  /**
   * Initialize knowledge directory
   */
  async init(): Promise<GitResult> {
    const knowledgeDir = this.gitClient.getKnowledgeDir();

    try {
      await mkdir(knowledgeDir, { recursive: true });

      // Create metadata file
      const metaPath = join(knowledgeDir, 'meta.json');
      await writeFile(
        metaPath,
        JSON.stringify({
          version: this.config.version,
          created: new Date().toISOString(),
          lastUpdated: new Date().toISOString(),
          entryCount: 0,
        }, null, 2)
      );

      // Create categories index
      const categoriesPath = join(knowledgeDir, 'categories.json');
      await writeFile(
        categoriesPath,
        JSON.stringify({
          categories: [
            'best-practice',
            'architecture',
            'security',
            'performance',
            'testing',
            'documentation',
            'other',
          ],
        }, null, 2)
      );

      return {
        success: true,
        message: 'Knowledge directory initialized',
        affectedFiles: [knowledgeDir, metaPath, categoriesPath],
      };
    } catch (error) {
      return {
        success: false,
        message: 'Failed to initialize knowledge directory',
        error: error instanceof Error ? error.message : String(error),
      };
    }
  }

  /**
   * Add knowledge entry
   */
  async addEntry(
    entry: Omit<TeamKnowledgeEntry, 'id' | 'timestamp'>
  ): Promise<GitResult> {
    const knowledgeDir = this.gitClient.getKnowledgeDir();
    await mkdir(knowledgeDir, { recursive: true });

    // Generate ID
    const id = this.generateId(entry.title);

    const fullEntry: TeamKnowledgeEntry = {
      ...entry,
      id,
      timestamp: new Date(),
    };

    // Write entry file
    const entryPath = join(knowledgeDir, `${id}.json`);
    await writeFile(entryPath, JSON.stringify(fullEntry, null, 2));

    // Update cache
    this.cache.set(id, fullEntry);

    // Update metadata
    await this.updateMetadata();

    // Auto-commit if enabled
    if (this.config.autoCommit) {
      await this.gitClient.add([entryPath]);
      const commitResult = await this.gitClient.commit(
        `[musubix-team] Add knowledge: ${entry.title}`
      );

      if (!commitResult.success) {
        return commitResult;
      }

      if (this.config.autoPush) {
        await this.gitClient.push();
      }
    }

    return {
      success: true,
      message: `Knowledge entry "${entry.title}" added`,
      affectedFiles: [entryPath],
    };
  }

  /**
   * Get knowledge entry by ID
   */
  async getEntry(id: string): Promise<TeamKnowledgeEntry | null> {
    // Check cache first
    if (this.cache.has(id)) {
      return this.cache.get(id) ?? null;
    }

    const entryPath = join(this.gitClient.getKnowledgeDir(), `${id}.json`);

    try {
      const content = await readFile(entryPath, 'utf-8');
      const entry = JSON.parse(content);
      this.cache.set(id, entry);
      return entry;
    } catch {
      return null;
    }
  }

  /**
   * Update knowledge entry
   */
  async updateEntry(
    id: string,
    updates: Partial<Omit<TeamKnowledgeEntry, 'id'>>
  ): Promise<GitResult> {
    const entry = await this.getEntry(id);

    if (!entry) {
      return {
        success: false,
        message: `Knowledge entry ${id} not found`,
      };
    }

    const updatedEntry: TeamKnowledgeEntry = {
      ...entry,
      ...updates,
      id, // Preserve original ID
      timestamp: new Date(),
    };

    const entryPath = join(this.gitClient.getKnowledgeDir(), `${id}.json`);
    await writeFile(entryPath, JSON.stringify(updatedEntry, null, 2));

    // Update cache
    this.cache.set(id, updatedEntry);

    if (this.config.autoCommit) {
      await this.gitClient.add([entryPath]);
      await this.gitClient.commit(`[musubix-team] Update knowledge: ${entry.title}`);

      if (this.config.autoPush) {
        await this.gitClient.push();
      }
    }

    return {
      success: true,
      message: `Knowledge entry "${entry.title}" updated`,
    };
  }

  /**
   * Query knowledge entries
   */
  async query(options?: KnowledgeQueryOptions): Promise<TeamKnowledgeEntry[]> {
    const entries = await this.loadAllEntries();

    if (!options) {
      return entries;
    }

    let filtered = entries;

    // Type filter
    if (options.type) {
      filtered = filtered.filter((e) => e.type === options.type);
    }

    // Category filter
    if (options.category) {
      filtered = filtered.filter((e) => e.category === options.category);
    }

    // Tags filter
    if (options.tags && options.tags.length > 0) {
      filtered = filtered.filter((e) =>
        options.tags?.some((tag) => e.tags?.includes(tag))
      );
    }

    // Contributor filter
    if (options.contributorId) {
      filtered = filtered.filter(
        (e) => e.contributor.id === options.contributorId
      );
    }

    // Date range filter
    if (options.dateRange) {
      const { start, end } = options.dateRange;
      filtered = filtered.filter((e) => {
        const date = new Date(e.timestamp);
        if (start && date < start) return false;
        if (end && date > end) return false;
        return true;
      });
    }

    // Sort by timestamp (newest first)
    filtered.sort((a, b) =>
      new Date(b.timestamp).getTime() - new Date(a.timestamp).getTime()
    );

    // Apply limit
    if (options.limit) {
      filtered = filtered.slice(0, options.limit);
    }

    return filtered;
  }

  /**
   * Search knowledge entries
   */
  async search(query: string): Promise<TeamKnowledgeEntry[]> {
    const entries = await this.loadAllEntries();
    const queryLower = query.toLowerCase();

    return entries.filter((e) =>
      e.title.toLowerCase().includes(queryLower) ||
      e.content.toLowerCase().includes(queryLower) ||
      e.tags?.some((tag) => tag.toLowerCase().includes(queryLower))
    );
  }

  /**
   * Get knowledge statistics
   */
  async getStats(): Promise<KnowledgeStats> {
    const entries = await this.loadAllEntries();

    // Count by type
    const byType: Record<string, number> = {};
    entries.forEach((e) => {
      byType[e.type] = (byType[e.type] ?? 0) + 1;
    });

    // Count by category
    const byCategory: Record<string, number> = {};
    entries.forEach((e) => {
      byCategory[e.category] = (byCategory[e.category] ?? 0) + 1;
    });

    // Top contributors
    const contributorCounts = new Map<string, { member: TeamKnowledgeEntry['contributor']; count: number }>();
    entries.forEach((e) => {
      const existing = contributorCounts.get(e.contributor.id);
      if (existing) {
        existing.count++;
      } else {
        contributorCounts.set(e.contributor.id, {
          member: e.contributor,
          count: 1,
        });
      }
    });
    const topContributors = Array.from(contributorCounts.values())
      .sort((a, b) => b.count - a.count)
      .slice(0, 10);

    // Recent activity
    const recentActivity = entries
      .sort((a, b) =>
        new Date(b.timestamp).getTime() - new Date(a.timestamp).getTime()
      )
      .slice(0, 10)
      .map((entry) => ({
        entry,
        action: 'add' as const, // In real impl, track actual actions
        date: new Date(entry.timestamp),
      }));

    return {
      totalEntries: entries.length,
      byType,
      byCategory,
      topContributors,
      recentActivity,
    };
  }

  /**
   * Sync knowledge with remote
   */
  async sync(): Promise<SyncStatus> {
    // Clear cache to force reload
    this.cache.clear();

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
   * Export knowledge to markdown
   */
  async exportToMarkdown(): Promise<string> {
    const entries = await this.loadAllEntries();
    const stats = await this.getStats();

    let md = '# Team Knowledge Base\n\n';
    md += `**Total Entries:** ${stats.totalEntries}\n\n`;

    // Group by category
    const byCategory = new Map<string, TeamKnowledgeEntry[]>();
    entries.forEach((e) => {
      const list = byCategory.get(e.category) ?? [];
      list.push(e);
      byCategory.set(e.category, list);
    });

    for (const [category, categoryEntries] of byCategory) {
      md += `## ${category}\n\n`;

      for (const entry of categoryEntries) {
        md += `### ${entry.title}\n\n`;
        md += `**Type:** ${entry.type}\n`;
        md += `**Contributor:** ${entry.contributor.name}\n`;
        md += `**Date:** ${new Date(entry.timestamp).toLocaleDateString()}\n\n`;
        md += `${entry.content}\n\n`;

        if (entry.relatedEntities && entry.relatedEntities.length > 0) {
          md += `**Related:** ${entry.relatedEntities.join(', ')}\n\n`;
        }

        md += '---\n\n';
      }
    }

    return md;
  }

  /**
   * Load all entries from disk
   */
  private async loadAllEntries(): Promise<TeamKnowledgeEntry[]> {
    const knowledgeDir = this.gitClient.getKnowledgeDir();
    const entries: TeamKnowledgeEntry[] = [];

    try {
      const files = await readdir(knowledgeDir);

      for (const file of files) {
        if (file.endsWith('.json') &&
            file !== 'meta.json' &&
            file !== 'categories.json') {
          try {
            const content = await readFile(join(knowledgeDir, file), 'utf-8');
            const entry = JSON.parse(content);
            entries.push(entry);
            this.cache.set(entry.id, entry);
          } catch {
            // Skip invalid files
          }
        }
      }
    } catch {
      // Directory doesn't exist
    }

    return entries;
  }

  /**
   * Update metadata file
   */
  private async updateMetadata(): Promise<void> {
    const metaPath = join(this.gitClient.getKnowledgeDir(), 'meta.json');

    let meta;
    try {
      const content = await readFile(metaPath, 'utf-8');
      meta = JSON.parse(content);
    } catch {
      meta = { version: this.config.version };
    }

    meta.lastUpdated = new Date().toISOString();
    meta.entryCount = this.cache.size;

    await writeFile(metaPath, JSON.stringify(meta, null, 2));
  }

  /**
   * Generate unique ID
   */
  private generateId(title: string): string {
    const slug = title
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, '-')
      .replace(/^-|-$/g, '')
      .slice(0, 40);
    const timestamp = Date.now().toString(36);
    return `${slug}-${timestamp}`;
  }
}

/**
 * Create a Team Knowledge instance
 */
export function createTeamKnowledge(config: TeamKnowledgeConfig): TeamKnowledge {
  return new TeamKnowledge(config);
}
