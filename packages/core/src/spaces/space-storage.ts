/**
 * Space Storage - Persistent storage for spaces
 *
 * Implements: TSK-SPACES-004, REQ-SPACES-004, DES-SPACES-003
 */

import { readFile, writeFile, mkdir, readdir, unlink } from 'node:fs/promises';
import { join } from 'node:path';
import type {
  Space,
  SpaceType,
  CreateSpaceInput,
  UpdateSpaceInput,
  SpaceStats,
} from './types.js';

/**
 * Space Storage configuration
 */
export interface SpaceStorageConfig {
  /** Storage directory path */
  storagePath: string;

  /** Max spaces to store */
  maxSpaces?: number;
}

/**
 * Space Storage class - manages persistent space storage
 */
export class SpaceStorage {
  private spacesDir: string;
  private metaPath: string;
  private activeSpaceId?: string;
  private readonly maxSpaces: number;

  constructor(config: SpaceStorageConfig) {
    this.maxSpaces = config.maxSpaces ?? 100;
    this.spacesDir = join(config.storagePath, 'spaces');
    this.metaPath = join(config.storagePath, 'spaces-meta.json');
  }

  /**
   * Initialize storage
   */
  async init(): Promise<void> {
    await mkdir(this.spacesDir, { recursive: true });

    // Load metadata
    try {
      const meta = await readFile(this.metaPath, 'utf-8');
      const data = JSON.parse(meta);
      this.activeSpaceId = data.activeSpaceId;
    } catch {
      // No metadata yet
    }
  }

  /**
   * Create a new space
   */
  async create(input: CreateSpaceInput): Promise<Space> {
    // Check max spaces limit
    const existing = await this.list();
    if (existing.length >= this.maxSpaces) {
      throw new Error(`Maximum number of spaces (${this.maxSpaces}) reached. Delete some spaces first.`);
    }

    const id = this.generateId(input.name);

    const space: Space = {
      id,
      name: input.name,
      description: input.description,
      type: input.type,
      createdAt: new Date(),
      updatedAt: new Date(),
      context: {
        includedFiles: [],
        excludedFiles: ['node_modules/**', 'dist/**', '.git/**'],
        requirements: [],
        designs: [],
        tasks: [],
        pinnedFiles: [],
        recentFiles: [],
        ...input.context,
      },
      settings: {
        autoInclude: true,
        maxContextFiles: 50,
        trackRecentFiles: true,
        recentFilesLimit: 20,
        autoCreateBranch: false,
        branchPattern: 'space/${spaceId}',
        ...input.settings,
      },
      metadata: input.metadata,
    };

    await this.save(space);
    return space;
  }

  /**
   * Get a space by ID
   */
  async get(id: string): Promise<Space | null> {
    const spacePath = join(this.spacesDir, `${id}.json`);

    try {
      const content = await readFile(spacePath, 'utf-8');
      return JSON.parse(content);
    } catch {
      return null;
    }
  }

  /**
   * Get all spaces
   */
  async list(): Promise<Space[]> {
    const spaces: Space[] = [];

    try {
      const files = await readdir(this.spacesDir);

      for (const file of files) {
        if (file.endsWith('.json')) {
          const content = await readFile(join(this.spacesDir, file), 'utf-8');
          spaces.push(JSON.parse(content));
        }
      }
    } catch {
      // Directory doesn't exist
    }

    // Sort by updatedAt (newest first)
    spaces.sort((a, b) =>
      new Date(b.updatedAt).getTime() - new Date(a.updatedAt).getTime()
    );

    return spaces;
  }

  /**
   * Update a space
   */
  async update(id: string, updates: UpdateSpaceInput): Promise<Space | null> {
    const space = await this.get(id);

    if (!space) {
      return null;
    }

    // Merge updates
    const updated: Space = {
      ...space,
      name: updates.name ?? space.name,
      description: updates.description ?? space.description,
      type: updates.type ?? space.type,
      context: {
        ...space.context,
        ...updates.context,
      },
      settings: {
        ...space.settings,
        ...updates.settings,
      },
      metadata: {
        ...space.metadata,
        ...updates.metadata,
      },
      updatedAt: new Date(),
    };

    await this.save(updated);
    return updated;
  }

  /**
   * Delete a space
   */
  async delete(id: string): Promise<boolean> {
    const spacePath = join(this.spacesDir, `${id}.json`);

    try {
      await unlink(spacePath);

      // Clear active space if deleted
      if (this.activeSpaceId === id) {
        this.activeSpaceId = undefined;
        await this.saveMetadata();
      }

      return true;
    } catch {
      return false;
    }
  }

  /**
   * Set active space
   */
  async setActive(id: string): Promise<Space | null> {
    const space = await this.get(id);

    if (!space) {
      return null;
    }

    this.activeSpaceId = id;
    await this.saveMetadata();

    // Update last accessed
    space.updatedAt = new Date();
    await this.save(space);

    return space;
  }

  /**
   * Get active space
   */
  async getActive(): Promise<Space | null> {
    if (!this.activeSpaceId) {
      return null;
    }

    return this.get(this.activeSpaceId);
  }

  /**
   * Clear active space
   */
  async clearActive(): Promise<void> {
    this.activeSpaceId = undefined;
    await this.saveMetadata();
  }

  /**
   * Get space statistics
   */
  async getStats(): Promise<SpaceStats> {
    const spaces = await this.list();

    const byType: Record<SpaceType, number> = {
      feature: 0,
      bugfix: 0,
      refactor: 0,
      documentation: 0,
      exploration: 0,
      custom: 0,
    };

    let totalFiles = 0;
    let totalRequirements = 0;

    for (const space of spaces) {
      byType[space.type]++;
      totalFiles += space.context.includedFiles.length +
                   (space.context.pinnedFiles?.length ?? 0);
      totalRequirements += space.context.requirements.length;
    }

    const recentSpaces = spaces.slice(0, 5).map((s) => ({
      id: s.id,
      name: s.name,
      lastUsed: new Date(s.updatedAt),
    }));

    return {
      totalSpaces: spaces.length,
      byType,
      activeSpaceId: this.activeSpaceId,
      recentSpaces,
      totalFiles,
      totalRequirements,
    };
  }

  /**
   * Search spaces
   */
  async search(query: string): Promise<Space[]> {
    const spaces = await this.list();
    const queryLower = query.toLowerCase();

    return spaces.filter((space) =>
      space.name.toLowerCase().includes(queryLower) ||
      space.description?.toLowerCase().includes(queryLower) ||
      space.context.requirements.some((r) => r.toLowerCase().includes(queryLower)) ||
      space.context.tasks.some((t) => t.toLowerCase().includes(queryLower))
    );
  }

  /**
   * Find spaces by type
   */
  async findByType(type: SpaceType): Promise<Space[]> {
    const spaces = await this.list();
    return spaces.filter((s) => s.type === type);
  }

  /**
   * Save a space
   */
  private async save(space: Space): Promise<void> {
    await mkdir(this.spacesDir, { recursive: true });
    const spacePath = join(this.spacesDir, `${space.id}.json`);
    await writeFile(spacePath, JSON.stringify(space, null, 2));
  }

  /**
   * Save metadata
   */
  private async saveMetadata(): Promise<void> {
    const meta = {
      activeSpaceId: this.activeSpaceId,
      lastUpdated: new Date().toISOString(),
    };
    await writeFile(this.metaPath, JSON.stringify(meta, null, 2));
  }

  /**
   * Generate unique ID
   */
  private generateId(name: string): string {
    const slug = name
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, '-')
      .replace(/^-|-$/g, '')
      .slice(0, 30);
    const timestamp = Date.now().toString(36);
    return `${slug}-${timestamp}`;
  }
}

/**
 * Create a Space Storage instance
 */
export function createSpaceStorage(config: SpaceStorageConfig): SpaceStorage {
  return new SpaceStorage(config);
}
