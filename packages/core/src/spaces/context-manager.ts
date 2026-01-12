/**
 * Context Manager - Central manager for space contexts
 *
 * Implements: TSK-SPACES-003, REQ-SPACES-003, DES-SPACES-004
 */

import type {
  Space,
  SpaceActivationResult,
  CreateSpaceInput,
  UpdateSpaceInput,
  ContextQuery,
  ContextSuggestion,
  SpaceStats,
} from './types.js';
import { SpaceContext_, createSpaceContext } from './space-context.js';
import { SpaceStorage, createSpaceStorage } from './space-storage.js';

/**
 * Context Manager configuration
 */
export interface ContextManagerConfig {
  /** Workspace root path */
  workspacePath: string;

  /** Storage path for spaces */
  storagePath: string;

  /** Auto-activate last space on init */
  autoActivate?: boolean;

  /** Callback when space is activated */
  onActivate?: (space: Space) => Promise<void>;

  /** Callback when space is deactivated */
  onDeactivate?: (space: Space) => Promise<void>;
}

/**
 * Context Manager - manages all spaces and their contexts
 */
export class ContextManager {
  private config: ContextManagerConfig;
  private storage: SpaceStorage;
  private spaceContext: SpaceContext_;
  private activeSpace?: Space;

  constructor(config: ContextManagerConfig) {
    this.config = config;
    this.storage = createSpaceStorage({ storagePath: config.storagePath });
    this.spaceContext = createSpaceContext({ workspacePath: config.workspacePath });
  }

  /**
   * Initialize the context manager
   */
  async init(): Promise<void> {
    await this.storage.init();

    // Auto-activate last space if enabled
    if (this.config.autoActivate) {
      const active = await this.storage.getActive();
      if (active) {
        await this.activate(active.id);
      }
    }
  }

  /**
   * Create a new space
   */
  async createSpace(input: CreateSpaceInput): Promise<Space> {
    return this.storage.create(input);
  }

  /**
   * Get a space by ID
   */
  async getSpace(id: string): Promise<Space | null> {
    return this.storage.get(id);
  }

  /**
   * List all spaces
   */
  async listSpaces(): Promise<Space[]> {
    return this.storage.list();
  }

  /**
   * Update a space
   */
  async updateSpace(id: string, updates: UpdateSpaceInput): Promise<Space | null> {
    const updated = await this.storage.update(id, updates);

    // Update active space if it's the one being updated
    if (updated && this.activeSpace?.id === id) {
      this.activeSpace = updated;
    }

    return updated;
  }

  /**
   * Delete a space
   */
  async deleteSpace(id: string): Promise<boolean> {
    // Deactivate if active
    if (this.activeSpace?.id === id) {
      await this.deactivate();
    }

    return this.storage.delete(id);
  }

  /**
   * Activate a space
   */
  async activate(id: string): Promise<SpaceActivationResult> {
    // Deactivate current space first
    if (this.activeSpace) {
      await this.deactivate();
    }

    const space = await this.storage.setActive(id);

    if (!space) {
      return {
        success: false,
        error: `Space ${id} not found`,
      };
    }

    this.activeSpace = space;

    // Get context files
    const loadedFiles = await this.spaceContext.getContextFiles(space);

    // Call activation callback
    if (this.config.onActivate) {
      await this.config.onActivate(space);
    }

    return {
      success: true,
      space,
      loadedFiles,
      branch: space.context.branch,
    };
  }

  /**
   * Deactivate current space
   */
  async deactivate(): Promise<void> {
    if (!this.activeSpace) {
      return;
    }

    // Save recent files before deactivating
    const recentFiles = this.spaceContext.getRecentFiles();
    await this.storage.update(this.activeSpace.id, {
      context: {
        recentFiles,
      },
    });

    // Call deactivation callback
    if (this.config.onDeactivate) {
      await this.config.onDeactivate(this.activeSpace);
    }

    this.activeSpace = undefined;
    await this.storage.clearActive();
  }

  /**
   * Get active space
   */
  getActiveSpace(): Space | undefined {
    return this.activeSpace;
  }

  /**
   * Get context files for active space
   */
  async getContextFiles(): Promise<string[]> {
    if (!this.activeSpace) {
      return [];
    }

    return this.spaceContext.getContextFiles(this.activeSpace);
  }

  /**
   * Suggest files for context
   */
  async suggestFiles(query: ContextQuery): Promise<ContextSuggestion[]> {
    return this.spaceContext.suggestFiles(query);
  }

  /**
   * Add file to active space context
   */
  async addFileToContext(filePath: string): Promise<boolean> {
    if (!this.activeSpace) {
      return false;
    }

    // Add to included files
    if (!this.activeSpace.context.includedFiles.includes(filePath)) {
      this.activeSpace.context.includedFiles.push(filePath);
      await this.storage.update(this.activeSpace.id, {
        context: {
          includedFiles: this.activeSpace.context.includedFiles,
        },
      });
    }

    // Track access
    this.spaceContext.trackFileAccess(filePath);

    return true;
  }

  /**
   * Pin file in active space
   */
  async pinFile(filePath: string): Promise<boolean> {
    if (!this.activeSpace) {
      return false;
    }

    const pinnedFiles = this.activeSpace.context.pinnedFiles ?? [];
    if (!pinnedFiles.includes(filePath)) {
      pinnedFiles.push(filePath);
      await this.storage.update(this.activeSpace.id, {
        context: {
          pinnedFiles,
        },
      });
      this.activeSpace.context.pinnedFiles = pinnedFiles;
    }

    return true;
  }

  /**
   * Unpin file from active space
   */
  async unpinFile(filePath: string): Promise<boolean> {
    if (!this.activeSpace) {
      return false;
    }

    const pinnedFiles = this.activeSpace.context.pinnedFiles ?? [];
    const index = pinnedFiles.indexOf(filePath);

    if (index !== -1) {
      pinnedFiles.splice(index, 1);
      await this.storage.update(this.activeSpace.id, {
        context: {
          pinnedFiles,
        },
      });
      this.activeSpace.context.pinnedFiles = pinnedFiles;
    }

    return true;
  }

  /**
   * Link requirement to active space
   */
  async linkRequirement(reqId: string): Promise<boolean> {
    if (!this.activeSpace) {
      return false;
    }

    if (!this.activeSpace.context.requirements.includes(reqId)) {
      this.activeSpace.context.requirements.push(reqId);
      await this.storage.update(this.activeSpace.id, {
        context: {
          requirements: this.activeSpace.context.requirements,
        },
      });
    }

    return true;
  }

  /**
   * Link design to active space
   */
  async linkDesign(desId: string): Promise<boolean> {
    if (!this.activeSpace) {
      return false;
    }

    if (!this.activeSpace.context.designs.includes(desId)) {
      this.activeSpace.context.designs.push(desId);
      await this.storage.update(this.activeSpace.id, {
        context: {
          designs: this.activeSpace.context.designs,
        },
      });
    }

    return true;
  }

  /**
   * Link task to active space
   */
  async linkTask(taskId: string): Promise<boolean> {
    if (!this.activeSpace) {
      return false;
    }

    if (!this.activeSpace.context.tasks.includes(taskId)) {
      this.activeSpace.context.tasks.push(taskId);
      await this.storage.update(this.activeSpace.id, {
        context: {
          tasks: this.activeSpace.context.tasks,
        },
      });
    }

    return true;
  }

  /**
   * Set custom instructions for active space
   */
  async setInstructions(instructions: string): Promise<boolean> {
    if (!this.activeSpace) {
      return false;
    }

    await this.storage.update(this.activeSpace.id, {
      context: {
        instructions,
      },
    });
    this.activeSpace.context.instructions = instructions;

    return true;
  }

  /**
   * Get space statistics
   */
  async getStats(): Promise<SpaceStats> {
    return this.storage.getStats();
  }

  /**
   * Search spaces
   */
  async searchSpaces(query: string): Promise<Space[]> {
    return this.storage.search(query);
  }

  /**
   * Find related files for a file
   */
  async findRelatedFiles(filePath: string): Promise<string[]> {
    return this.spaceContext.findRelatedFiles(filePath);
  }

  /**
   * Export space to markdown
   */
  async exportSpaceToMarkdown(id: string): Promise<string> {
    const space = await this.storage.get(id);

    if (!space) {
      return '# Space not found';
    }

    let md = `# Space: ${space.name}\n\n`;
    md += `**Type:** ${space.type}\n`;
    md += `**Created:** ${new Date(space.createdAt).toLocaleDateString('ja-JP')}\n`;
    md += `**Updated:** ${new Date(space.updatedAt).toLocaleDateString('ja-JP')}\n\n`;

    if (space.description) {
      md += `## Description\n\n${space.description}\n\n`;
    }

    if (space.context.instructions) {
      md += `## Instructions\n\n${space.context.instructions}\n\n`;
    }

    if (space.context.requirements.length > 0) {
      md += `## Requirements\n\n`;
      for (const req of space.context.requirements) {
        md += `- ${req}\n`;
      }
      md += '\n';
    }

    if (space.context.designs.length > 0) {
      md += `## Designs\n\n`;
      for (const des of space.context.designs) {
        md += `- ${des}\n`;
      }
      md += '\n';
    }

    if (space.context.tasks.length > 0) {
      md += `## Tasks\n\n`;
      for (const task of space.context.tasks) {
        md += `- ${task}\n`;
      }
      md += '\n';
    }

    if (space.context.includedFiles.length > 0) {
      md += `## Included Files\n\n`;
      for (const file of space.context.includedFiles) {
        md += `- ${file}\n`;
      }
      md += '\n';
    }

    if (space.context.pinnedFiles && space.context.pinnedFiles.length > 0) {
      md += `## Pinned Files\n\n`;
      for (const file of space.context.pinnedFiles) {
        md += `- 📌 ${file}\n`;
      }
      md += '\n';
    }

    return md;
  }
}

/**
 * Create a Context Manager instance
 */
export function createContextManager(config: ContextManagerConfig): ContextManager {
  return new ContextManager(config);
}
