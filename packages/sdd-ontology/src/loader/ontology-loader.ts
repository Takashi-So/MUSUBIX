/**
 * @fileoverview Ontology loader for TTL files
 * @traceability TSK-SDD-ONTO-005, REQ-SDD-ONTO-001-F005
 */

import { readFile } from 'node:fs/promises';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import type { OntologyModule } from '../types.js';
import { coreModule } from '../modules/core.js';
import { earsModule } from '../modules/ears.js';
import { c4Module } from '../modules/c4.js';
import { traceModule } from '../modules/traceability.js';

/**
 * All available ontology modules
 */
const allModules: OntologyModule[] = [coreModule, earsModule, c4Module, traceModule];

/**
 * Ontology loader for TTL files
 */
export class OntologyLoader {
  private basePath: string;
  private loadedModules = new Map<string, string>();

  constructor(basePath?: string) {
    // Default to package's ttl directory
    this.basePath = basePath ?? join(dirname(fileURLToPath(import.meta.url)), '../../ttl');
  }

  /**
   * Load single module by ID
   */
  async loadModule(moduleId: string): Promise<string | null> {
    const module = allModules.find(m => m.id === moduleId);
    if (!module) return null;

    // Check cache
    if (this.loadedModules.has(moduleId)) {
      return this.loadedModules.get(moduleId) ?? null;
    }

    // Load dependencies first
    for (const depId of module.dependencies) {
      await this.loadModule(depId);
    }

    // Load module file
    try {
      const filePath = join(this.basePath, module.filePath.replace('ttl/', ''));
      const content = await readFile(filePath, 'utf-8');
      this.loadedModules.set(moduleId, content);
      return content;
    } catch {
      // File not found - module may be stub only
      return null;
    }
  }

  /**
   * Load all modules
   */
  async loadAll(): Promise<Map<string, string>> {
    for (const module of allModules) {
      await this.loadModule(module.id);
    }
    return new Map(this.loadedModules);
  }

  /**
   * Get module metadata
   */
  getModuleMetadata(moduleId: string): OntologyModule | undefined {
    return allModules.find(m => m.id === moduleId);
  }

  /**
   * List all available modules
   */
  listModules(): OntologyModule[] {
    return [...allModules];
  }

  /**
   * Check if module is loaded
   */
  isLoaded(moduleId: string): boolean {
    return this.loadedModules.has(moduleId);
  }

  /**
   * Get loaded module count
   */
  get loadedCount(): number {
    return this.loadedModules.size;
  }
}
