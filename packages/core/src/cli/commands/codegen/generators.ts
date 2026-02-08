/**
 * Code Generators
 *
 * Entity, Service, Repository, Controller, and C4 component code generators
 *
 * @packageDocumentation
 * @module cli/commands/codegen/generators
 *
 * @see REQ-CG-001 - Code Generation
 * @see REQ-BUGFIX-003-01 - 4 file generation
 */

import { ComponentInference } from '../../../design/component-inference.js';
import { toPascalCase, toSnakeCase, toKebabCase } from '../../../utils/string-casing.js';
import type {
  CodegenOptions,
  GeneratedCode,
  GeneratedSkeleton,
  FullSkeletonOptions,
  ExtendedGenerateOptions,
  C4Component,
  DesignPattern,
} from './types.js';
import {
  parseC4DesignComponents,
  extractDesignPatterns,
  extractEarsRequirements,
  generateMethodStubsForComponent,
  generateMethodImplementation,
  generateInterfaceMethods,
} from './template-utils.js';

/**
 * Infer components from EARS requirements
 */
function inferComponentsFromRequirements(
  requirements: Array<{ id: string; pattern: string; priority: string; description: string }>
): Array<{ name: string; type: 'service' | 'repository' | 'controller' | 'model'; requirements: string[] }> {
  const components: Map<string, { name: string; type: 'service' | 'repository' | 'controller' | 'model'; requirements: string[] }> = new Map();

  for (const req of requirements) {
    const desc = req.description.toLowerCase();

    // Infer component types from requirement patterns
    if (desc.includes('persist') || desc.includes('store') || desc.includes('save') || desc.includes('storage')) {
      const name = 'DataRepository';
      if (!components.has(name)) {
        components.set(name, { name, type: 'repository', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }

    if (desc.includes('create') || desc.includes('update') || desc.includes('delete') || desc.includes('manage')) {
      // Extract entity name
      const entityMatch = desc.match(/(?:create|update|delete|manage)\s+(\w+)/i);
      const entityName = entityMatch ? toPascalCase(entityMatch[1]) : 'Entity';
      const serviceName = `${entityName}Service`;
      if (!components.has(serviceName)) {
        components.set(serviceName, { name: serviceName, type: 'service', requirements: [] });
      }
      components.get(serviceName)!.requirements.push(req.id);
    }

    // Shopping/E-commerce specific components
    if (desc.includes('cart') || desc.includes('\u30AB\u30FC\u30C8')) {
      const name = 'CartService';
      if (!components.has(name)) {
        components.set(name, { name, type: 'service', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }

    if (desc.includes('product') || desc.includes('catalog') || desc.includes('\u5546\u54C1')) {
      const name = 'ProductCatalogService';
      if (!components.has(name)) {
        components.set(name, { name, type: 'service', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }

    if (desc.includes('checkout') || desc.includes('\u8CFC\u5165') || desc.includes('\u6C7A\u6E08')) {
      const name = 'CheckoutService';
      if (!components.has(name)) {
        components.set(name, { name, type: 'service', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }

    if (desc.includes('price') || desc.includes('total') || desc.includes('tax') || desc.includes('\u4FA1\u683C') || desc.includes('\u8A08\u7B97')) {
      const name = 'PricingService';
      if (!components.has(name)) {
        components.set(name, { name, type: 'service', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }

    if (desc.includes('stock') || desc.includes('inventory') || desc.includes('\u5728\u5EAB')) {
      const name = 'InventoryService';
      if (!components.has(name)) {
        components.set(name, { name, type: 'service', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }

    if (desc.includes('coupon') || desc.includes('discount') || desc.includes('\u5272\u5F15')) {
      const name = 'DiscountService';
      if (!components.has(name)) {
        components.set(name, { name, type: 'service', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }

    if (desc.includes('notification') || desc.includes('notify') || desc.includes('alert')) {
      const name = 'NotificationService';
      if (!components.has(name)) {
        components.set(name, { name, type: 'service', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }

    if (desc.includes('user') || desc.includes('confirmation') || desc.includes('display')) {
      const name = 'UserInterface';
      if (!components.has(name)) {
        components.set(name, { name, type: 'controller', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }

    if (desc.includes('task') || desc.includes('item') || desc.includes('data') || desc.includes('entity')) {
      const entityMatch = desc.match(/\b(task|item|user|product|order)\b/i);
      const entityName = entityMatch ? toPascalCase(entityMatch[1]) : 'Entity';
      const modelName = `${entityName}Model`;
      if (!components.has(modelName)) {
        components.set(modelName, { name: modelName, type: 'model', requirements: [] });
      }
      components.get(modelName)!.requirements.push(req.id);
    }
  }

  // If no components were inferred, create a default service
  if (components.size === 0 && requirements.length > 0) {
    components.set('MainService', {
      name: 'MainService',
      type: 'service',
      requirements: requirements.map(r => r.id),
    });
  }

  return Array.from(components.values());
}

/**
 * Generate code from design
 * Enhanced in v1.1.2: Domain-aware code generation using ComponentInference
 * Enhanced in v3.3.10: Full skeleton generation (4 files per component)
 * @see TSK-BUGFIX-003 - codegen full implementation
 */
export function generateCodeFromDesign(
  content: string,
  options: CodegenOptions,
  extendedOptions?: ExtendedGenerateOptions
): GeneratedCode[] {
  const files: GeneratedCode[] = [];
  const language = options.language ?? 'typescript';
  const { fullSkeleton = false, withTests = false } = extendedOptions ?? {};

  // Detect domain from content for domain-specific method generation
  const componentInference = new ComponentInference();
  const domainKeywords = content.toLowerCase();
  const detectedDomain = componentInference.detectDomain(domainKeywords);
  const ext = language === 'typescript' ? '.ts' : language === 'javascript' ? '.js' : '.py';

  // Check if this is an EARS requirements document
  const isEarsDoc = content.includes('EARS') || content.includes('SHALL') || content.includes('REQ-');

  // Check if this is a C4 design document (table-based)
  const isC4Design = content.includes('C4 Component') ||
                     content.includes('### Elements') ||
                     content.includes('### \u30B3\u30F3\u30DD\u30FC\u30CD\u30F3\u30C8\u4E00\u89A7') ||
                     content.includes('Component Diagram') ||
                     (content.includes('| ID |') && content.includes('| Type |'));

  if (isC4Design) {
    // Parse C4 design document table format
    const c4Components = parseC4DesignComponents(content);
    const reqMatches = content.match(/REQ-[A-Z]+-\d+/g) || [];
    const patterns = extractDesignPatterns(content);

    for (const component of c4Components) {
      if (component.type === 'person') continue; // Skip user/person elements

      // Full skeleton mode: generate 4 files per component
      if (fullSkeleton) {
        const skeleton = generateFullSkeleton(component.name, {
          language: language as 'typescript' | 'javascript' | 'python',
          patterns: patterns.map(p => p.name),
          requirements: reqMatches.slice(0, 5),
          designId: component.id,
          includeTest: true,
        });
        files.push(skeleton.interface, skeleton.implementation, skeleton.test, skeleton.index);
        continue;
      }

      const code = generateC4ComponentCode(component, language, reqMatches, patterns, detectedDomain);
      // Normalize name: BLOG_PLATFORM -> BlogPlatform -> blog-platform
      const normalizedName = toKebabCase(toPascalCase(component.name));

      files.push({
        filename: `${normalizedName}${ext}`,
        language,
        content: code,
        metadata: {
          requirements: reqMatches.slice(0, 5),
          designElements: [component.id],
          patterns: patterns.map(p => p.name),
        },
      });

      // Generate test file if --with-tests is specified
      if (withTests) {
        const testCode = generateTestForComponent(normalizedName, language);
        files.push({
          filename: `${normalizedName}.test${ext}`,
          language,
          content: testCode,
          metadata: {
            requirements: [],
            designElements: [],
            patterns: [],
          },
        });
      }
    }
  } else if (isEarsDoc) {
    // Extract and process EARS requirements
    const requirements = extractEarsRequirements(content);
    const components = inferComponentsFromRequirements(requirements);

    for (const component of components) {
      const code = generateComponentCodeFromRequirements(component, language, requirements);
      files.push({
        filename: `${toKebabCase(component.name)}${ext}`,
        language,
        content: code,
        metadata: {
          requirements: component.requirements,
          designElements: [],
          patterns: component.type === 'repository' ? ['Repository'] : component.type === 'service' ? ['Service'] : [],
        },
      });
    }
  } else {
    // Original logic for design documents
    const componentMatches = content.match(/component\s+["']?([A-Za-z0-9_-]+)["']?/gi) || [];
    const classMatches = content.match(/class\s+["']?([A-Za-z0-9_-]+)["']?/gi) || [];
    const interfaceMatches = content.match(/interface\s+["']?([A-Za-z0-9_-]+)["']?/gi) || [];

    const reqMatches = content.match(/REQ-[A-Z]+-\d+/g) || [];
    const desMatches = content.match(/DES-[A-Z]+-\d+/g) || [];

    const seen = new Set<string>();
    const allMatches = [...componentMatches, ...classMatches, ...interfaceMatches];

    for (const match of allMatches) {
      const name = match.split(/\s+/).pop()?.replace(/["']/g, '') || 'Unknown';
      if (seen.has(name)) continue;
      seen.add(name);

      const code = generateComponentCode(name, language);
      files.push({
        filename: `${toKebabCase(name)}${ext}`,
        language,
        content: code,
        metadata: {
          requirements: reqMatches.slice(0, 5),
          designElements: desMatches.slice(0, 5),
          patterns: [],
        },
      });
    }
  }

  // Generate index file
  if (files.length > 0) {
    const indexContent = files
      .map(f => {
        const baseName = f.filename.replace(ext, '');
        return `export * from './${baseName}';`;
      })
      .join('\n');

    files.push({
      filename: `index${ext}`,
      language,
      content: `/**\n * Generated index file\n * @generated\n */\n\n${indexContent}\n`,
      metadata: {
        requirements: [],
        designElements: [],
        patterns: [],
      },
    });
  }

  return files;
}

/**
 * Generate component code from EARS requirements
 */
function generateComponentCodeFromRequirements(
  component: { name: string; type: 'service' | 'repository' | 'controller' | 'model'; requirements: string[] },
  language: string,
  allRequirements: Array<{ id: string; pattern: string; priority: string; description: string }>
): string {
  const className = component.name;
  const relatedReqs = allRequirements.filter(r => component.requirements.includes(r.id));
  const reqComments = relatedReqs.map(r => ` * @see ${r.id} - ${r.description.substring(0, 60)}...`).join('\n');

  if (language === 'typescript') {
    if (component.type === 'model') {
      return `/**
 * ${className}
 *
 * @generated by MUSUBIX from EARS requirements
 * @module ${toKebabCase(className)}
 *
${reqComments}
 */

/**
 * ${className} interface
 */
export interface I${className} {
  id: string;
  createdAt: Date;
  updatedAt: Date;
}

/**
 * ${className} implementation
 */
export class ${className} implements I${className} {
  id: string;
  createdAt: Date;
  updatedAt: Date;

  constructor(data?: Partial<I${className}>) {
    this.id = data?.id ?? crypto.randomUUID();
    this.createdAt = data?.createdAt ?? new Date();
    this.updatedAt = data?.updatedAt ?? new Date();
  }

  /**
   * Update the model
   */
  update(data: Partial<I${className}>): void {
    Object.assign(this, data);
    this.updatedAt = new Date();
  }

  /**
   * Convert to plain object
   */
  toJSON(): I${className} {
    return {
      id: this.id,
      createdAt: this.createdAt,
      updatedAt: this.updatedAt,
    };
  }
}
`;
    }

    if (component.type === 'repository') {
      return `/**
 * ${className}
 *
 * @generated by MUSUBIX from EARS requirements
 * @module ${toKebabCase(className)}
 *
${reqComments}
 */

/**
 * ${className} interface
 */
export interface I${className}<T> {
  findAll(): Promise<T[]>;
  findById(id: string): Promise<T | null>;
  save(entity: T): Promise<T>;
  delete(id: string): Promise<boolean>;
}

/**
 * ${className} implementation
 * @implements REQ: persist, store, save, storage
 */
export class ${className}<T extends { id: string }> implements I${className}<T> {
  private storage: Map<string, T> = new Map();

  async findAll(): Promise<T[]> {
    return Array.from(this.storage.values());
  }

  async findById(id: string): Promise<T | null> {
    return this.storage.get(id) ?? null;
  }

  async save(entity: T): Promise<T> {
    this.storage.set(entity.id, entity);
    return entity;
  }

  async delete(id: string): Promise<boolean> {
    return this.storage.delete(id);
  }

  /**
   * Clear all data
   */
  async clear(): Promise<void> {
    this.storage.clear();
  }
}

/**
 * Create a singleton repository instance
 */
let instance: ${className}<unknown> | null = null;
export function get${className}<T extends { id: string }>(): ${className}<T> {
  if (!instance) {
    instance = new ${className}<T>();
  }
  return instance as ${className}<T>;
}
`;
    }

    if (component.type === 'controller') {
      return `/**
 * ${className}
 *
 * @generated by MUSUBIX from EARS requirements
 * @module ${toKebabCase(className)}
 *
${reqComments}
 */

/**
 * ${className} interface
 */
export interface I${className} {
  display(message: string): void;
  confirm(message: string): Promise<boolean>;
  notify(title: string, body: string): void;
}

/**
 * ${className} implementation
 * @implements REQ: user, confirmation, display
 */
export class ${className} implements I${className} {
  /**
   * Display a message to the user
   */
  display(message: string): void {
    console.log(message);
  }

  /**
   * Request user confirmation
   * @implements Article VI - SHALL NOT allow without confirmation
   */
  async confirm(message: string): Promise<boolean> {
    // In a real implementation, this would show a dialog
    console.log(\`Confirmation required: \${message}\`);
    return true;
  }

  /**
   * Show a notification
   * @implements REQ: notification, notify, alert
   */
  notify(title: string, body: string): void {
    console.log(\`[Notification] \${title}: \${body}\`);
  }
}

/**
 * Create ${className} instance
 */
export function create${className}(): ${className} {
  return new ${className}();
}
`;
    }

    // Default: Service
    return `/**
 * ${className}
 *
 * @generated by MUSUBIX from EARS requirements
 * @module ${toKebabCase(className)}
 *
${reqComments}
 */

/**
 * ${className} interface
 */
export interface I${className} {
  initialize(): Promise<void>;
  execute(): Promise<void>;
  dispose(): Promise<void>;
}

/**
 * ${className} implementation
 */
export class ${className} implements I${className} {
  private initialized = false;

  constructor() {
    // Initialize
  }

  async initialize(): Promise<void> {
    if (this.initialized) return;
    // TODO: Add initialization logic
    this.initialized = true;
  }

  async execute(): Promise<void> {
    if (!this.initialized) {
      await this.initialize();
    }
    // TODO: Add execution logic
  }

  async dispose(): Promise<void> {
    // TODO: Add cleanup logic
    this.initialized = false;
  }
}

/**
 * Create ${className} instance
 */
export function create${className}(): ${className} {
  return new ${className}();
}
`;
  }

  // JavaScript default
  return generateComponentCode(className, language);
}

/**
 * Generate component code
 */
function generateComponentCode(name: string, language: string): string {
  const className = toPascalCase(name);

  if (language === 'typescript') {
    return `/**
 * ${className}
 *
 * @generated
 * @module ${toKebabCase(name)}
 */

/**
 * ${className} interface
 */
export interface I${className} {
  /**
   * Initialize the component
   */
  initialize(): Promise<void>;

  /**
   * Execute main logic
   */
  execute(): Promise<void>;

  /**
   * Cleanup resources
   */
  dispose(): Promise<void>;
}

/**
 * ${className} implementation
 */
export class ${className} implements I${className} {
  private initialized = false;

  /**
   * Create a new ${className} instance
   */
  constructor() {
    // Initialize
  }

  /**
   * Initialize the component
   */
  async initialize(): Promise<void> {
    if (this.initialized) return;
    // TODO: Add initialization logic
    this.initialized = true;
  }

  /**
   * Execute main logic
   */
  async execute(): Promise<void> {
    if (!this.initialized) {
      await this.initialize();
    }
    // TODO: Add execution logic
  }

  /**
   * Cleanup resources
   */
  async dispose(): Promise<void> {
    // TODO: Add cleanup logic
    this.initialized = false;
  }
}

/**
 * Create a new ${className} instance
 */
export function create${className}(): ${className} {
  return new ${className}();
}
`;
  } else if (language === 'python') {
    return `"""
${className}

Generated module
"""

from abc import ABC, abstractmethod
from typing import Optional


class I${className}(ABC):
    """${className} interface."""

    @abstractmethod
    async def initialize(self) -> None:
        """Initialize the component."""
        pass

    @abstractmethod
    async def execute(self) -> None:
        """Execute main logic."""
        pass

    @abstractmethod
    async def dispose(self) -> None:
        """Cleanup resources."""
        pass


class ${className}(I${className}):
    """${className} implementation."""

    def __init__(self) -> None:
        """Create a new ${className} instance."""
        self._initialized = False

    async def initialize(self) -> None:
        """Initialize the component."""
        if self._initialized:
            return
        # TODO: Add initialization logic
        self._initialized = True

    async def execute(self) -> None:
        """Execute main logic."""
        if not self._initialized:
            await self.initialize()
        # TODO: Add execution logic

    async def dispose(self) -> None:
        """Cleanup resources."""
        # TODO: Add cleanup logic
        self._initialized = False


def create_${toSnakeCase(name)}() -> ${className}:
    """Create a new ${className} instance."""
    return ${className}()
`;
  }

  // JavaScript
  return `/**
 * ${className}
 *
 * @generated
 * @module ${toKebabCase(name)}
 */

/**
 * ${className} implementation
 */
export class ${className} {
  #initialized = false;

  /**
   * Create a new ${className} instance
   */
  constructor() {
    // Initialize
  }

  /**
   * Initialize the component
   */
  async initialize() {
    if (this.#initialized) return;
    // TODO: Add initialization logic
    this.#initialized = true;
  }

  /**
   * Execute main logic
   */
  async execute() {
    if (!this.#initialized) {
      await this.initialize();
    }
    // TODO: Add execution logic
  }

  /**
   * Dispose resources
   */
  async dispose() {
    // TODO: Add cleanup logic
    this.#initialized = false;
  }
}

/**
 * Create a new ${className} instance
 */
export function create${className}() {
  return new ${className}();
}
`;
}

/**
 * Generate full skeleton with 4 files (interface, implementation, test, index)
 * @see REQ-BUGFIX-003-01 - 4 file generation
 * @see TSK-BUGFIX-003-02 - SkeletonGenerator extension
 */
export function generateFullSkeleton(
  componentName: string,
  options: FullSkeletonOptions
): GeneratedSkeleton {
  const baseName = toKebabCase(componentName);
  const className = toPascalCase(componentName);
  const ext = options.language === 'typescript' ? '.ts' : options.language === 'javascript' ? '.js' : '.py';
  const reqComments = options.requirements.map(r => ` * @see ${r}`).join('\n');
  const patternComments = options.patterns.map(p => ` * @pattern ${p}`).join('\n');
  const traceComment = options.designId ? ` * @trace ${options.designId}` : '';

  // Interface file
  const interfaceContent = `/**
 * ${className} Interface
 *
${reqComments}
${patternComments}
${traceComment}
 * @generated
 */

export interface I${className} {
  /**
   * Get the identifier
   */
  getId(): string;

  /**
   * Execute the main operation
   */
  execute(): Promise<void>;
}

export interface ${className}Config {
  readonly id: string;
  readonly options?: Record<string, unknown>;
}
`;

  // Implementation file
  const implementationContent = `/**
 * ${className} Implementation
 *
${reqComments}
${patternComments}
${traceComment}
 * @generated
 */

import type { I${className}, ${className}Config } from './${baseName}.interface${ext === '.ts' ? '' : ext}';

export class ${className} implements I${className} {
  private readonly config: ${className}Config;

  constructor(config: ${className}Config) {
    this.config = config;
  }

  getId(): string {
    return this.config.id;
  }

  async execute(): Promise<void> {
    // TODO: Implement ${className} logic
    throw new Error('Not implemented');
  }
}

export function create${className}(config: ${className}Config): I${className} {
  return new ${className}(config);
}
`;

  // Test file
  const testContent = `/**
 * ${className} Tests
 *
${reqComments}
 * @generated
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { ${className}, create${className} } from './${baseName}${ext === '.ts' ? '' : ext}';
import type { ${className}Config } from './${baseName}.interface${ext === '.ts' ? '' : ext}';

describe('${className}', () => {
  let instance: ${className};
  const testConfig: ${className}Config = {
    id: 'test-${baseName}-001',
  };

  beforeEach(() => {
    instance = new ${className}(testConfig);
  });

  describe('getId', () => {
    it('should return the configured id', () => {
      expect(instance.getId()).toBe(testConfig.id);
    });
  });

  describe('execute', () => {
    it('should be implemented', async () => {
      // TODO: Update test when implementation is complete
      await expect(instance.execute()).rejects.toThrow('Not implemented');
    });
  });

  describe('create${className}', () => {
    it('should create an instance via factory', () => {
      const created = create${className}(testConfig);
      expect(created.getId()).toBe(testConfig.id);
    });
  });
});
`;

  // Index file
  const indexContent = `/**
 * ${className} Module
 * @generated
 */

export type { I${className}, ${className}Config } from './${baseName}.interface${ext === '.ts' ? '' : ext}';
export { ${className}, create${className} } from './${baseName}${ext === '.ts' ? '' : ext}';
`;

  return {
    interface: {
      filename: `${baseName}.interface${ext}`,
      language: options.language,
      content: interfaceContent,
      metadata: {
        requirements: options.requirements,
        designElements: options.designId ? [options.designId] : [],
        patterns: options.patterns,
      },
    },
    implementation: {
      filename: `${baseName}${ext}`,
      language: options.language,
      content: implementationContent,
      metadata: {
        requirements: options.requirements,
        designElements: options.designId ? [options.designId] : [],
        patterns: options.patterns,
      },
    },
    test: {
      filename: `${baseName}.test${ext}`,
      language: options.language,
      content: testContent,
      metadata: {
        requirements: options.requirements,
        designElements: [],
        patterns: [],
      },
    },
    index: {
      filename: `index${ext}`,
      language: options.language,
      content: indexContent,
      metadata: {
        requirements: [],
        designElements: [],
        patterns: [],
      },
    },
  };
}

/**
 * Generate test file for a component
 * @see TSK-BUGFIX-006 - test generation integration
 */
function generateTestForComponent(componentName: string, _language: string): string {
  const className = toPascalCase(componentName);
  const baseName = toKebabCase(componentName);

  return `/**
 * ${className} Tests
 * @generated
 */

import { describe, it, expect } from 'vitest';
import { ${className} } from './${baseName}';

describe('${className}', () => {
  it('should be defined', () => {
    expect(${className}).toBeDefined();
  });

  // TODO: Add more test cases based on the component's functionality
});
`;
}

/**
 * Generate TypeScript code for C4 component
 * Enhanced in v1.1.2: Accepts domainId for domain-specific method generation
 */
function generateC4ComponentCode(
  component: C4Component,
  language: string,
  requirements: string[],
  patterns: DesignPattern[],
  domainId?: string
): string {
  const { id, name, type, description, pattern } = component;
  // Normalize name to PascalCase (handles UPPER_CASE, snake_case, kebab-case, etc.)
  const className = toPascalCase(name);
  const patternComments = patterns.map(p => ` * @pattern ${p.name} - ${p.intent}`).join('\n');
  const reqComments = requirements.slice(0, 3).map(r => ` * @see ${r}`).join('\n');
  const lowerType = type.toLowerCase();

  if (language === 'typescript') {
    const interfaceName = `I${className}`;

    // Entity-specific template with proper structure
    if (lowerType === 'entity' || pattern?.toLowerCase() === 'entity') {
      return generateEntityTemplate(className, interfaceName, id, description, patternComments, reqComments);
    }

    // Repository-specific template with generics
    if (lowerType === 'repository' || pattern?.toLowerCase() === 'repository') {
      return generateRepositoryTemplate(className, interfaceName, id, description, patternComments, reqComments);
    }

    // Service-specific template with proper types and domain-specific methods
    if (lowerType === 'service' && (pattern?.toLowerCase() === 'service' || description.includes('\u30D3\u30B8\u30CD\u30B9\u30ED\u30B8\u30C3\u30AF') || description.includes('CRUD'))) {
      return generateServiceTemplate(className, interfaceName, id, description, patternComments, reqComments, domainId);
    }

    // Default: Use method stubs
    // Pass both name and description for better domain context matching
    const methodStubs = generateMethodStubsForComponent(pattern || type, `${name.toLowerCase()} ${description}`);

    return `/**
 * ${className}
 * ${description}
 *
 * @generated by MUSUBIX from C4 design
 * @module ${toKebabCase(className)}
 * @designElement ${id}
 *
${patternComments}
${reqComments}
 */

/**
 * ${className} interface
 */
export interface ${interfaceName} {
${methodStubs.map(m => `  ${m.name}(${m.params}): ${m.returnType};`).join('\n')}
}

/**
 * ${className} implementation
 */
export class ${className} implements ${interfaceName} {
  constructor() {
    // Initialize ${className}
  }

${methodStubs.map(m => `  /**
   * ${m.description}
   */
  ${m.async ? 'async ' : ''}${m.name}(${m.params}): ${m.returnType} {
    // TODO: Implement ${m.name}
    throw new Error('Not implemented');
  }`).join('\n\n')}
}

/**
 * Factory function
 */
export function create${className}(): ${interfaceName} {
  return new ${className}();
}
`;
  }

  // JavaScript/Python fallback
  return `/**
 * ${className}
 * ${description}
 *
 * @generated by MUSUBIX from C4 design
 */

export class ${className} {
  constructor() {
    // Initialize ${className}
  }
}
`;
}

/**
 * Generate Entity template with proper structure
 */
function generateEntityTemplate(
  className: string,
  interfaceName: string,
  id: string,
  description: string,
  patternComments: string,
  reqComments: string
): string {
  return `/**
 * ${className}
 * ${description}
 *
 * @generated by MUSUBIX from C4 design
 * @module ${toKebabCase(className)}
 * @designElement ${id}
 *
${patternComments}
${reqComments}
 */

/**
 * ${className} data transfer object
 */
export interface ${className}DTO {
  id?: string;
  name?: string;
  description?: string;
  createdAt?: Date;
  updatedAt?: Date;
  [key: string]: unknown;
}

/**
 * ${className} interface
 */
export interface ${interfaceName} {
  readonly id: string;
  readonly createdAt: Date;
  updatedAt: Date;

  update(data: Partial<${className}DTO>): void;
  validate(): boolean;
  toJSON(): ${className}DTO;
}

/**
 * ${className} implementation
 */
export class ${className} implements ${interfaceName} {
  readonly id: string;
  readonly createdAt: Date;
  updatedAt: Date;

  private data: ${className}DTO;

  constructor(data?: Partial<${className}DTO>) {
    this.id = data?.id ?? crypto.randomUUID();
    this.createdAt = data?.createdAt ?? new Date();
    this.updatedAt = data?.updatedAt ?? new Date();
    this.data = { ...data };
  }

  /**
   * Update entity with partial data
   */
  update(data: Partial<${className}DTO>): void {
    Object.assign(this.data, data);
    this.updatedAt = new Date();
  }

  /**
   * Validate entity state
   */
  validate(): boolean {
    // TODO: Implement validation logic
    return this.id !== undefined && this.id.length > 0;
  }

  /**
   * Convert to plain object
   */
  toJSON(): ${className}DTO {
    return {
      id: this.id,
      createdAt: this.createdAt,
      updatedAt: this.updatedAt,
      ...this.data,
    };
  }
}

/**
 * Factory function
 */
export function create${className}(data?: Partial<${className}DTO>): ${interfaceName} {
  return new ${className}(data);
}
`;
}

/**
 * Generate Repository template with generics
 */
function generateRepositoryTemplate(
  className: string,
  interfaceName: string,
  id: string,
  description: string,
  patternComments: string,
  reqComments: string
): string {
  return `/**
 * ${className}
 * ${description}
 *
 * @generated by MUSUBIX from C4 design
 * @module ${toKebabCase(className)}
 * @designElement ${id}
 *
${patternComments}
${reqComments}
 */

/**
 * Base entity interface for repository
 */
export interface BaseEntity {
  id: string;
  createdAt: Date;
  updatedAt: Date;
}

/**
 * Query options for repository
 */
export interface QueryOptions {
  limit?: number;
  offset?: number;
  orderBy?: string;
  orderDir?: 'asc' | 'desc';
}

/**
 * ${className} interface
 */
export interface ${interfaceName}<T extends BaseEntity = BaseEntity> {
  save(entity: T): Promise<T>;
  findById(id: string): Promise<T | null>;
  findAll(options?: QueryOptions): Promise<T[]>;
  update(id: string, data: Partial<T>): Promise<T | null>;
  delete(id: string): Promise<boolean>;
  count(): Promise<number>;
}

/**
 * ${className} implementation
 */
export class ${className}<T extends BaseEntity = BaseEntity> implements ${interfaceName}<T> {
  private storage: Map<string, T> = new Map();

  /**
   * Save entity to repository
   */
  async save(entity: T): Promise<T> {
    this.storage.set(entity.id, entity);
    return entity;
  }

  /**
   * Find entity by ID
   */
  async findById(id: string): Promise<T | null> {
    return this.storage.get(id) ?? null;
  }

  /**
   * Find all entities
   */
  async findAll(options?: QueryOptions): Promise<T[]> {
    let results = Array.from(this.storage.values());

    if (options?.orderBy) {
      results.sort((a, b) => {
        const aVal = (a as Record<string, unknown>)[options.orderBy!];
        const bVal = (b as Record<string, unknown>)[options.orderBy!];
        const cmp = aVal < bVal ? -1 : aVal > bVal ? 1 : 0;
        return options.orderDir === 'desc' ? -cmp : cmp;
      });
    }

    if (options?.offset) {
      results = results.slice(options.offset);
    }
    if (options?.limit) {
      results = results.slice(0, options.limit);
    }

    return results;
  }

  /**
   * Update entity
   */
  async update(id: string, data: Partial<T>): Promise<T | null> {
    const entity = this.storage.get(id);
    if (!entity) return null;

    const updated = { ...entity, ...data, updatedAt: new Date() } as T;
    this.storage.set(id, updated);
    return updated;
  }

  /**
   * Delete entity
   */
  async delete(id: string): Promise<boolean> {
    return this.storage.delete(id);
  }

  /**
   * Count entities
   */
  async count(): Promise<number> {
    return this.storage.size;
  }
}

/**
 * Factory function
 */
export function create${className}<T extends BaseEntity = BaseEntity>(): ${interfaceName}<T> {
  return new ${className}<T>();
}
`;
}

/**
 * Generate Service template with proper types and domain-specific methods
 * Enhanced in v1.1.2: Uses ComponentInference for domain-aware method generation
 */
function generateServiceTemplate(
  className: string,
  interfaceName: string,
  id: string,
  description: string,
  patternComments: string,
  reqComments: string,
  domainId?: string
): string {
  const baseName = className.replace(/Service$/, '');

  // Get domain-specific methods from ComponentInference
  const componentInference = new ComponentInference();
  const domainMethods = componentInference.getMethodsForComponent(className, domainId);

  // Generate interface methods and implementations
  const hasExtraMethods = domainMethods.length > 0;
  const extraInterfaceMethods = hasExtraMethods
    ? '\n  // Domain-specific methods\n' + generateInterfaceMethods(domainMethods)
    : '';
  const extraImplementations = hasExtraMethods
    ? '\n\n  // Domain-specific methods' + domainMethods.map(m => generateMethodImplementation(m, baseName)).join('')
    : '';

  return `/**
 * ${className}
 * ${description}
 *
 * @generated by MUSUBIX from C4 design
 * @module ${toKebabCase(className)}
 * @designElement ${id}
 *
${patternComments}
${reqComments}
 */

/**
 * Create input type
 */
export interface Create${baseName}Input {
  name: string;
  description?: string;
  [key: string]: unknown;
}

/**
 * Update input type
 */
export interface Update${baseName}Input {
  name?: string;
  description?: string;
  [key: string]: unknown;
}

/**
 * Filter options type
 */
export interface ${baseName}FilterOptions {
  search?: string;
  limit?: number;
  offset?: number;
  sortBy?: string;
  sortDir?: 'asc' | 'desc';
}

/**
 * Entity type
 */
export interface ${baseName}Entity {
  id: string;
  name: string;
  description?: string;
  createdAt: Date;
  updatedAt: Date;
}

/**
 * ${className} interface
 */
export interface ${interfaceName} {
  // Core CRUD methods
  create(data: Create${baseName}Input): Promise<${baseName}Entity>;
  getById(id: string): Promise<${baseName}Entity | null>;
  getAll(filter?: ${baseName}FilterOptions): Promise<${baseName}Entity[]>;
  update(id: string, data: Update${baseName}Input): Promise<${baseName}Entity | null>;
  delete(id: string): Promise<boolean>;
${extraInterfaceMethods}
}

/**
 * ${className} implementation
 */
export class ${className} implements ${interfaceName} {
  private entities: Map<string, ${baseName}Entity> = new Map();

  /**
   * Create a new entity
   */
  async create(data: Create${baseName}Input): Promise<${baseName}Entity> {
    const entity: ${baseName}Entity = {
      id: crypto.randomUUID(),
      name: data.name,
      description: data.description,
      createdAt: new Date(),
      updatedAt: new Date(),
    };
    this.entities.set(entity.id, entity);
    return entity;
  }

  /**
   * Get entity by ID
   */
  async getById(id: string): Promise<${baseName}Entity | null> {
    return this.entities.get(id) ?? null;
  }

  /**
   * Get all entities with optional filtering
   */
  async getAll(filter?: ${baseName}FilterOptions): Promise<${baseName}Entity[]> {
    let results = Array.from(this.entities.values());

    if (filter?.search) {
      const searchLower = filter.search.toLowerCase();
      results = results.filter(e =>
        e.name.toLowerCase().includes(searchLower) ||
        e.description?.toLowerCase().includes(searchLower)
      );
    }

    if (filter?.sortBy) {
      results.sort((a, b) => {
        const aVal = (a as Record<string, unknown>)[filter.sortBy!];
        const bVal = (b as Record<string, unknown>)[filter.sortBy!];
        const cmp = aVal < bVal ? -1 : aVal > bVal ? 1 : 0;
        return filter.sortDir === 'desc' ? -cmp : cmp;
      });
    }

    if (filter?.offset) {
      results = results.slice(filter.offset);
    }
    if (filter?.limit) {
      results = results.slice(0, filter.limit);
    }

    return results;
  }

  /**
   * Update an entity
   */
  async update(id: string, data: Update${baseName}Input): Promise<${baseName}Entity | null> {
    const entity = this.entities.get(id);
    if (!entity) return null;

    const updated: ${baseName}Entity = {
      ...entity,
      ...data,
      updatedAt: new Date(),
    };
    this.entities.set(id, updated);
    return updated;
  }

  /**
   * Delete an entity
   */
  async delete(id: string): Promise<boolean> {
    return this.entities.delete(id);
  }${extraImplementations}
}

/**
 * Factory function
 */
export function create${className}(): ${interfaceName} {
  return new ${className}();
}
`;
}
