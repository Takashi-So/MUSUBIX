/**
 * Enhanced Code Generator
 *
 * C4設計ドキュメントからスケルトンコードを自動生成。
 * EARS要件からテストコードを自動生成。
 *
 * @packageDocumentation
 * @module codegen/enhanced-generator
 *
 * @see REQ-YI-GEN-001 - C4 Design to Code
 * @see REQ-YI-GEN-002 - EARS to Test
 * @see REQ-YI-GEN-003 - Traceability Maintenance
 * @see DES-YATA-IMPROVEMENTS-001 - Design Document
 */

import * as fs from 'fs';
import * as path from 'path';
import type {
  TargetLanguage,
  PropertyDefinition,
  MethodDefinition,
  ParameterDefinition,
} from './generator.js';

// ============================================================
// Types
// ============================================================

/**
 * Code generation configuration
 * @see REQ-YI-GEN-001
 */
export interface CodeGenConfig {
  /** Output directory */
  outputDir: string;
  /** Target language */
  language: TargetLanguage;
  /** Framework (optional) */
  framework?: 'express' | 'fastify' | 'nestjs' | 'none';
  /** Include test files */
  includeTests: boolean;
  /** Test framework */
  testFramework: 'vitest' | 'jest';
  /** Custom template directory */
  templateDir?: string;
  /** Dry run - don't write files */
  dryRun?: boolean;
  /** Overwrite existing files */
  overwrite?: boolean;
}

/**
 * Generated file information
 */
export interface GeneratedFile {
  /** File path (relative to outputDir) */
  path: string;
  /** File content */
  content: string;
  /** Associated requirement IDs */
  requirementIds: string[];
  /** Associated design element IDs */
  designElementIds: string[];
  /** File type */
  fileType: 'entity' | 'repository' | 'service' | 'controller' | 'test' | 'types' | 'index';
}

/**
 * Traceability entry
 * @see REQ-YI-GEN-003
 */
export interface TraceabilityEntry {
  /** Requirement ID (REQ-*) */
  requirementId: string;
  /** Design element ID (DES-*) */
  designElementId: string;
  /** Generated file path */
  filePath: string;
  /** Line numbers where the requirement is implemented */
  lineNumbers: number[];
  /** Code element (class, method, etc.) */
  codeElement?: string;
}

/**
 * Generation result
 */
export interface GenerationResult {
  /** Whether generation was successful */
  success: boolean;
  /** Generated files */
  files: GeneratedFile[];
  /** Traceability map */
  traceabilityMap: TraceabilityEntry[];
  /** Warnings */
  warnings: string[];
  /** Errors */
  errors: string[];
  /** Statistics */
  stats: {
    totalFiles: number;
    entities: number;
    repositories: number;
    services: number;
    controllers: number;
    tests: number;
  };
}

/**
 * C4 Design component
 */
export interface C4Component {
  /** Component ID */
  id: string;
  /** Component name */
  name: string;
  /** Component type */
  type: 'entity' | 'repository' | 'service' | 'controller' | 'value-object' | 'factory';
  /** Description */
  description?: string;
  /** Properties */
  properties: PropertyDefinition[];
  /** Methods */
  methods: MethodDefinition[];
  /** Dependencies */
  dependencies: string[];
  /** Associated requirements */
  requirementIds: string[];
  /** Associated design elements */
  designElementIds: string[];
}

/**
 * Parsed C4 design document
 */
export interface C4Design {
  /** Design document title */
  title: string;
  /** Version */
  version?: string;
  /** Components */
  components: C4Component[];
  /** Relationships */
  relationships: Array<{
    source: string;
    target: string;
    label: string;
  }>;
}

/**
 * EARS requirement
 */
export interface EARSRequirement {
  /** Requirement ID */
  id: string;
  /** Requirement type */
  type: 'ubiquitous' | 'event-driven' | 'state-driven' | 'unwanted' | 'optional';
  /** Subject (system) */
  subject: string;
  /** Trigger (event/state/condition) */
  trigger?: string;
  /** Requirement (shall statement) */
  requirement: string;
  /** Full EARS text */
  text: string;
}

/**
 * Default configuration
 */
export const DEFAULT_CODEGEN_CONFIG: Partial<CodeGenConfig> = {
  language: 'typescript',
  framework: 'none',
  includeTests: true,
  testFramework: 'vitest',
  dryRun: false,
  overwrite: false,
};

// ============================================================
// EnhancedCodeGenerator Class
// ============================================================

/**
 * Enhanced Code Generator
 *
 * Generates skeleton code from C4 design documents and
 * test code from EARS requirements.
 *
 * @example
 * ```typescript
 * const generator = new EnhancedCodeGenerator({
 *   outputDir: './src',
 *   language: 'typescript',
 *   includeTests: true,
 *   testFramework: 'vitest',
 * });
 *
 * const design = await generator.parseDesign('./design/system.md');
 * const result = await generator.generateFromDesign(design);
 * console.log(`Generated ${result.stats.totalFiles} files`);
 * ```
 *
 * @see REQ-YI-GEN-001
 * @see REQ-YI-GEN-002
 * @see REQ-YI-GEN-003
 */
export class EnhancedCodeGenerator {
  private config: CodeGenConfig;

  constructor(config: Partial<CodeGenConfig>) {
    this.config = { ...DEFAULT_CODEGEN_CONFIG, ...config } as CodeGenConfig;
  }

  // ============================================================
  // Public API
  // ============================================================

  /**
   * Parse C4 design document from Markdown
   * @see REQ-YI-GEN-001
   */
  parseDesign(content: string): C4Design {
    const design: C4Design = {
      title: '',
      components: [],
      relationships: [],
    };

    // Parse title
    const titleMatch = content.match(/^#\s+(.+)$/m);
    if (titleMatch) {
      design.title = titleMatch[1];
    }

    // Parse version
    const versionMatch = content.match(/Version:\s*(\S+)/i);
    if (versionMatch) {
      design.version = versionMatch[1];
    }

    // Parse components from TypeScript interface definitions
    const interfacePattern = /interface\s+(\w+)\s*{([^}]*)}/g;
    let match;
    while ((match = interfacePattern.exec(content)) !== null) {
      const component = this.parseInterface(match[1], match[2], content);
      if (component) {
        design.components.push(component);
      }
    }

    // Parse components from code blocks with type annotations
    const codeBlockPattern = /```(?:typescript|ts)\n([\s\S]*?)```/g;
    while ((match = codeBlockPattern.exec(content)) !== null) {
      const components = this.parseCodeBlock(match[1]);
      for (const comp of components) {
        // Avoid duplicates
        if (!design.components.some(c => c.name === comp.name)) {
          design.components.push(comp);
        }
      }
    }

    // Parse component definitions from markdown sections
    const sectionPattern = /###\s+\d+\.\d+\s+(?:Component:\s+)?(\w+)/g;
    while ((match = sectionPattern.exec(content)) !== null) {
      const componentName = match[1];
      const existing = design.components.find(c => c.name === componentName);
      if (!existing) {
        // Extract info from section
        const component = this.parseMarkdownSection(componentName, content, match.index);
        if (component) {
          design.components.push(component);
        }
      }
    }

    // Parse relationships
    const arrowPattern = /(\w+)\s*-+>\s*(\w+)\s*:\s*(.+)/g;
    while ((match = arrowPattern.exec(content)) !== null) {
      design.relationships.push({
        source: match[1],
        target: match[2],
        label: match[3].trim(),
      });
    }

    return design;
  }

  /**
   * Generate code from C4 design
   * @see REQ-YI-GEN-001
   */
  async generateFromDesign(design: C4Design): Promise<GenerationResult> {
    const result: GenerationResult = {
      success: true,
      files: [],
      traceabilityMap: [],
      warnings: [],
      errors: [],
      stats: {
        totalFiles: 0,
        entities: 0,
        repositories: 0,
        services: 0,
        controllers: 0,
        tests: 0,
      },
    };

    try {
      // Generate code for each component
      for (const component of design.components) {
        const files = this.generateComponentCode(component);
        result.files.push(...files);

        // Update stats
        for (const file of files) {
          result.stats.totalFiles++;
          switch (file.fileType) {
            case 'entity':
              result.stats.entities++;
              break;
            case 'repository':
              result.stats.repositories++;
              break;
            case 'service':
              result.stats.services++;
              break;
            case 'controller':
              result.stats.controllers++;
              break;
            case 'test':
              result.stats.tests++;
              break;
          }
        }

        // Generate traceability entries
        for (const file of files) {
          for (const reqId of file.requirementIds) {
            result.traceabilityMap.push({
              requirementId: reqId,
              designElementId: component.id || component.name,
              filePath: file.path,
              lineNumbers: [1],
              codeElement: component.name,
            });
          }
        }
      }

      // Write files (unless dry run)
      if (!this.config.dryRun) {
        await this.writeFiles(result.files, result);
      }

    } catch (error) {
      result.success = false;
      result.errors.push(error instanceof Error ? error.message : String(error));
    }

    return result;
  }

  /**
   * Parse EARS requirements from text
   * @see REQ-YI-GEN-002
   */
  parseEARSRequirements(content: string): EARSRequirement[] {
    const requirements: EARSRequirement[] = [];

    const lines = content.split('\n');
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i].trim();
      
      // Check for requirement ID
      const idMatch = line.match(/^(REQ-[\w-]+)/);
      if (idMatch) {
        const id = idMatch[1];
        // Get requirement text
        const text = line.substring(idMatch[0].length).trim();
        const earsReq = this.parseEARSStatement(id, text);
        if (earsReq) {
          requirements.push(earsReq);
        }
      }
    }

    return requirements;
  }

  /**
   * Generate test code from EARS requirements
   * @see REQ-YI-GEN-002
   */
  generateTestsFromEARS(requirements: EARSRequirement[]): GeneratedFile[] {
    const files: GeneratedFile[] = [];

    // Group requirements by subject
    const bySubject = new Map<string, EARSRequirement[]>();
    for (const req of requirements) {
      const existing = bySubject.get(req.subject) || [];
      existing.push(req);
      bySubject.set(req.subject, existing);
    }

    // Generate test file for each subject
    for (const [subject, reqs] of bySubject) {
      const testFile = this.generateTestFile(subject, reqs);
      files.push(testFile);
    }

    return files;
  }

  /**
   * Generate traceability matrix
   * @see REQ-YI-GEN-003
   */
  generateTraceabilityMatrix(entries: TraceabilityEntry[]): string {
    let markdown = '# Traceability Matrix\n\n';
    markdown += '| Requirement | Design Element | File | Lines | Code Element |\n';
    markdown += '|-------------|----------------|------|-------|-------------|\n';

    for (const entry of entries) {
      markdown += `| ${entry.requirementId} | ${entry.designElementId} | ${entry.filePath} | ${entry.lineNumbers.join(', ')} | ${entry.codeElement || '-'} |\n`;
    }

    return markdown;
  }

  // ============================================================
  // Internal: Parsing
  // ============================================================

  /**
   * Parse TypeScript interface to component
   */
  private parseInterface(name: string, body: string, _context: string): C4Component | null {
    const properties: PropertyDefinition[] = [];
    const methods: MethodDefinition[] = [];

    // Parse properties
    const propPattern = /(\w+)(\?)?:\s*(.+);/g;
    let match;
    while ((match = propPattern.exec(body)) !== null) {
      const propName = match[1];
      const isOptional = match[2] === '?';
      const propType = match[3].trim();

      // Check if it's a method signature
      if (propType.includes('=>') || propType.includes('(')) {
        // It's a method
        const methodDef = this.parseMethodSignature(propName, propType, isOptional);
        if (methodDef) {
          methods.push(methodDef);
        }
      } else {
        properties.push({
          name: propName,
          type: propType,
          optional: isOptional,
        });
      }
    }

    // Determine component type from name
    const type = this.inferComponentType(name);

    return {
      id: `DES-${name}`,
      name,
      type,
      properties,
      methods,
      dependencies: [],
      requirementIds: [],
      designElementIds: [`DES-${name}`],
    };
  }

  /**
   * Parse code block for components
   */
  private parseCodeBlock(code: string): C4Component[] {
    const components: C4Component[] = [];

    // Parse interfaces
    const interfacePattern = /interface\s+(\w+)\s*{([^}]*)}/g;
    let match;
    while ((match = interfacePattern.exec(code)) !== null) {
      const comp = this.parseInterface(match[1], match[2], code);
      if (comp) {
        components.push(comp);
      }
    }

    // Parse classes
    const classPattern = /class\s+(\w+)\s*(?:extends\s+\w+)?\s*(?:implements\s+[\w,\s]+)?\s*{/g;
    while ((match = classPattern.exec(code)) !== null) {
      const className = match[1];
      const type = this.inferComponentType(className);
      components.push({
        id: `DES-${className}`,
        name: className,
        type,
        properties: [],
        methods: [],
        dependencies: [],
        requirementIds: [],
        designElementIds: [`DES-${className}`],
      });
    }

    return components;
  }

  /**
   * Parse markdown section for component info
   */
  private parseMarkdownSection(name: string, content: string, startIndex: number): C4Component | null {
    // Find section content
    const sectionEnd = content.indexOf('\n## ', startIndex + 1);
    const sectionContent = content.substring(
      startIndex,
      sectionEnd > 0 ? sectionEnd : content.length
    );

    // Extract requirement IDs
    const reqIds: string[] = [];
    const reqPattern = /REQ-[\w-]+/g;
    let match;
    while ((match = reqPattern.exec(sectionContent)) !== null) {
      reqIds.push(match[0]);
    }

    // Extract design element IDs
    const desIds: string[] = [];
    const desPattern = /DES-[\w-]+/g;
    while ((match = desPattern.exec(sectionContent)) !== null) {
      desIds.push(match[0]);
    }

    return {
      id: `DES-${name}`,
      name,
      type: this.inferComponentType(name),
      properties: [],
      methods: [],
      dependencies: [],
      requirementIds: reqIds,
      designElementIds: desIds.length > 0 ? desIds : [`DES-${name}`],
    };
  }

  /**
   * Parse method signature
   */
  private parseMethodSignature(
    name: string,
    signature: string,
    _optional: boolean
  ): MethodDefinition | null {
    // Parse (params) => returnType
    const arrowMatch = signature.match(/\(([^)]*)\)\s*=>\s*(.+)/);
    if (arrowMatch) {
      const params = this.parseParameters(arrowMatch[1]);
      return {
        name,
        parameters: params,
        returnType: arrowMatch[2].trim(),
        visibility: 'public',
        async: arrowMatch[2].includes('Promise'),
      };
    }

    return null;
  }

  /**
   * Parse parameter list
   */
  private parseParameters(paramStr: string): ParameterDefinition[] {
    const params: ParameterDefinition[] = [];
    if (!paramStr.trim()) return params;

    const parts = paramStr.split(',');
    for (const part of parts) {
      const match = part.trim().match(/(\w+)(\?)?:\s*(.+)/);
      if (match) {
        params.push({
          name: match[1],
          type: match[3].trim(),
          optional: match[2] === '?',
        });
      }
    }

    return params;
  }

  /**
   * Infer component type from name
   */
  private inferComponentType(name: string): C4Component['type'] {
    const lowerName = name.toLowerCase();
    if (lowerName.includes('repository')) return 'repository';
    if (lowerName.includes('service')) return 'service';
    if (lowerName.includes('controller')) return 'controller';
    if (lowerName.includes('factory')) return 'factory';
    if (lowerName.includes('vo') || lowerName.includes('valueobject')) return 'value-object';
    return 'entity';
  }

  /**
   * Parse EARS statement
   */
  private parseEARSStatement(id: string, text: string): EARSRequirement | null {
    const upperText = text.toUpperCase();
    let type: EARSRequirement['type'];
    let trigger: string | undefined;
    let subject = '';
    let requirement = '';

    if (upperText.startsWith('WHEN ')) {
      type = 'event-driven';
      const match = text.match(/WHEN\s+(.+?),?\s+THE\s+(.+?)\s+SHALL\s+(.+)/i);
      if (match) {
        trigger = match[1];
        subject = match[2];
        requirement = match[3];
      }
    } else if (upperText.startsWith('WHILE ')) {
      type = 'state-driven';
      const match = text.match(/WHILE\s+(.+?),?\s+THE\s+(.+?)\s+SHALL\s+(.+)/i);
      if (match) {
        trigger = match[1];
        subject = match[2];
        requirement = match[3];
      }
    } else if (upperText.startsWith('IF ')) {
      type = 'optional';
      const match = text.match(/IF\s+(.+?),?\s+THEN\s+THE\s+(.+?)\s+SHALL\s+(.+)/i);
      if (match) {
        trigger = match[1];
        subject = match[2];
        requirement = match[3];
      }
    } else if (upperText.includes('SHALL NOT')) {
      type = 'unwanted';
      const match = text.match(/THE\s+(.+?)\s+SHALL\s+NOT\s+(.+)/i);
      if (match) {
        subject = match[1];
        requirement = `NOT ${match[2]}`;
      }
    } else {
      type = 'ubiquitous';
      const match = text.match(/THE\s+(.+?)\s+SHALL\s+(.+)/i);
      if (match) {
        subject = match[1];
        requirement = match[2];
      }
    }

    if (!subject || !requirement) {
      return null;
    }

    return {
      id,
      type,
      subject,
      trigger,
      requirement,
      text,
    };
  }

  // ============================================================
  // Internal: Code Generation
  // ============================================================

  /**
   * Generate code for a component
   */
  private generateComponentCode(component: C4Component): GeneratedFile[] {
    const files: GeneratedFile[] = [];

    switch (component.type) {
      case 'entity':
        files.push(this.generateEntityCode(component));
        if (this.config.includeTests) {
          files.push(this.generateEntityTestCode(component));
        }
        break;
      case 'repository':
        files.push(this.generateRepositoryCode(component));
        if (this.config.includeTests) {
          files.push(this.generateRepositoryTestCode(component));
        }
        break;
      case 'service':
        files.push(this.generateServiceCode(component));
        if (this.config.includeTests) {
          files.push(this.generateServiceTestCode(component));
        }
        break;
      case 'controller':
        files.push(this.generateControllerCode(component));
        if (this.config.includeTests) {
          files.push(this.generateControllerTestCode(component));
        }
        break;
      case 'value-object':
        files.push(this.generateValueObjectCode(component));
        if (this.config.includeTests) {
          files.push(this.generateValueObjectTestCode(component));
        }
        break;
      case 'factory':
        files.push(this.generateFactoryCode(component));
        break;
    }

    return files;
  }

  /**
   * Generate entity code
   */
  private generateEntityCode(component: C4Component): GeneratedFile {
    const fileName = this.toKebabCase(component.name);
    const lines: string[] = [];

    // Header
    lines.push('/**');
    lines.push(` * ${component.name}`);
    if (component.description) {
      lines.push(` * ${component.description}`);
    }
    lines.push(' *');
    for (const reqId of component.requirementIds) {
      lines.push(` * @see ${reqId}`);
    }
    lines.push(' */');
    lines.push('');

    // Interface
    lines.push(`export interface ${component.name}Input {`);
    for (const prop of component.properties) {
      if (prop.name !== 'id' && prop.name !== 'createdAt' && prop.name !== 'updatedAt') {
        const opt = prop.optional ? '?' : '';
        lines.push(`  ${prop.name}${opt}: ${prop.type};`);
      }
    }
    lines.push('}');
    lines.push('');

    // Entity interface
    lines.push(`export interface ${component.name} {`);
    lines.push('  readonly id: string;');
    for (const prop of component.properties) {
      if (prop.name !== 'id') {
        const ro = prop.readonly ? 'readonly ' : '';
        const opt = prop.optional ? '?' : '';
        lines.push(`  ${ro}${prop.name}${opt}: ${prop.type};`);
      }
    }
    lines.push('  readonly createdAt: Date;');
    lines.push('  readonly updatedAt: Date;');
    lines.push('}');
    lines.push('');

    // Factory function
    lines.push(`let ${this.toCamelCase(component.name)}Counter = 0;`);
    lines.push('');
    lines.push(`export function create${component.name}(input: ${component.name}Input): ${component.name} {`);
    lines.push('  const now = new Date();');
    lines.push('  const dateStr = now.toISOString().slice(0, 10).replace(/-/g, \'\');');
    lines.push(`  const id = \`${component.name.toUpperCase().slice(0, 3)}-\${dateStr}-\${String(++${this.toCamelCase(component.name)}Counter).padStart(3, '0')}\`;`);
    lines.push('  return {');
    lines.push('    id,');
    for (const prop of component.properties) {
      if (prop.name !== 'id' && prop.name !== 'createdAt' && prop.name !== 'updatedAt') {
        lines.push(`    ${prop.name}: input.${prop.name},`);
      }
    }
    lines.push('    createdAt: now,');
    lines.push('    updatedAt: now,');
    lines.push('  };');
    lines.push('}');
    lines.push('');

    // Reset function for testing
    lines.push(`export function reset${component.name}Counter(): void {`);
    lines.push(`  ${this.toCamelCase(component.name)}Counter = 0;`);
    lines.push('}');

    return {
      path: `${fileName}.ts`,
      content: lines.join('\n'),
      requirementIds: component.requirementIds,
      designElementIds: component.designElementIds,
      fileType: 'entity',
    };
  }

  /**
   * Generate entity test code
   */
  private generateEntityTestCode(component: C4Component): GeneratedFile {
    const fileName = this.toKebabCase(component.name);
    const framework = this.config.testFramework;
    const lines: string[] = [];

    // Imports
    lines.push(`import { describe, it, expect, beforeEach } from '${framework}';`);
    lines.push(`import { create${component.name}, reset${component.name}Counter } from './${fileName}.js';`);
    lines.push('');

    // Test suite
    lines.push(`describe('${component.name}', () => {`);
    lines.push('  beforeEach(() => {');
    lines.push(`    reset${component.name}Counter();`);
    lines.push('  });');
    lines.push('');

    // Creation test
    lines.push(`  describe('create${component.name}', () => {`);
    lines.push(`    it('should create ${component.name} with generated ID', () => {`);
    lines.push(`      const input = {`);
    for (const prop of component.properties) {
      if (prop.name !== 'id' && prop.name !== 'createdAt' && prop.name !== 'updatedAt') {
        const value = this.getTestValue(prop.type, prop.name);
        lines.push(`        ${prop.name}: ${value},`);
      }
    }
    lines.push('      };');
    lines.push(`      const entity = create${component.name}(input);`);
    lines.push('');
    lines.push(`      expect(entity.id).toMatch(/^${component.name.toUpperCase().slice(0, 3)}-\\d{8}-001$/);`);
    for (const prop of component.properties) {
      if (prop.name !== 'id' && prop.name !== 'createdAt' && prop.name !== 'updatedAt') {
        lines.push(`      expect(entity.${prop.name}).toBe(input.${prop.name});`);
      }
    }
    lines.push('      expect(entity.createdAt).toBeInstanceOf(Date);');
    lines.push('      expect(entity.updatedAt).toBeInstanceOf(Date);');
    lines.push('    });');
    lines.push('');

    lines.push('    it(\'should increment counter for sequential IDs\', () => {');
    lines.push(`      const input1 = { ${this.getMinimalInput(component)} };`);
    lines.push(`      const input2 = { ${this.getMinimalInput(component)} };`);
    lines.push(`      const entity1 = create${component.name}(input1);`);
    lines.push(`      const entity2 = create${component.name}(input2);`);
    lines.push('');
    lines.push('      expect(entity1.id).toMatch(/-001$/);');
    lines.push('      expect(entity2.id).toMatch(/-002$/);');
    lines.push('    });');
    lines.push('  });');

    lines.push('});');

    return {
      path: `${fileName}.test.ts`,
      content: lines.join('\n'),
      requirementIds: component.requirementIds,
      designElementIds: component.designElementIds,
      fileType: 'test',
    };
  }

  /**
   * Generate repository code
   */
  private generateRepositoryCode(component: C4Component): GeneratedFile {
    const fileName = this.toKebabCase(component.name);
    const entityName = component.name.replace('Repository', '');
    const lines: string[] = [];

    // Header
    lines.push('/**');
    lines.push(` * ${component.name}`);
    lines.push(' *');
    for (const reqId of component.requirementIds) {
      lines.push(` * @see ${reqId}`);
    }
    lines.push(' */');
    lines.push('');

    // Import entity (placeholder)
    lines.push(`// import type { ${entityName} } from './${this.toKebabCase(entityName)}.js';`);
    lines.push('');

    // Interface
    lines.push(`export interface ${component.name} {`);
    lines.push(`  findById(id: string): Promise<unknown | null>;`);
    lines.push(`  findAll(): Promise<unknown[]>;`);
    lines.push(`  save(entity: unknown): Promise<void>;`);
    lines.push(`  delete(id: string): Promise<boolean>;`);
    for (const method of component.methods) {
      const params = (method.parameters || [])
        .map(p => `${p.name}${p.optional ? '?' : ''}: ${p.type}`)
        .join(', ');
      lines.push(`  ${method.name}(${params}): ${method.returnType || 'void'};`);
    }
    lines.push('}');
    lines.push('');

    // In-memory implementation
    lines.push(`export class InMemory${component.name} implements ${component.name} {`);
    lines.push('  private storage = new Map<string, unknown>();');
    lines.push('');
    lines.push('  async findById(id: string): Promise<unknown | null> {');
    lines.push('    return this.storage.get(id) ?? null;');
    lines.push('  }');
    lines.push('');
    lines.push('  async findAll(): Promise<unknown[]> {');
    lines.push('    return Array.from(this.storage.values());');
    lines.push('  }');
    lines.push('');
    lines.push('  async save(entity: unknown): Promise<void> {');
    lines.push('    const e = entity as { id: string };');
    lines.push('    this.storage.set(e.id, entity);');
    lines.push('  }');
    lines.push('');
    lines.push('  async delete(id: string): Promise<boolean> {');
    lines.push('    return this.storage.delete(id);');
    lines.push('  }');
    lines.push('}');

    return {
      path: `${fileName}.ts`,
      content: lines.join('\n'),
      requirementIds: component.requirementIds,
      designElementIds: component.designElementIds,
      fileType: 'repository',
    };
  }

  /**
   * Generate repository test code
   */
  private generateRepositoryTestCode(component: C4Component): GeneratedFile {
    const fileName = this.toKebabCase(component.name);
    const framework = this.config.testFramework;
    const lines: string[] = [];

    lines.push(`import { describe, it, expect, beforeEach } from '${framework}';`);
    lines.push(`import { InMemory${component.name} } from './${fileName}.js';`);
    lines.push('');
    lines.push(`describe('${component.name}', () => {`);
    lines.push(`  let repository: InMemory${component.name};`);
    lines.push('');
    lines.push('  beforeEach(() => {');
    lines.push(`    repository = new InMemory${component.name}();`);
    lines.push('  });');
    lines.push('');
    lines.push('  it(\'should save and find entity\', async () => {');
    lines.push('    const entity = { id: \'test-1\', name: \'Test\' };');
    lines.push('    await repository.save(entity);');
    lines.push('    const found = await repository.findById(\'test-1\');');
    lines.push('    expect(found).toEqual(entity);');
    lines.push('  });');
    lines.push('');
    lines.push('  it(\'should return null for non-existent entity\', async () => {');
    lines.push('    const found = await repository.findById(\'non-existent\');');
    lines.push('    expect(found).toBeNull();');
    lines.push('  });');
    lines.push('');
    lines.push('  it(\'should delete entity\', async () => {');
    lines.push('    const entity = { id: \'test-1\', name: \'Test\' };');
    lines.push('    await repository.save(entity);');
    lines.push('    const deleted = await repository.delete(\'test-1\');');
    lines.push('    expect(deleted).toBe(true);');
    lines.push('    const found = await repository.findById(\'test-1\');');
    lines.push('    expect(found).toBeNull();');
    lines.push('  });');
    lines.push('});');

    return {
      path: `${fileName}.test.ts`,
      content: lines.join('\n'),
      requirementIds: component.requirementIds,
      designElementIds: component.designElementIds,
      fileType: 'test',
    };
  }

  /**
   * Generate service code
   */
  private generateServiceCode(component: C4Component): GeneratedFile {
    const fileName = this.toKebabCase(component.name);
    const lines: string[] = [];

    lines.push('/**');
    lines.push(` * ${component.name}`);
    lines.push(' *');
    for (const reqId of component.requirementIds) {
      lines.push(` * @see ${reqId}`);
    }
    lines.push(' */');
    lines.push('');
    lines.push(`export class ${component.name} {`);
    lines.push('  // TODO: Implement service methods');
    for (const method of component.methods) {
      const params = (method.parameters || [])
        .map(p => `${p.name}${p.optional ? '?' : ''}: ${p.type}`)
        .join(', ');
      const async = method.async ? 'async ' : '';
      lines.push('');
      lines.push(`  ${async}${method.name}(${params}): ${method.returnType || 'void'} {`);
      lines.push('    throw new Error(\'Not implemented\');');
      lines.push('  }');
    }
    lines.push('}');

    return {
      path: `${fileName}.ts`,
      content: lines.join('\n'),
      requirementIds: component.requirementIds,
      designElementIds: component.designElementIds,
      fileType: 'service',
    };
  }

  /**
   * Generate service test code
   */
  private generateServiceTestCode(component: C4Component): GeneratedFile {
    const fileName = this.toKebabCase(component.name);
    const framework = this.config.testFramework;
    const lines: string[] = [];

    lines.push(`import { describe, it, expect } from '${framework}';`);
    lines.push(`import { ${component.name} } from './${fileName}.js';`);
    lines.push('');
    lines.push(`describe('${component.name}', () => {`);
    lines.push('  // TODO: Add service tests');
    lines.push('  it(\'should be defined\', () => {');
    lines.push(`    const service = new ${component.name}();`);
    lines.push('    expect(service).toBeDefined();');
    lines.push('  });');
    lines.push('});');

    return {
      path: `${fileName}.test.ts`,
      content: lines.join('\n'),
      requirementIds: component.requirementIds,
      designElementIds: component.designElementIds,
      fileType: 'test',
    };
  }

  /**
   * Generate controller code
   */
  private generateControllerCode(component: C4Component): GeneratedFile {
    const fileName = this.toKebabCase(component.name);
    const lines: string[] = [];

    lines.push('/**');
    lines.push(` * ${component.name}`);
    lines.push(' *');
    for (const reqId of component.requirementIds) {
      lines.push(` * @see ${reqId}`);
    }
    lines.push(' */');
    lines.push('');
    lines.push(`export class ${component.name} {`);
    lines.push('  // TODO: Implement controller methods');
    lines.push('}');

    return {
      path: `${fileName}.ts`,
      content: lines.join('\n'),
      requirementIds: component.requirementIds,
      designElementIds: component.designElementIds,
      fileType: 'controller',
    };
  }

  /**
   * Generate controller test code
   */
  private generateControllerTestCode(component: C4Component): GeneratedFile {
    const fileName = this.toKebabCase(component.name);
    const framework = this.config.testFramework;
    const lines: string[] = [];

    lines.push(`import { describe, it, expect } from '${framework}';`);
    lines.push(`import { ${component.name} } from './${fileName}.js';`);
    lines.push('');
    lines.push(`describe('${component.name}', () => {`);
    lines.push('  // TODO: Add controller tests');
    lines.push('  it(\'should be defined\', () => {');
    lines.push(`    const controller = new ${component.name}();`);
    lines.push('    expect(controller).toBeDefined();');
    lines.push('  });');
    lines.push('});');

    return {
      path: `${fileName}.test.ts`,
      content: lines.join('\n'),
      requirementIds: component.requirementIds,
      designElementIds: component.designElementIds,
      fileType: 'test',
    };
  }

  /**
   * Generate value object code
   */
  private generateValueObjectCode(component: C4Component): GeneratedFile {
    const fileName = this.toKebabCase(component.name);
    const lines: string[] = [];

    lines.push('/**');
    lines.push(` * ${component.name} Value Object`);
    lines.push(' *');
    for (const reqId of component.requirementIds) {
      lines.push(` * @see ${reqId}`);
    }
    lines.push(' */');
    lines.push('');
    lines.push(`export interface ${component.name} {`);
    for (const prop of component.properties) {
      lines.push(`  readonly ${prop.name}: ${prop.type};`);
    }
    lines.push('}');
    lines.push('');
    lines.push(`export type ${component.name}Error = string;`);
    lines.push('');
    lines.push(`export type ${component.name}Result = `);
    lines.push(`  | { success: true; value: ${component.name} }`);
    lines.push(`  | { success: false; error: ${component.name}Error };`);
    lines.push('');
    lines.push(`export function create${component.name}(`);
    for (let i = 0; i < component.properties.length; i++) {
      const prop = component.properties[i];
      const comma = i < component.properties.length - 1 ? ',' : '';
      lines.push(`  ${prop.name}: ${prop.type}${comma}`);
    }
    lines.push(`): ${component.name}Result {`);
    lines.push('  // TODO: Add validation');
    lines.push('  return {');
    lines.push('    success: true,');
    lines.push(`    value: { ${component.properties.map(p => p.name).join(', ')} },`);
    lines.push('  };');
    lines.push('}');

    return {
      path: `${fileName}.ts`,
      content: lines.join('\n'),
      requirementIds: component.requirementIds,
      designElementIds: component.designElementIds,
      fileType: 'entity',
    };
  }

  /**
   * Generate value object test code
   */
  private generateValueObjectTestCode(component: C4Component): GeneratedFile {
    const fileName = this.toKebabCase(component.name);
    const framework = this.config.testFramework;
    const lines: string[] = [];

    lines.push(`import { describe, it, expect } from '${framework}';`);
    lines.push(`import { create${component.name} } from './${fileName}.js';`);
    lines.push('');
    lines.push(`describe('${component.name}', () => {`);
    lines.push(`  describe('create${component.name}', () => {`);
    lines.push('    it(\'should create valid value object\', () => {');
    lines.push(`      const result = create${component.name}(`);
    for (let i = 0; i < component.properties.length; i++) {
      const prop = component.properties[i];
      const value = this.getTestValue(prop.type, prop.name);
      const comma = i < component.properties.length - 1 ? ',' : '';
      lines.push(`        ${value}${comma}`);
    }
    lines.push('      );');
    lines.push('      expect(result.success).toBe(true);');
    lines.push('    });');
    lines.push('  });');
    lines.push('});');

    return {
      path: `${fileName}.test.ts`,
      content: lines.join('\n'),
      requirementIds: component.requirementIds,
      designElementIds: component.designElementIds,
      fileType: 'test',
    };
  }

  /**
   * Generate factory code
   */
  private generateFactoryCode(component: C4Component): GeneratedFile {
    const fileName = this.toKebabCase(component.name);
    const lines: string[] = [];

    lines.push('/**');
    lines.push(` * ${component.name}`);
    lines.push(' *');
    for (const reqId of component.requirementIds) {
      lines.push(` * @see ${reqId}`);
    }
    lines.push(' */');
    lines.push('');
    lines.push(`export class ${component.name} {`);
    lines.push('  // TODO: Implement factory methods');
    lines.push('}');

    return {
      path: `${fileName}.ts`,
      content: lines.join('\n'),
      requirementIds: component.requirementIds,
      designElementIds: component.designElementIds,
      fileType: 'entity',
    };
  }

  /**
   * Generate test file from EARS requirements
   */
  private generateTestFile(subject: string, requirements: EARSRequirement[]): GeneratedFile {
    const fileName = this.toKebabCase(subject);
    const framework = this.config.testFramework;
    const lines: string[] = [];

    lines.push(`import { describe, it, expect } from '${framework}';`);
    lines.push('');
    lines.push(`describe('${subject}', () => {`);

    for (const req of requirements) {
      lines.push('');
      lines.push(`  // ${req.id}: ${req.text}`);
      
      const testName = this.generateTestName(req);
      lines.push(`  it('${testName}', () => {`);
      lines.push('    // TODO: Implement test');
      lines.push(`    // ${req.type.toUpperCase()}: ${req.trigger ? `${req.trigger} -> ` : ''}${req.requirement}`);
      lines.push('    expect(true).toBe(true); // Placeholder');
      lines.push('  });');
    }

    lines.push('});');

    return {
      path: `${fileName}.test.ts`,
      content: lines.join('\n'),
      requirementIds: requirements.map(r => r.id),
      designElementIds: [],
      fileType: 'test',
    };
  }

  /**
   * Generate test name from EARS requirement
   */
  private generateTestName(req: EARSRequirement): string {
    switch (req.type) {
      case 'event-driven':
        return `should ${req.requirement.toLowerCase()} when ${req.trigger?.toLowerCase()}`;
      case 'state-driven':
        return `should ${req.requirement.toLowerCase()} while ${req.trigger?.toLowerCase()}`;
      case 'optional':
        return `should ${req.requirement.toLowerCase()} if ${req.trigger?.toLowerCase()}`;
      case 'unwanted':
        return `should not ${req.requirement.replace(/^NOT\s+/i, '').toLowerCase()}`;
      default:
        return `should ${req.requirement.toLowerCase()}`;
    }
  }

  // ============================================================
  // Internal: File Writing
  // ============================================================

  /**
   * Write generated files to disk
   */
  private async writeFiles(files: GeneratedFile[], result: GenerationResult): Promise<void> {
    for (const file of files) {
      const fullPath = path.join(this.config.outputDir, file.path);
      const dir = path.dirname(fullPath);

      // Create directory if needed
      if (!fs.existsSync(dir)) {
        fs.mkdirSync(dir, { recursive: true });
      }

      // Check if file exists
      if (fs.existsSync(fullPath) && !this.config.overwrite) {
        result.warnings.push(`File already exists: ${fullPath}`);
        continue;
      }

      // Write file
      fs.writeFileSync(fullPath, file.content, 'utf-8');
    }
  }

  // ============================================================
  // Internal: Utilities
  // ============================================================

  /**
   * Convert to kebab-case
   */
  private toKebabCase(str: string): string {
    return str
      .replace(/([a-z])([A-Z])/g, '$1-$2')
      .replace(/[\s_]+/g, '-')
      .toLowerCase();
  }

  /**
   * Convert to camelCase
   */
  private toCamelCase(str: string): string {
    return str.charAt(0).toLowerCase() + str.slice(1);
  }

  /**
   * Get test value for type
   */
  private getTestValue(type: string, name: string): string {
    const lowerType = type.toLowerCase();
    if (lowerType === 'string') return `'test-${name}'`;
    if (lowerType === 'number') return '100';
    if (lowerType === 'boolean') return 'true';
    if (lowerType === 'date') return 'new Date()';
    if (lowerType.includes('[]')) return '[]';
    return '{}';
  }

  /**
   * Get minimal input for entity
   */
  private getMinimalInput(component: C4Component): string {
    const parts: string[] = [];
    for (const prop of component.properties) {
      if (prop.name !== 'id' && prop.name !== 'createdAt' && prop.name !== 'updatedAt') {
        const value = this.getTestValue(prop.type, prop.name);
        parts.push(`${prop.name}: ${value}`);
      }
    }
    return parts.join(', ');
  }
}

/**
 * Factory function to create EnhancedCodeGenerator
 */
export function createEnhancedCodeGenerator(
  config: Partial<CodeGenConfig>
): EnhancedCodeGenerator {
  return new EnhancedCodeGenerator(config);
}
