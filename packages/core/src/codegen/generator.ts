/**
 * Code Generator
 * 
 * Generates code from design specifications
 * 
 * @packageDocumentation
 * @module codegen/generator
 * 
 * @see REQ-COD-001 - Code Generation
 * @see Article V - Code Generation Standards
 */

/**
 * Supported programming languages
 */
export type TargetLanguage =
  | 'typescript'
  | 'javascript'
  | 'python'
  | 'java'
  | 'csharp'
  | 'go'
  | 'rust';

/**
 * Code generation template type
 */
export type TemplateType =
  | 'class'
  | 'interface'
  | 'function'
  | 'module'
  | 'test'
  | 'api-endpoint'
  | 'model'
  | 'repository'
  | 'service'
  | 'controller'
  | 'value-object'
  | 'entity';

/**
 * Code structure definition
 */
export interface CodeStructureDefinition {
  /** Structure name */
  name: string;
  /** Template type */
  type: TemplateType;
  /** Description */
  description?: string;
  /** Properties/fields */
  properties?: PropertyDefinition[];
  /** Methods */
  methods?: MethodDefinition[];
  /** Dependencies/imports */
  dependencies?: DependencyDefinition[];
  /** Decorators/annotations */
  decorators?: DecoratorDefinition[];
  /** Extends/implements */
  inheritance?: InheritanceDefinition;
  /** Metadata */
  metadata?: Record<string, unknown>;
}

/**
 * Property definition
 */
export interface PropertyDefinition {
  /** Property name */
  name: string;
  /** Type */
  type: string;
  /** Optional */
  optional?: boolean;
  /** Default value */
  defaultValue?: string;
  /** Visibility */
  visibility?: 'public' | 'private' | 'protected';
  /** Read-only */
  readonly?: boolean;
  /** Documentation */
  description?: string;
  /** Decorators */
  decorators?: DecoratorDefinition[];
}

/**
 * Method definition
 */
export interface MethodDefinition {
  /** Method name */
  name: string;
  /** Parameters */
  parameters?: ParameterDefinition[];
  /** Return type */
  returnType?: string;
  /** Visibility */
  visibility?: 'public' | 'private' | 'protected';
  /** Async */
  async?: boolean;
  /** Static */
  static?: boolean;
  /** Documentation */
  description?: string;
  /** Implementation hint */
  implementation?: string;
  /** Decorators */
  decorators?: DecoratorDefinition[];
}

/**
 * Parameter definition
 */
export interface ParameterDefinition {
  /** Parameter name */
  name: string;
  /** Type */
  type: string;
  /** Optional */
  optional?: boolean;
  /** Default value */
  defaultValue?: string;
  /** Description */
  description?: string;
}

/**
 * Dependency definition
 */
export interface DependencyDefinition {
  /** Module/package name */
  module: string;
  /** Imports */
  imports: string[];
  /** Type import only */
  typeOnly?: boolean;
}

/**
 * Decorator definition
 */
export interface DecoratorDefinition {
  /** Decorator name */
  name: string;
  /** Arguments */
  arguments?: string[];
}

/**
 * Inheritance definition
 */
export interface InheritanceDefinition {
  /** Extends class */
  extends?: string;
  /** Implements interfaces */
  implements?: string[];
}

/**
 * Generated code result
 */
export interface GeneratedCode {
  /** Generated code */
  code: string;
  /** Language */
  language: TargetLanguage;
  /** Suggested file name */
  fileName: string;
  /** Imports required */
  imports: string[];
  /** Dependencies required */
  dependencies: string[];
  /** Warnings */
  warnings: string[];
}

/**
 * Code generation options
 */
export interface CodeGeneratorOptions {
  /** Target language */
  language: TargetLanguage;
  /** Use strict mode */
  strictMode: boolean;
  /** Generate documentation */
  generateDocs: boolean;
  /** Indentation */
  indent: string;
  /** Line ending */
  lineEnding: '\n' | '\r\n';
  /** Max line length */
  maxLineLength: number;
  /** Style guide */
  styleGuide?: 'google' | 'airbnb' | 'standard';
}

/**
 * Default options
 */
export const DEFAULT_GENERATOR_OPTIONS: CodeGeneratorOptions = {
  language: 'typescript',
  strictMode: true,
  generateDocs: true,
  indent: '  ',
  lineEnding: '\n',
  maxLineLength: 100,
  styleGuide: 'standard',
};

/**
 * Language-specific configuration
 */
interface LanguageConfig {
  fileExtension: string;
  typePrefix: string;
  typeSuffix: string;
  visibility: Record<string, string>;
  nullableSymbol: string;
  asyncKeyword: string;
  classKeyword: string;
  interfaceKeyword: string;
  importStyle: 'es6' | 'commonjs' | 'python' | 'java' | 'csharp' | 'go' | 'rust';
}

/**
 * Language configurations
 */
const LANGUAGE_CONFIGS: Record<TargetLanguage, LanguageConfig> = {
  typescript: {
    fileExtension: '.ts',
    typePrefix: '',
    typeSuffix: '',
    visibility: { public: 'public', private: 'private', protected: 'protected' },
    nullableSymbol: '?',
    asyncKeyword: 'async',
    classKeyword: 'class',
    interfaceKeyword: 'interface',
    importStyle: 'es6',
  },
  javascript: {
    fileExtension: '.js',
    typePrefix: '',
    typeSuffix: '',
    visibility: { public: '', private: '#', protected: '' },
    nullableSymbol: '',
    asyncKeyword: 'async',
    classKeyword: 'class',
    interfaceKeyword: '',
    importStyle: 'es6',
  },
  python: {
    fileExtension: '.py',
    typePrefix: '',
    typeSuffix: '',
    visibility: { public: '', private: '_', protected: '_' },
    nullableSymbol: ' | None',
    asyncKeyword: 'async',
    classKeyword: 'class',
    interfaceKeyword: '',
    importStyle: 'python',
  },
  java: {
    fileExtension: '.java',
    typePrefix: '',
    typeSuffix: '',
    visibility: { public: 'public', private: 'private', protected: 'protected' },
    nullableSymbol: '',
    asyncKeyword: '',
    classKeyword: 'class',
    interfaceKeyword: 'interface',
    importStyle: 'java',
  },
  csharp: {
    fileExtension: '.cs',
    typePrefix: '',
    typeSuffix: '',
    visibility: { public: 'public', private: 'private', protected: 'protected' },
    nullableSymbol: '?',
    asyncKeyword: 'async',
    classKeyword: 'class',
    interfaceKeyword: 'interface',
    importStyle: 'csharp',
  },
  go: {
    fileExtension: '.go',
    typePrefix: '',
    typeSuffix: '',
    visibility: { public: '', private: '', protected: '' },
    nullableSymbol: '*',
    asyncKeyword: '',
    classKeyword: 'type',
    interfaceKeyword: 'type',
    importStyle: 'go',
  },
  rust: {
    fileExtension: '.rs',
    typePrefix: '',
    typeSuffix: '',
    visibility: { public: 'pub', private: '', protected: 'pub(crate)' },
    nullableSymbol: 'Option<>',
    asyncKeyword: 'async',
    classKeyword: 'struct',
    interfaceKeyword: 'trait',
    importStyle: 'rust',
  },
};

/**
 * Code Generator
 */
export class CodeGenerator {
  private options: CodeGeneratorOptions;
  private langConfig: LanguageConfig;

  constructor(options?: Partial<CodeGeneratorOptions>) {
    this.options = { ...DEFAULT_GENERATOR_OPTIONS, ...options };
    this.langConfig = LANGUAGE_CONFIGS[this.options.language];
  }

  /**
   * Generate code from structure definition
   */
  generate(definition: CodeStructureDefinition): GeneratedCode {
    const warnings: string[] = [];
    let code = '';

    // Generate imports
    const imports = this.generateImports(definition.dependencies ?? []);
    if (imports) {
      code += imports + this.options.lineEnding + this.options.lineEnding;
    }

    // Generate documentation
    if (this.options.generateDocs && definition.description) {
      code += this.generateDocumentation(definition.description);
    }

    // Generate decorators
    if (definition.decorators) {
      code += this.generateDecorators(definition.decorators);
    }

    // Generate structure based on type
    switch (definition.type) {
      case 'class':
      case 'service':
      case 'controller':
      case 'repository':
        code += this.generateClass(definition);
        break;
      case 'interface':
        code += this.generateInterface(definition);
        break;
      case 'function':
        code += this.generateFunction(definition);
        break;
      case 'module':
        code += this.generateModule(definition);
        break;
      case 'model':
        code += this.generateModel(definition);
        break;
      case 'api-endpoint':
        code += this.generateApiEndpoint(definition);
        break;
      case 'value-object':
        code += this.generateValueObject(definition);
        break;
      case 'entity':
        code += this.generateEntity(definition);
        break;
      default:
        warnings.push(`Unknown template type: ${definition.type}`);
        code += this.generateClass(definition);
    }

    return {
      code,
      language: this.options.language,
      fileName: this.generateFileName(definition.name),
      imports: this.extractImportModules(definition.dependencies ?? []),
      dependencies: this.extractDependencies(definition.dependencies ?? []),
      warnings,
    };
  }

  /**
   * Generate multiple structures
   */
  generateBatch(definitions: CodeStructureDefinition[]): GeneratedCode[] {
    return definitions.map((def) => this.generate(def));
  }

  /**
   * Generate imports
   */
  private generateImports(dependencies: DependencyDefinition[]): string {
    if (dependencies.length === 0) return '';

    const lines: string[] = [];

    for (const dep of dependencies) {
      lines.push(this.formatImport(dep));
    }

    return lines.join(this.options.lineEnding);
  }

  /**
   * Format single import
   */
  private formatImport(dep: DependencyDefinition): string {
    const { language } = this.options;
    const imports = dep.imports.join(', ');

    switch (language) {
      case 'typescript':
      case 'javascript':
        if (dep.typeOnly && language === 'typescript') {
          return `import type { ${imports} } from '${dep.module}';`;
        }
        return `import { ${imports} } from '${dep.module}';`;
      case 'python':
        return `from ${dep.module} import ${imports}`;
      case 'java':
        return dep.imports.map((i) => `import ${dep.module}.${i};`).join('\n');
      case 'csharp':
        return `using ${dep.module};`;
      case 'go':
        return `import "${dep.module}"`;
      case 'rust':
        return `use ${dep.module}::{${imports}};`;
      default:
        return `import { ${imports} } from '${dep.module}';`;
    }
  }

  /**
   * Generate documentation comment
   */
  private generateDocumentation(description: string, params?: ParameterDefinition[]): string {
    const { language, indent } = this.options;
    const lines: string[] = [];

    switch (language) {
      case 'typescript':
      case 'javascript':
      case 'java':
      case 'csharp':
        lines.push('/**');
        lines.push(` * ${description}`);
        if (params) {
          lines.push(' *');
          for (const p of params) {
            lines.push(` * @param ${p.name} ${p.description ?? p.type}`);
          }
        }
        lines.push(' */');
        break;
      case 'python':
        lines.push('"""');
        lines.push(description);
        if (params) {
          lines.push('');
          lines.push('Args:');
          for (const p of params) {
            lines.push(`${indent}${p.name}: ${p.description ?? p.type}`);
          }
        }
        lines.push('"""');
        break;
      case 'go':
        lines.push(`// ${description}`);
        break;
      case 'rust':
        lines.push(`/// ${description}`);
        break;
    }

    return lines.join(this.options.lineEnding) + this.options.lineEnding;
  }

  /**
   * Generate decorators
   */
  private generateDecorators(decorators: DecoratorDefinition[]): string {
    const { language } = this.options;
    const lines: string[] = [];

    for (const dec of decorators) {
      switch (language) {
        case 'typescript':
        case 'javascript':
          if (dec.arguments?.length) {
            lines.push(`@${dec.name}(${dec.arguments.join(', ')})`);
          } else {
            lines.push(`@${dec.name}()`);
          }
          break;
        case 'python':
          if (dec.arguments?.length) {
            lines.push(`@${dec.name}(${dec.arguments.join(', ')})`);
          } else {
            lines.push(`@${dec.name}`);
          }
          break;
        case 'java':
          if (dec.arguments?.length) {
            lines.push(`@${dec.name}(${dec.arguments.join(', ')})`);
          } else {
            lines.push(`@${dec.name}`);
          }
          break;
        case 'csharp':
          if (dec.arguments?.length) {
            lines.push(`[${dec.name}(${dec.arguments.join(', ')})]`);
          } else {
            lines.push(`[${dec.name}]`);
          }
          break;
        default:
          // Go and Rust don't have decorators
          break;
      }
    }

    return lines.length > 0
      ? lines.join(this.options.lineEnding) + this.options.lineEnding
      : '';
  }

  /**
   * Generate class
   */
  private generateClass(definition: CodeStructureDefinition): string {
    const { language, indent } = this.options;
    const lines: string[] = [];

    // Class declaration
    const inheritance = this.formatInheritance(definition.inheritance);

    switch (language) {
      case 'typescript':
      case 'javascript':
        lines.push(`export ${this.langConfig.classKeyword} ${definition.name}${inheritance} {`);
        break;
      case 'python':
        lines.push(`class ${definition.name}${inheritance}:`);
        break;
      case 'java':
      case 'csharp':
        lines.push(`public ${this.langConfig.classKeyword} ${definition.name}${inheritance} {`);
        break;
      case 'go':
        lines.push(`type ${definition.name} struct {`);
        break;
      case 'rust':
        lines.push(`pub struct ${definition.name} {`);
        break;
    }

    // Properties
    if (definition.properties) {
      for (const prop of definition.properties) {
        lines.push(this.generateProperty(prop));
      }
      if (definition.methods?.length) {
        lines.push('');
      }
    }

    // Constructor (for some languages)
    if (language === 'python' && definition.properties?.length) {
      lines.push(this.generatePythonInit(definition.properties));
    }

    // Methods
    if (definition.methods) {
      for (const method of definition.methods) {
        lines.push(this.generateMethod(method));
      }
    }

    // Close class
    switch (language) {
      case 'python':
        if (!definition.properties?.length && !definition.methods?.length) {
          lines.push(`${indent}pass`);
        }
        break;
      default:
        lines.push('}');
    }

    return lines.join(this.options.lineEnding);
  }

  /**
   * Generate interface
   */
  private generateInterface(definition: CodeStructureDefinition): string {
    const { language, indent } = this.options;
    const lines: string[] = [];

    switch (language) {
      case 'typescript':
        lines.push(`export interface ${definition.name} {`);
        for (const prop of definition.properties ?? []) {
          const optional = prop.optional ? '?' : '';
          lines.push(`${indent}${prop.name}${optional}: ${prop.type};`);
        }
        for (const method of definition.methods ?? []) {
          const params = this.formatParameters(method.parameters ?? []);
          lines.push(`${indent}${method.name}(${params}): ${method.returnType ?? 'void'};`);
        }
        lines.push('}');
        break;
      case 'java':
        lines.push(`public interface ${definition.name} {`);
        for (const method of definition.methods ?? []) {
          const params = this.formatParameters(method.parameters ?? []);
          lines.push(`${indent}${method.returnType ?? 'void'} ${method.name}(${params});`);
        }
        lines.push('}');
        break;
      case 'go':
        lines.push(`type ${definition.name} interface {`);
        for (const method of definition.methods ?? []) {
          const params = this.formatParameters(method.parameters ?? []);
          lines.push(`${indent}${method.name}(${params}) ${method.returnType ?? ''}`);
        }
        lines.push('}');
        break;
      case 'rust':
        lines.push(`pub trait ${definition.name} {`);
        for (const method of definition.methods ?? []) {
          const params = this.formatParameters(method.parameters ?? []);
          const ret = method.returnType ? ` -> ${method.returnType}` : '';
          lines.push(`${indent}fn ${method.name}(&self, ${params})${ret};`);
        }
        lines.push('}');
        break;
      default:
        // Python, JavaScript, C# - use abstract class or type alias
        return this.generateClass({ ...definition, type: 'class' });
    }

    return lines.join(this.options.lineEnding);
  }

  /**
   * Generate function
   */
  private generateFunction(definition: CodeStructureDefinition): string {
    const { language, indent } = this.options;
    const method = definition.methods?.[0];
    if (!method) return '';

    const lines: string[] = [];
    const params = this.formatParameters(method.parameters ?? []);
    const async = method.async ? this.langConfig.asyncKeyword + ' ' : '';

    switch (language) {
      case 'typescript':
        lines.push(`export ${async}function ${method.name}(${params}): ${method.returnType ?? 'void'} {`);
        lines.push(`${indent}// TODO: Implement`);
        lines.push(`${indent}throw new Error('Not implemented');`);
        lines.push('}');
        break;
      case 'javascript':
        lines.push(`export ${async}function ${method.name}(${params}) {`);
        lines.push(`${indent}// TODO: Implement`);
        lines.push(`${indent}throw new Error('Not implemented');`);
        lines.push('}');
        break;
      case 'python':
        const retType = method.returnType ? ` -> ${method.returnType}` : '';
        lines.push(`${async}def ${method.name}(${params})${retType}:`);
        lines.push(`${indent}# TODO: Implement`);
        lines.push(`${indent}raise NotImplementedError()`);
        break;
      case 'go':
        lines.push(`func ${method.name}(${params}) ${method.returnType ?? ''} {`);
        lines.push(`${indent}// TODO: Implement`);
        lines.push(`${indent}panic("not implemented")`);
        lines.push('}');
        break;
      case 'rust':
        const ret = method.returnType ? ` -> ${method.returnType}` : '';
        lines.push(`pub ${async}fn ${method.name}(${params})${ret} {`);
        lines.push(`${indent}// TODO: Implement`);
        lines.push(`${indent}todo!()`);
        lines.push('}');
        break;
      default:
        lines.push(`// Function: ${method.name}`);
    }

    return lines.join(this.options.lineEnding);
  }

  /**
   * Generate module
   */
  private generateModule(definition: CodeStructureDefinition): string {
    const { language } = this.options;
    const lines: string[] = [];

    // Generate exports for all properties and methods
    switch (language) {
      case 'typescript':
      case 'javascript':
        for (const prop of definition.properties ?? []) {
          lines.push(`export const ${prop.name}: ${prop.type} = ${prop.defaultValue ?? 'undefined'};`);
        }
        for (const method of definition.methods ?? []) {
          const funcDef: CodeStructureDefinition = {
            name: method.name,
            type: 'function',
            methods: [method],
          };
          lines.push(this.generateFunction(funcDef));
        }
        break;
      default:
        lines.push(this.generateClass(definition));
    }

    return lines.join(this.options.lineEnding + this.options.lineEnding);
  }

  /**
   * Generate model
   */
  private generateModel(definition: CodeStructureDefinition): string {
    // Models are typically data classes
    return this.generateClass(definition);
  }

  /**
   * Generate API endpoint
   */
  private generateApiEndpoint(definition: CodeStructureDefinition): string {
    const { language, indent } = this.options;
    const lines: string[] = [];

    switch (language) {
      case 'typescript':
        lines.push(`export class ${definition.name}Controller {`);
        for (const method of definition.methods ?? []) {
          const route = method.decorators?.find((d) => 
            ['Get', 'Post', 'Put', 'Delete', 'Patch'].includes(d.name)
          );
          if (route) {
            lines.push(`${indent}@${route.name}(${route.arguments?.map((a) => `'${a}'`).join(', ') ?? ''})`);
          }
          const params = this.formatParameters(method.parameters ?? []);
          lines.push(`${indent}async ${method.name}(${params}): Promise<${method.returnType ?? 'void'}> {`);
          lines.push(`${indent}${indent}// TODO: Implement`);
          lines.push(`${indent}${indent}throw new Error('Not implemented');`);
          lines.push(`${indent}}`);
          lines.push('');
        }
        lines.push('}');
        break;
      default:
        return this.generateClass(definition);
    }

    return lines.join(this.options.lineEnding);
  }

  /**
   * Generate property
   */
  private generateProperty(prop: PropertyDefinition): string {
    const { language, indent } = this.options;
    const visibility = this.formatVisibility(prop.visibility ?? 'public');
    const readonly = prop.readonly ? 'readonly ' : '';

    switch (language) {
      case 'typescript':
        const optional = prop.optional ? '?' : '';
        const defaultVal = prop.defaultValue ? ` = ${prop.defaultValue}` : '';
        return `${indent}${visibility}${readonly}${prop.name}${optional}: ${prop.type}${defaultVal};`;
      case 'javascript':
        const prefix = prop.visibility === 'private' ? '#' : '';
        return `${indent}${prefix}${prop.name} = ${prop.defaultValue ?? 'undefined'};`;
      case 'python':
        return `${indent}${prop.name}: ${prop.type}`;
      case 'java':
        return `${indent}${visibility}${prop.type} ${prop.name};`;
      case 'csharp':
        return `${indent}${visibility}${prop.type} ${prop.name} { get; set; }`;
      case 'go':
        const goVisibility = prop.visibility === 'public' 
          ? prop.name.charAt(0).toUpperCase() + prop.name.slice(1)
          : prop.name;
        return `${indent}${goVisibility} ${prop.type}`;
      case 'rust':
        const rustVis = prop.visibility === 'public' ? 'pub ' : '';
        return `${indent}${rustVis}${prop.name}: ${prop.type},`;
      default:
        return `${indent}${prop.name}: ${prop.type}`;
    }
  }

  /**
   * Generate method
   */
  private generateMethod(method: MethodDefinition): string {
    const { language, indent } = this.options;
    const lines: string[] = [];
    const visibility = this.formatVisibility(method.visibility ?? 'public');
    const params = this.formatParameters(method.parameters ?? []);
    const async = method.async ? this.langConfig.asyncKeyword + ' ' : '';
    const staticMod = method.static ? 'static ' : '';

    // Documentation
    if (this.options.generateDocs && method.description) {
      const doc = this.generateDocumentation(method.description, method.parameters);
      lines.push(doc.split('\n').map((l) => indent + l).join('\n'));
    }

    // Decorators
    if (method.decorators) {
      const decs = this.generateDecorators(method.decorators);
      lines.push(decs.split('\n').map((l) => indent + l).join('\n'));
    }

    switch (language) {
      case 'typescript':
        lines.push(`${indent}${visibility}${staticMod}${async}${method.name}(${params}): ${method.returnType ?? 'void'} {`);
        lines.push(`${indent}${indent}// TODO: Implement`);
        if (method.implementation) {
          lines.push(`${indent}${indent}${method.implementation}`);
        } else {
          lines.push(`${indent}${indent}throw new Error('Not implemented');`);
        }
        lines.push(`${indent}}`);
        break;
      case 'javascript':
        lines.push(`${indent}${staticMod}${async}${method.name}(${params}) {`);
        lines.push(`${indent}${indent}// TODO: Implement`);
        lines.push(`${indent}${indent}throw new Error('Not implemented');`);
        lines.push(`${indent}}`);
        break;
      case 'python':
        const pyStatic = method.static ? '@staticmethod\n' : '';
        const retType = method.returnType ? ` -> ${method.returnType}` : '';
        const selfParam = method.static ? '' : 'self, ';
        lines.push(`${indent}${pyStatic}${indent}${async}def ${method.name}(${selfParam}${params})${retType}:`);
        lines.push(`${indent}${indent}# TODO: Implement`);
        lines.push(`${indent}${indent}raise NotImplementedError()`);
        break;
      case 'java':
        lines.push(`${indent}${visibility}${staticMod}${method.returnType ?? 'void'} ${method.name}(${params}) {`);
        lines.push(`${indent}${indent}// TODO: Implement`);
        lines.push(`${indent}${indent}throw new UnsupportedOperationException();`);
        lines.push(`${indent}}`);
        break;
      case 'csharp':
        lines.push(`${indent}${visibility}${staticMod}${async}${method.returnType ?? 'void'} ${method.name}(${params}) {`);
        lines.push(`${indent}${indent}// TODO: Implement`);
        lines.push(`${indent}${indent}throw new NotImplementedException();`);
        lines.push(`${indent}}`);
        break;
      case 'go':
        lines.push(`func (r *${method.name}) ${method.name}(${params}) ${method.returnType ?? ''} {`);
        lines.push(`${indent}// TODO: Implement`);
        lines.push(`${indent}panic("not implemented")`);
        lines.push('}');
        break;
      case 'rust':
        const ret = method.returnType ? ` -> ${method.returnType}` : '';
        lines.push(`${indent}pub ${async}fn ${method.name}(&self, ${params})${ret} {`);
        lines.push(`${indent}${indent}// TODO: Implement`);
        lines.push(`${indent}${indent}todo!()`);
        lines.push(`${indent}}`);
        break;
    }

    return lines.join(this.options.lineEnding);
  }

  /**
   * Generate Python __init__ method
   */
  private generatePythonInit(properties: PropertyDefinition[]): string {
    const { indent } = this.options;
    const lines: string[] = [];
    
    const params = properties.map((p) => {
      const optional = p.optional ? ` = ${p.defaultValue ?? 'None'}` : '';
      return `${p.name}: ${p.type}${optional}`;
    }).join(', ');

    lines.push(`${indent}def __init__(self, ${params}):`);
    for (const prop of properties) {
      lines.push(`${indent}${indent}self.${prop.name} = ${prop.name}`);
    }

    return lines.join(this.options.lineEnding) + this.options.lineEnding;
  }

  /**
   * Format inheritance
   */
  private formatInheritance(inheritance?: InheritanceDefinition): string {
    if (!inheritance) return '';

    const { language } = this.options;
    const parts: string[] = [];

    switch (language) {
      case 'typescript':
      case 'javascript':
        if (inheritance.extends) parts.push(`extends ${inheritance.extends}`);
        if (inheritance.implements?.length) {
          parts.push(`implements ${inheritance.implements.join(', ')}`);
        }
        return parts.length > 0 ? ' ' + parts.join(' ') : '';
      case 'python':
        const bases = [
          inheritance.extends,
          ...(inheritance.implements ?? []),
        ].filter(Boolean);
        return bases.length > 0 ? `(${bases.join(', ')})` : '';
      case 'java':
      case 'csharp':
        if (inheritance.extends) parts.push(`extends ${inheritance.extends}`);
        if (inheritance.implements?.length) {
          parts.push(`implements ${inheritance.implements.join(', ')}`);
        }
        return parts.length > 0 ? ' ' + parts.join(' ') : '';
      default:
        return '';
    }
  }

  /**
   * Format visibility
   */
  private formatVisibility(visibility: string): string {
    const vis = this.langConfig.visibility[visibility] ?? '';
    return vis ? vis + ' ' : '';
  }

  /**
   * Format parameters
   */
  private formatParameters(parameters: ParameterDefinition[]): string {
    const { language } = this.options;

    return parameters.map((p) => {
      const optional = p.optional ? '?' : '';
      const defaultVal = p.defaultValue ? ` = ${p.defaultValue}` : '';

      switch (language) {
        case 'typescript':
          return `${p.name}${optional}: ${p.type}${defaultVal}`;
        case 'javascript':
          return `${p.name}${defaultVal}`;
        case 'python':
          return `${p.name}: ${p.type}${defaultVal}`;
        case 'java':
        case 'csharp':
          return `${p.type} ${p.name}`;
        case 'go':
          return `${p.name} ${p.type}`;
        case 'rust':
          return `${p.name}: ${p.type}`;
        default:
          return `${p.name}: ${p.type}`;
      }
    }).join(', ');
  }

  /**
   * Generate file name
   */
  private generateFileName(name: string): string {
    const { language } = this.options;
    const ext = this.langConfig.fileExtension;

    // Convert to appropriate case
    switch (language) {
      case 'typescript':
      case 'javascript':
        return this.toKebabCase(name) + ext;
      case 'python':
        return this.toSnakeCase(name) + ext;
      case 'java':
      case 'csharp':
        return name + ext;
      case 'go':
        return this.toSnakeCase(name) + ext;
      case 'rust':
        return this.toSnakeCase(name) + ext;
      default:
        return name + ext;
    }
  }

  /**
   * Extract import modules
   */
  private extractImportModules(dependencies: DependencyDefinition[]): string[] {
    return dependencies.map((d) => d.module);
  }

  /**
   * Extract dependencies (external packages)
   */
  private extractDependencies(dependencies: DependencyDefinition[]): string[] {
    return dependencies
      .filter((d) => !d.module.startsWith('.') && !d.module.startsWith('/'))
      .map((d) => d.module.split('/')[0]);
  }

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
   * Convert to snake_case
   */
  private toSnakeCase(str: string): string {
    return str
      .replace(/([a-z])([A-Z])/g, '$1_$2')
      .replace(/[\s-]+/g, '_')
      .toLowerCase();
  }

  /**
   * Generate Value Object with function-based pattern (BP-CODE-004)
   * 
   * Uses interface + factory function pattern instead of classes
   * for better TypeScript structural typing compatibility.
   */
  private generateValueObject(definition: CodeStructureDefinition): string {
    const { indent, lineEnding } = this.options;
    const lines: string[] = [];

    // Interface definition
    lines.push(`export interface ${definition.name} {`);
    for (const prop of definition.properties ?? []) {
      const readonly = prop.readonly !== false ? 'readonly ' : '';
      lines.push(`${indent}${readonly}${prop.name}: ${prop.type};`);
    }
    lines.push('}');
    lines.push('');

    // Factory function with Result type (BP-CODE-005)
    const inputParams = (definition.properties ?? [])
      .map((p) => `${p.name}: ${p.type}`)
      .join(', ');
    
    lines.push(`/**`);
    lines.push(` * Create a ${definition.name} with validation`);
    lines.push(` * @returns Result<${definition.name}, ValidationError>`);
    lines.push(` */`);
    lines.push(`export function create${definition.name}(${inputParams}): Result<${definition.name}, ValidationError> {`);
    lines.push(`${indent}// TODO: Add validation logic`);
    lines.push(`${indent}return ok({`);
    for (const prop of definition.properties ?? []) {
      lines.push(`${indent}${indent}${prop.name},`);
    }
    lines.push(`${indent}});`);
    lines.push('}');
    lines.push('');

    // Equality function
    lines.push(`/**`);
    lines.push(` * Check if two ${definition.name} values are equal`);
    lines.push(` */`);
    lines.push(`export function ${this.toCamelCase(definition.name)}Equals(a: ${definition.name}, b: ${definition.name}): boolean {`);
    const propComparisons = (definition.properties ?? [])
      .map((p) => `a.${p.name} === b.${p.name}`)
      .join(' && ');
    lines.push(`${indent}return ${propComparisons || 'true'};`);
    lines.push('}');

    return lines.join(lineEnding);
  }

  /**
   * Generate Entity with status transitions and counter reset (BP-DESIGN-001, BP-DESIGN-006)
   */
  private generateEntity(definition: CodeStructureDefinition): string {
    const { indent, lineEnding } = this.options;
    const lines: string[] = [];
    const entityName = definition.name;
    const lowerName = this.toCamelCase(entityName);

    // Counter for ID generation (BP-CODE-002)
    lines.push(`let ${lowerName}Counter = 0;`);
    lines.push('');

    // ID type
    lines.push(`export type ${entityName}Id = string & { readonly brand: unique symbol };`);
    lines.push('');

    // Status type (if has status property)
    const statusProp = (definition.properties ?? []).find((p) => p.name === 'status');
    if (statusProp) {
      lines.push(`export type ${entityName}Status = 'draft' | 'active' | 'completed' | 'cancelled';`);
      lines.push('');
      // Status Transition Map (BP-DESIGN-001)
      lines.push(`const valid${entityName}StatusTransitions: Record<${entityName}Status, ${entityName}Status[]> = {`);
      lines.push(`${indent}draft: ['active', 'cancelled'],`);
      lines.push(`${indent}active: ['completed', 'cancelled'],`);
      lines.push(`${indent}completed: [],`);
      lines.push(`${indent}cancelled: [],`);
      lines.push('};');
      lines.push('');
    }

    // Interface
    lines.push(`export interface ${entityName} {`);
    lines.push(`${indent}readonly id: ${entityName}Id;`);
    for (const prop of definition.properties ?? []) {
      if (prop.name === 'id') continue;
      const readonly = prop.readonly !== false ? 'readonly ' : '';
      lines.push(`${indent}${readonly}${prop.name}: ${prop.type};`);
    }
    lines.push(`${indent}readonly version: number;`);
    lines.push(`${indent}readonly createdAt: Date;`);
    lines.push(`${indent}readonly updatedAt: Date;`);
    lines.push('}');
    lines.push('');

    // Input DTO (BP-CODE-001)
    lines.push(`export interface Create${entityName}Input {`);
    for (const prop of definition.properties ?? []) {
      if (['id', 'status', 'version', 'createdAt', 'updatedAt'].includes(prop.name)) continue;
      lines.push(`${indent}${prop.name}: ${prop.type};`);
    }
    lines.push('}');
    lines.push('');

    // ID generator (BP-CODE-002)
    lines.push(`function generate${entityName}Id(): ${entityName}Id {`);
    lines.push(`${indent}const dateStr = new Date().toISOString().slice(0, 10).replace(/-/g, '');`);
    lines.push(`${indent}const seq = String(++${lowerName}Counter).padStart(3, '0');`);
    lines.push(`${indent}return \`${entityName.substring(0, 3).toUpperCase()}-\${dateStr}-\${seq}\` as ${entityName}Id;`);
    lines.push('}');
    lines.push('');

    // Counter reset function (BP-DESIGN-006)
    lines.push(`/**`);
    lines.push(` * Reset counter for testing (BP-DESIGN-006)`);
    lines.push(` */`);
    lines.push(`export function reset${entityName}Counter(): void {`);
    lines.push(`${indent}${lowerName}Counter = 0;`);
    lines.push('}');
    lines.push('');

    // Factory function
    lines.push(`/**`);
    lines.push(` * Create a new ${entityName}`);
    lines.push(` */`);
    lines.push(`export function create${entityName}(input: Create${entityName}Input): Result<${entityName}, ValidationError> {`);
    lines.push(`${indent}const now = new Date();`);
    lines.push(`${indent}// TODO: Add validation logic`);
    lines.push(`${indent}return ok({`);
    lines.push(`${indent}${indent}id: generate${entityName}Id(),`);
    for (const prop of definition.properties ?? []) {
      if (['id', 'version', 'createdAt', 'updatedAt'].includes(prop.name)) continue;
      if (prop.name === 'status') {
        lines.push(`${indent}${indent}status: 'draft' as ${entityName}Status,`);
      } else {
        lines.push(`${indent}${indent}${prop.name}: input.${prop.name},`);
      }
    }
    lines.push(`${indent}${indent}version: 1,`);
    lines.push(`${indent}${indent}createdAt: now,`);
    lines.push(`${indent}${indent}updatedAt: now,`);
    lines.push(`${indent}});`);
    lines.push('}');

    return lines.join(lineEnding);
  }

  /**
   * Convert to camelCase
   */
  private toCamelCase(str: string): string {
    return str.charAt(0).toLowerCase() + str.slice(1);
  }
}

/**
 * Create code generator instance
 */
export function createCodeGenerator(
  options?: Partial<CodeGeneratorOptions>
): CodeGenerator {
  return new CodeGenerator(options);
}
