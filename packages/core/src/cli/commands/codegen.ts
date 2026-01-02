/**
 * Codegen Command
 *
 * CLI commands for code generation and analysis
 *
 * @packageDocumentation
 * @module cli/commands/codegen
 *
 * @see REQ-CLI-003 - Codegen CLI
 * @see REQ-CG-001 - Code Generation
 * @see REQ-CG-002 - Static Analysis
 * @see DES-MUSUBIX-001 Section 16-C.3 - codegenコマンド設計
 * @see TSK-071〜073 - Codegen CLI実装
 */

import type { Command } from 'commander';
import { readFile, writeFile, mkdir, readdir, stat } from 'fs/promises';
import { resolve, dirname, extname, join } from 'path';
import { ExitCode, getGlobalOptions, outputResult } from '../base.js';

/**
 * Codegen command options
 */
export interface CodegenOptions {
  output?: string;
  language?: 'typescript' | 'javascript' | 'python';
  template?: string;
  verbose?: boolean;
}

/**
 * Generated code
 */
export interface GeneratedCode {
  filename: string;
  language: string;
  content: string;
  metadata: {
    requirements: string[];
    designElements: string[];
    patterns: string[];
  };
}

/**
 * Generation result
 */
export interface GenerationResult {
  success: boolean;
  files: GeneratedCode[];
  summary: {
    totalFiles: number;
    totalLines: number;
    languages: string[];
  };
  message: string;
}

/**
 * Analysis issue
 */
export interface AnalysisIssue {
  file: string;
  line?: number;
  column?: number;
  severity: 'error' | 'warning' | 'info';
  rule: string;
  message: string;
}

/**
 * Analysis result
 */
export interface AnalysisResult {
  success: boolean;
  issues: AnalysisIssue[];
  metrics: {
    files: number;
    lines: number;
    complexity: number;
    maintainabilityIndex: number;
  };
  summary: {
    errors: number;
    warnings: number;
    info: number;
  };
  message: string;
}

/**
 * Security vulnerability
 */
export interface SecurityVulnerability {
  severity: 'critical' | 'high' | 'medium' | 'low';
  type: string;
  file: string;
  line?: number;
  description: string;
  recommendation: string;
  cwe?: string;
}

/**
 * Security result
 */
export interface SecurityResult {
  success: boolean;
  vulnerabilities: SecurityVulnerability[];
  summary: {
    critical: number;
    high: number;
    medium: number;
    low: number;
  };
  score: number;
  message: string;
}

/**
 * Security patterns to check
 */
const SECURITY_PATTERNS = [
  {
    pattern: /eval\s*\(/g,
    type: 'Code Injection',
    severity: 'critical' as const,
    cwe: 'CWE-94',
    description: 'Use of eval() can lead to code injection vulnerabilities',
    recommendation: 'Avoid eval(). Use safer alternatives like JSON.parse() for data parsing.',
  },
  {
    pattern: /new\s+Function\s*\(/g,
    type: 'Code Injection',
    severity: 'high' as const,
    cwe: 'CWE-94',
    description: 'Dynamic function creation can lead to code injection',
    recommendation: 'Avoid dynamic function creation. Use predefined functions instead.',
  },
  {
    pattern: /innerHTML\s*=/g,
    type: 'XSS',
    severity: 'high' as const,
    cwe: 'CWE-79',
    description: 'Direct innerHTML assignment can lead to XSS vulnerabilities',
    recommendation: 'Use textContent or sanitize HTML before assignment.',
  },
  {
    pattern: /document\.write\s*\(/g,
    type: 'XSS',
    severity: 'high' as const,
    cwe: 'CWE-79',
    description: 'document.write can be exploited for XSS attacks',
    recommendation: 'Use DOM manipulation methods instead of document.write.',
  },
  {
    pattern: /password\s*[:=]\s*['"][^'"]+['"]/gi,
    type: 'Hardcoded Credentials',
    severity: 'critical' as const,
    cwe: 'CWE-798',
    description: 'Hardcoded passwords detected',
    recommendation: 'Use environment variables or secure credential stores.',
  },
  {
    pattern: /api[_-]?key\s*[:=]\s*['"][^'"]+['"]/gi,
    type: 'Hardcoded Credentials',
    severity: 'high' as const,
    cwe: 'CWE-798',
    description: 'Hardcoded API key detected',
    recommendation: 'Use environment variables for API keys.',
  },
  {
    pattern: /exec\s*\(/g,
    type: 'Command Injection',
    severity: 'high' as const,
    cwe: 'CWE-78',
    description: 'Use of exec() can lead to command injection',
    recommendation: 'Use execFile() or spawn() with explicit arguments.',
  },
  {
    pattern: /dangerouslySetInnerHTML/g,
    type: 'XSS',
    severity: 'medium' as const,
    cwe: 'CWE-79',
    description: 'React dangerouslySetInnerHTML can lead to XSS',
    recommendation: 'Sanitize HTML content before using dangerouslySetInnerHTML.',
  },
  {
    pattern: /\bhttp:\/\//g,
    type: 'Insecure Communication',
    severity: 'medium' as const,
    cwe: 'CWE-319',
    description: 'Use of HTTP instead of HTTPS',
    recommendation: 'Use HTTPS for all external communications.',
  },
  {
    pattern: /Math\.random\(\)/g,
    type: 'Weak Randomness',
    severity: 'low' as const,
    cwe: 'CWE-338',
    description: 'Math.random() is not cryptographically secure',
    recommendation: 'Use crypto.getRandomValues() for security-sensitive randomness.',
  },
];

/**
 * Code analysis rules
 */
const ANALYSIS_RULES = [
  {
    name: 'no-any',
    pattern: /:\s*any\b/g,
    severity: 'warning' as const,
    message: 'Avoid using "any" type. Use proper types for better type safety.',
  },
  {
    name: 'no-console',
    pattern: /console\.(log|warn|error|info|debug)\s*\(/g,
    severity: 'info' as const,
    message: 'Console statements should be removed in production code.',
  },
  {
    name: 'max-line-length',
    check: (line: string) => line.length > 120,
    severity: 'info' as const,
    message: 'Line exceeds 120 characters.',
  },
  {
    name: 'no-magic-numbers',
    pattern: /[^0-9a-z_]([2-9]|[1-9]\d+)(?=[^0-9]|$)/gi,
    severity: 'info' as const,
    message: 'Avoid magic numbers. Use named constants instead.',
  },
  {
    name: 'prefer-const',
    pattern: /\blet\s+\w+\s*=/g,
    severity: 'info' as const,
    message: 'Consider using const if variable is not reassigned.',
  },
];

/**
 * Register codegen command
 */
export function registerCodegenCommand(program: Command): void {
  const codegen = program
    .command('codegen')
    .description('Code generation and analysis');

  // codegen generate
  codegen
    .command('generate <design>')
    .description('Generate code from design')
    .option('-o, --output <dir>', 'Output directory', 'src/generated')
    .option('-l, --language <lang>', 'Target language', 'typescript')
    .option('-t, --template <name>', 'Code template to use')
    .action(async (design: string, options: CodegenOptions) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const designPath = resolve(process.cwd(), design);
        const content = await readFile(designPath, 'utf-8');

        // Parse design and generate code
        const files = generateCodeFromDesign(content, options);

        const outputDir = resolve(process.cwd(), options.output ?? 'src/generated');
        await mkdir(outputDir, { recursive: true });

        let totalLines = 0;
        const languages = new Set<string>();

        for (const file of files) {
          const filePath = resolve(outputDir, file.filename);
          await mkdir(dirname(filePath), { recursive: true });
          await writeFile(filePath, file.content, 'utf-8');
          totalLines += file.content.split('\n').length;
          languages.add(file.language);
        }

        const result: GenerationResult = {
          success: true,
          files,
          summary: {
            totalFiles: files.length,
            totalLines,
            languages: Array.from(languages),
          },
          message: `Generated ${files.length} files (${totalLines} lines)`,
        };

        if (!globalOpts.quiet) {
          console.log(`✅ Code generated in ${outputDir}`);
          for (const file of files) {
            console.log(`   - ${file.filename}`);
          }
        }

        if (globalOpts.json) {
          outputResult(result, globalOpts);
        }

        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Code generation failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // codegen analyze
  codegen
    .command('analyze <path>')
    .description('Static code analysis')
    .option('--strict', 'Enable strict mode', false)
    .action(async (path: string, _options: { strict?: boolean }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const targetPath = resolve(process.cwd(), path);
        const issues: AnalysisIssue[] = [];
        let fileCount = 0;
        let totalLines = 0;

        // Check if path is file or directory
        const pathStat = await stat(targetPath);

        if (pathStat.isDirectory()) {
          await analyzeDirectory(targetPath, issues, (lines) => {
            fileCount++;
            totalLines += lines;
          });
        } else {
          const content = await readFile(targetPath, 'utf-8');
          const lines = content.split('\n');
          analyzeFile(targetPath, lines, issues);
          fileCount = 1;
          totalLines = lines.length;
        }

        const errors = issues.filter(i => i.severity === 'error').length;
        const warnings = issues.filter(i => i.severity === 'warning').length;
        const info = issues.filter(i => i.severity === 'info').length;

        // Calculate metrics
        const complexity = Math.round(totalLines / 10); // Simplified
        const maintainabilityIndex = Math.max(0, 100 - errors * 10 - warnings * 2);

        const result: AnalysisResult = {
          success: true,
          issues,
          metrics: {
            files: fileCount,
            lines: totalLines,
            complexity,
            maintainabilityIndex,
          },
          summary: { errors, warnings, info },
          message: errors === 0
            ? `✅ Analyzed ${fileCount} files - No errors found`
            : `⚠️ Found ${errors} errors, ${warnings} warnings`,
        };

        outputResult(result, globalOpts);
        process.exit(errors === 0 ? ExitCode.SUCCESS : ExitCode.VALIDATION_ERROR);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Analysis failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // codegen security
  codegen
    .command('security <path>')
    .description('Security scan')
    .option('--severity <level>', 'Minimum severity to report', 'low')
    .action(async (path: string, options: { severity?: string }) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const targetPath = resolve(process.cwd(), path);
        const vulnerabilities: SecurityVulnerability[] = [];

        // Check if path is file or directory
        const pathStat = await stat(targetPath);

        if (pathStat.isDirectory()) {
          await scanDirectory(targetPath, vulnerabilities);
        } else {
          const content = await readFile(targetPath, 'utf-8');
          scanFile(targetPath, content, vulnerabilities);
        }

        // Filter by severity
        const severityOrder = ['critical', 'high', 'medium', 'low'];
        const minSeverityIndex = severityOrder.indexOf(options.severity ?? 'low');
        const filtered = vulnerabilities.filter(v => 
          severityOrder.indexOf(v.severity) <= minSeverityIndex
        );

        const critical = filtered.filter(v => v.severity === 'critical').length;
        const high = filtered.filter(v => v.severity === 'high').length;
        const medium = filtered.filter(v => v.severity === 'medium').length;
        const low = filtered.filter(v => v.severity === 'low').length;

        // Calculate security score (0-100)
        const score = Math.max(0, 100 - critical * 30 - high * 15 - medium * 5 - low * 1);

        const result: SecurityResult = {
          success: true,
          vulnerabilities: filtered,
          summary: { critical, high, medium, low },
          score,
          message: critical + high === 0
            ? `✅ Security score: ${score}/100 - No critical issues`
            : `🔴 Security score: ${score}/100 - ${critical} critical, ${high} high severity issues`,
        };

        outputResult(result, globalOpts);
        process.exit(critical === 0 ? ExitCode.SUCCESS : ExitCode.VALIDATION_ERROR);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Security scan failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });
}

/**
 * Extract EARS requirements from content
 */
function extractEarsRequirements(content: string): Array<{
  id: string;
  pattern: string;
  priority: string;
  description: string;
}> {
  const requirements: Array<{ id: string; pattern: string; priority: string; description: string }> = [];
  
  // Match EARS requirements from table or detailed sections
  // Format: | REQ-XX-001 | pattern | P0 | description |
  const tableMatches = content.matchAll(/\|\s*(REQ-[\w-]+)\s*\|\s*(\w+)\s*\|\s*(P\d)\s*\|\s*([^|]+)\|/g);
  for (const match of tableMatches) {
    requirements.push({
      id: match[1],
      pattern: match[2].toLowerCase(),
      priority: match[3],
      description: match[4].trim(),
    });
  }
  
  // Also extract from detailed sections
  // Format: ### REQ-XX-001 (Pattern - P0)
  // > The system SHALL...
  const detailMatches = content.matchAll(/###\s*(REQ-[\w-]+)\s*\((\w+)\s*-\s*(P\d)\)\s*\n+>\s*(.+?)(?=\n\n|\n###|$)/gs);
  for (const match of detailMatches) {
    const existing = requirements.find(r => r.id === match[1]);
    if (!existing) {
      requirements.push({
        id: match[1],
        pattern: match[2].toLowerCase(),
        priority: match[3],
        description: match[4].trim(),
      });
    }
  }
  
  return requirements;
}

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
 */
function generateCodeFromDesign(content: string, options: CodegenOptions): GeneratedCode[] {
  const files: GeneratedCode[] = [];
  const language = options.language ?? 'typescript';
  const ext = language === 'typescript' ? '.ts' : language === 'javascript' ? '.js' : '.py';

  // Check if this is an EARS requirements document
  const isEarsDoc = content.includes('EARS') || content.includes('SHALL') || content.includes('REQ-');
  
  if (isEarsDoc) {
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
 * Create UserInterface instance
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
 * Analyze directory
 */
async function analyzeDirectory(
  dir: string,
  issues: AnalysisIssue[],
  onFile: (lines: number) => void
): Promise<void> {
  const entries = await readdir(dir, { withFileTypes: true });

  for (const entry of entries) {
    const fullPath = join(dir, entry.name);

    if (entry.isDirectory()) {
      if (!entry.name.startsWith('.') && entry.name !== 'node_modules') {
        await analyzeDirectory(fullPath, issues, onFile);
      }
    } else if (entry.isFile()) {
      const ext = extname(entry.name);
      if (['.ts', '.js', '.tsx', '.jsx', '.py'].includes(ext)) {
        const content = await readFile(fullPath, 'utf-8');
        const lines = content.split('\n');
        analyzeFile(fullPath, lines, issues);
        onFile(lines.length);
      }
    }
  }
}

/**
 * Analyze file
 */
function analyzeFile(file: string, lines: string[], issues: AnalysisIssue[]): void {
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];

    for (const rule of ANALYSIS_RULES) {
      if ('pattern' in rule && rule.pattern) {
        rule.pattern.lastIndex = 0;
        if (rule.pattern.test(line)) {
          issues.push({
            file,
            line: i + 1,
            severity: rule.severity,
            rule: rule.name,
            message: rule.message,
          });
        }
      } else if ('check' in rule && rule.check?.(line)) {
        issues.push({
          file,
          line: i + 1,
          severity: rule.severity,
          rule: rule.name,
          message: rule.message,
        });
      }
    }
  }
}

/**
 * Scan directory for security issues
 */
async function scanDirectory(
  dir: string,
  vulnerabilities: SecurityVulnerability[]
): Promise<void> {
  const entries = await readdir(dir, { withFileTypes: true });

  for (const entry of entries) {
    const fullPath = join(dir, entry.name);

    if (entry.isDirectory()) {
      if (!entry.name.startsWith('.') && entry.name !== 'node_modules') {
        await scanDirectory(fullPath, vulnerabilities);
      }
    } else if (entry.isFile()) {
      const ext = extname(entry.name);
      if (['.ts', '.js', '.tsx', '.jsx', '.py', '.json', '.yml', '.yaml'].includes(ext)) {
        const content = await readFile(fullPath, 'utf-8');
        scanFile(fullPath, content, vulnerabilities);
      }
    }
  }
}

/**
 * Scan file for security issues
 */
function scanFile(
  file: string,
  content: string,
  vulnerabilities: SecurityVulnerability[]
): void {
  const lines = content.split('\n');

  for (const pattern of SECURITY_PATTERNS) {
    pattern.pattern.lastIndex = 0;

    for (let i = 0; i < lines.length; i++) {
      pattern.pattern.lastIndex = 0;
      if (pattern.pattern.test(lines[i])) {
        vulnerabilities.push({
          severity: pattern.severity,
          type: pattern.type,
          file,
          line: i + 1,
          description: pattern.description,
          recommendation: pattern.recommendation,
          cwe: pattern.cwe,
        });
      }
    }
  }
}

/**
 * Convert to kebab-case
 */
function toKebabCase(str: string): string {
  return str
    .replace(/([a-z])([A-Z])/g, '$1-$2')
    .replace(/[\s_]+/g, '-')
    .toLowerCase();
}

/**
 * Convert to PascalCase
 */
function toPascalCase(str: string): string {
  return str
    .replace(/[-_\s]+(.)?/g, (_, c) => (c ? c.toUpperCase() : ''))
    .replace(/^./, s => s.toUpperCase());
}

/**
 * Convert to snake_case
 */
function toSnakeCase(str: string): string {
  return str
    .replace(/([a-z])([A-Z])/g, '$1_$2')
    .replace(/[-\s]+/g, '_')
    .toLowerCase();
}

export {
  generateCodeFromDesign,
  analyzeFile,
  scanFile,
};
