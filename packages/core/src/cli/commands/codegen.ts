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
  const tableMatches = content.matchAll(/\|\s*(REQ-[\w-]+)\s*\|\s*([\w-]+)\s*\|\s*(P\d)\s*\|\s*([^|]+)\|/g);
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
    
    // Shopping/E-commerce specific components
    if (desc.includes('cart') || desc.includes('カート')) {
      const name = 'CartService';
      if (!components.has(name)) {
        components.set(name, { name, type: 'service', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }
    
    if (desc.includes('product') || desc.includes('catalog') || desc.includes('商品')) {
      const name = 'ProductCatalogService';
      if (!components.has(name)) {
        components.set(name, { name, type: 'service', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }
    
    if (desc.includes('checkout') || desc.includes('購入') || desc.includes('決済')) {
      const name = 'CheckoutService';
      if (!components.has(name)) {
        components.set(name, { name, type: 'service', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }
    
    if (desc.includes('price') || desc.includes('total') || desc.includes('tax') || desc.includes('価格') || desc.includes('計算')) {
      const name = 'PricingService';
      if (!components.has(name)) {
        components.set(name, { name, type: 'service', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }
    
    if (desc.includes('stock') || desc.includes('inventory') || desc.includes('在庫')) {
      const name = 'InventoryService';
      if (!components.has(name)) {
        components.set(name, { name, type: 'service', requirements: [] });
      }
      components.get(name)!.requirements.push(req.id);
    }
    
    if (desc.includes('coupon') || desc.includes('discount') || desc.includes('割引')) {
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
 */
function generateCodeFromDesign(content: string, options: CodegenOptions): GeneratedCode[] {
  const files: GeneratedCode[] = [];
  const language = options.language ?? 'typescript';
  const ext = language === 'typescript' ? '.ts' : language === 'javascript' ? '.js' : '.py';

  // Check if this is an EARS requirements document
  const isEarsDoc = content.includes('EARS') || content.includes('SHALL') || content.includes('REQ-');
  
  // Check if this is a C4 design document (table-based)
  const isC4Design = content.includes('C4 Component') || 
                     content.includes('### Elements') || 
                     content.includes('### コンポーネント一覧') ||
                     content.includes('Component Diagram') ||
                     (content.includes('| ID |') && content.includes('| Type |'));
  
  if (isC4Design) {
    // Parse C4 design document table format
    const c4Components = parseC4DesignComponents(content);
    const reqMatches = content.match(/REQ-[A-Z]+-\d+/g) || [];
    const patterns = extractDesignPatterns(content);
    
    for (const component of c4Components) {
      if (component.type === 'person') continue; // Skip user/person elements
      
      const code = generateC4ComponentCode(component, language, reqMatches, patterns);
      // Normalize name: BLOG_PLATFORM → BlogPlatform → blog-platform
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
 * C4 Component definition
 */
interface C4Component {
  id: string;
  name: string;
  type: string;
  description: string;
  pattern?: string;
}

/**
 * Design Pattern definition
 */
interface DesignPattern {
  name: string;
  category: string;
  intent: string;
}

/**
 * Parse C4 design document components from table format
 */
function parseC4DesignComponents(content: string): C4Component[] {
  const components: C4Component[] = [];
  
  // Match table rows: | ID | Name | Type | Description | or | ID | Name | Type | Description | Pattern |
  // Support both 4 and 5 column formats
  const tableRowRegex = /\|\s*(\w+)\s*\|\s*(\w+)\s*\|\s*(\w+)\s*\|\s*([^|]+?)\s*\|(?:\s*([^|]*?)\s*\|)?/g;
  let match;
  
  while ((match = tableRowRegex.exec(content)) !== null) {
    const [, id, name, type, description, pattern] = match;
    // Skip header row and separator row
    if (id === 'ID' || id === '----' || id.startsWith('-') || name === '----' || name === 'Name') continue;
    
    components.push({
      id,
      name,
      type: type.toLowerCase(),
      description: description.trim(),
      pattern: pattern?.trim() || undefined,
    });
  }
  
  return components;
}

/**
 * Extract design patterns from document
 */
function extractDesignPatterns(content: string): DesignPattern[] {
  const patterns: DesignPattern[] = [];
  
  // Match pattern sections: ### PatternName
  const patternSectionRegex = /###\s+(\w+)\s*\n.*?Category:\s*(\w+).*?Intent:\s*(.+?)(?=\n\n|$)/gis;
  let match: RegExpExecArray | null;
  
  while ((match = patternSectionRegex.exec(content)) !== null) {
    patterns.push({
      name: match[1],
      category: match[2],
      intent: match[3].trim(),
    });
  }
  
  // Also try simpler pattern: - **Category**: behavioral
  const simplePatternRegex = /###\s+(\w+)\s*\n-\s*\*\*Category\*\*:\s*(\w+)\s*\n-\s*\*\*Intent\*\*:\s*(.+)/gi;
  let simpleMatch: RegExpExecArray | null;
  
  while ((simpleMatch = simplePatternRegex.exec(content)) !== null) {
    // Avoid duplicates
    if (!patterns.find(p => p.name === simpleMatch![1])) {
      patterns.push({
        name: simpleMatch[1],
        category: simpleMatch[2],
        intent: simpleMatch[3].trim(),
      });
    }
  }
  
  return patterns;
}

/**
 * Generate TypeScript code for C4 component
 */
function generateC4ComponentCode(
  component: C4Component,
  language: string,
  requirements: string[],
  patterns: DesignPattern[]
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
    
    // Service-specific template with proper types
    if (lowerType === 'service' && (pattern?.toLowerCase() === 'service' || description.includes('ビジネスロジック') || description.includes('CRUD'))) {
      return generateServiceTemplate(className, interfaceName, id, description, patternComments, reqComments);
    }
    
    // Default: Use method stubs
    const methodStubs = generateMethodStubsForComponent(pattern || type, description);
    
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
 * Generate method stubs based on component type and description
 */
function generateMethodStubsForComponent(type: string, description: string): Array<{
  name: string;
  params: string;
  returnType: string;
  description: string;
  async: boolean;
}> {
  const lowerDesc = description.toLowerCase();
  const lowerType = type.toLowerCase();
  const methods: Array<{
    name: string;
    params: string;
    returnType: string;
    description: string;
    async: boolean;
  }> = [];
  
  // Service patterns - CRUD operations
  if (lowerType === 'service' || lowerDesc.includes('crud') || lowerDesc.includes('管理')) {
    methods.push(
      {
        name: 'create',
        params: 'data: CreateInput',
        returnType: 'Promise<Entity>',
        description: 'Create a new entity',
        async: true,
      },
      {
        name: 'getById',
        params: 'id: string',
        returnType: 'Promise<Entity | null>',
        description: 'Get entity by ID',
        async: true,
      },
      {
        name: 'getAll',
        params: 'filter?: FilterOptions',
        returnType: 'Promise<Entity[]>',
        description: 'Get all entities',
        async: true,
      },
      {
        name: 'update',
        params: 'id: string, data: UpdateInput',
        returnType: 'Promise<Entity>',
        description: 'Update an entity',
        async: true,
      },
      {
        name: 'delete',
        params: 'id: string',
        returnType: 'Promise<boolean>',
        description: 'Delete an entity',
        async: true,
      }
    );
    return methods;
  }
  
  // Repository patterns
  if (lowerType === 'repository' || lowerDesc.includes('storage') || lowerDesc.includes('persist') || lowerDesc.includes('永続化')) {
    methods.push(
      {
        name: 'save',
        params: 'key: string, data: T',
        returnType: 'void',
        description: 'Save data',
        async: false,
      },
      {
        name: 'load',
        params: 'key: string',
        returnType: 'T | null',
        description: 'Load data',
        async: false,
      },
      {
        name: 'remove',
        params: 'key: string',
        returnType: 'void',
        description: 'Remove data',
        async: false,
      },
      {
        name: 'clear',
        params: '',
        returnType: 'void',
        description: 'Clear all data',
        async: false,
      }
    );
    return methods;
  }
  
  // Validator patterns
  if (lowerType === 'validator' || lowerDesc.includes('validat') || lowerDesc.includes('検証') || lowerDesc.includes('入力')) {
    methods.push(
      {
        name: 'validate',
        params: 'input: unknown',
        returnType: '{ valid: boolean; errors: string[] }',
        description: 'Validate input',
        async: false,
      },
      {
        name: 'sanitize',
        params: 'input: string',
        returnType: 'string',
        description: 'Sanitize input',
        async: false,
      }
    );
    return methods;
  }
  
  // Search/Filter patterns
  if (lowerDesc.includes('search') || lowerDesc.includes('filter') || lowerDesc.includes('検索') || lowerDesc.includes('フィルタ')) {
    methods.push(
      {
        name: 'search',
        params: 'query: string',
        returnType: 'Promise<SearchResult[]>',
        description: 'Search items',
        async: true,
      },
      {
        name: 'filter',
        params: 'criteria: FilterCriteria',
        returnType: 'Promise<Entity[]>',
        description: 'Filter items by criteria',
        async: true,
      },
      {
        name: 'sort',
        params: 'items: Entity[], sortBy: string',
        returnType: 'Entity[]',
        description: 'Sort items',
        async: false,
      }
    );
    return methods;
  }
  
  // Notification/Alert patterns
  if (lowerDesc.includes('notification') || lowerDesc.includes('alert') || lowerDesc.includes('通知') || lowerDesc.includes('アラート')) {
    methods.push(
      {
        name: 'subscribe',
        params: 'callback: (event: Event) => void',
        returnType: '() => void',
        description: 'Subscribe to events',
        async: false,
      },
      {
        name: 'notify',
        params: 'event: Event',
        returnType: 'void',
        description: 'Notify subscribers',
        async: false,
      },
      {
        name: 'checkConditions',
        params: '',
        returnType: 'Promise<Alert[]>',
        description: 'Check alert conditions',
        async: true,
      }
    );
    return methods;
  }
  
  // Export/Import patterns
  if (lowerDesc.includes('export') || lowerDesc.includes('import') || lowerDesc.includes('エクスポート') || lowerDesc.includes('インポート')) {
    methods.push(
      {
        name: 'exportToJson',
        params: 'data: Entity[]',
        returnType: 'string',
        description: 'Export data to JSON',
        async: false,
      },
      {
        name: 'importFromJson',
        params: 'json: string',
        returnType: '{ success: boolean; imported: number; errors: string[] }',
        description: 'Import data from JSON',
        async: false,
      }
    );
    return methods;
  }
  
  // Authentication patterns
  if (lowerDesc.includes('auth') || lowerDesc.includes('login') || lowerDesc.includes('認証')) {
    methods.push(
      {
        name: 'authenticate',
        params: 'credentials: { username: string; password: string }',
        returnType: 'Promise<{ token: string }>',
        description: 'Authenticate user',
        async: true,
      },
      {
        name: 'validateToken',
        params: 'token: string',
        returnType: 'Promise<boolean>',
        description: 'Validate token',
        async: true,
      }
    );
    return methods;
  }
  
  // Entity/Model patterns
  if (lowerType === 'entity' || lowerType === 'model' || lowerDesc.includes('データモデル') || lowerDesc.includes('エンティティ')) {
    methods.push(
      {
        name: 'toJSON',
        params: '',
        returnType: 'Record<string, unknown>',
        description: 'Convert to JSON object',
        async: false,
      },
      {
        name: 'validate',
        params: '',
        returnType: 'boolean',
        description: 'Validate entity state',
        async: false,
      }
    );
    return methods;
  }
  
  // Component/UI patterns
  if (lowerType === 'component' || lowerDesc.includes('表示') || lowerDesc.includes('ui') || lowerDesc.includes('display')) {
    methods.push(
      {
        name: 'render',
        params: 'data: RenderData',
        returnType: 'string',
        description: 'Render component',
        async: false,
      },
      {
        name: 'update',
        params: 'props: Props',
        returnType: 'void',
        description: 'Update component with new props',
        async: false,
      }
    );
    return methods;
  }
  
  // Default method if no patterns matched
  methods.push({
    name: 'execute',
    params: '',
    returnType: 'Promise<void>',
    description: 'Execute main operation',
    async: true,
  });
  
  return methods;
}

/**
 * Convert to PascalCase
 * Handles: UPPER_CASE, snake_case, kebab-case, camelCase, etc.
 * Examples:
 *   - BLOG_PLATFORM → BlogPlatform
 *   - blog-platform → BlogPlatform
 *   - BlogPlatformService → BlogPlatformService
 *   - BLOG_PLATFORMService → BlogPlatformService
 *   - UserAccountEntity → UserAccountEntity
 */
function toPascalCase(str: string): string {
  // Check if already proper PascalCase (no underscores/hyphens, starts uppercase)
  if (/^[A-Z][a-zA-Z0-9]*$/.test(str) && str !== str.toUpperCase()) {
    return str;
  }
  
  // Preserve known suffixes like Service, Entity, Repository, etc.
  const suffixes = ['Service', 'Entity', 'Repository', 'Validator', 'Controller', 'Manager', 'Component', 'View', 'Panel', 'Helper', 'Factory', 'Builder'];
  let preservedSuffix = '';
  let baseName = str;
  
  for (const suffix of suffixes) {
    if (str.endsWith(suffix) && str.length > suffix.length) {
      preservedSuffix = suffix;
      baseName = str.slice(0, -suffix.length);
      break;
    }
  }
  
  // Convert base name to PascalCase
  const pascalBase = baseName
    .toLowerCase()
    .replace(/[-_\s]+(.)?/g, (_, c) => (c ? c.toUpperCase() : ''))
    .replace(/^./, s => s.toUpperCase());
  
  return pascalBase + preservedSuffix;
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
 * Generate Service template with proper types
 */
function generateServiceTemplate(
  className: string,
  interfaceName: string,
  id: string,
  description: string,
  patternComments: string,
  reqComments: string
): string {
  const baseName = className.replace(/Service$/, '');
  
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
  create(data: Create${baseName}Input): Promise<${baseName}Entity>;
  getById(id: string): Promise<${baseName}Entity | null>;
  getAll(filter?: ${baseName}FilterOptions): Promise<${baseName}Entity[]>;
  update(id: string, data: Update${baseName}Input): Promise<${baseName}Entity | null>;
  delete(id: string): Promise<boolean>;
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
  }
}

/**
 * Factory function
 */
export function create${className}(): ${interfaceName} {
  return new ${className}();
}
`;
}

export {
  generateCodeFromDesign,
  analyzeFile,
  scanFile,
};
