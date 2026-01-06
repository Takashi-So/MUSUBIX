/**
 * @fileoverview Taint analysis engine
 * @module @nahisaho/musubix-security/analysis/taint-analyzer
 * @trace REQ-SEC-TAINT-001, REQ-SEC-TAINT-002, REQ-SEC-TAINT-003, REQ-SEC-TAINT-004
 */

import type { SourceFile } from 'ts-morph';
import { SyntaxKind } from 'ts-morph';
import type {
  TaintSource,
  TaintSink,
  TaintPath,
  TaintFlowStep,
  TaintResult,
  TaintAnalysisOptions,
  TaintSourceCategory,
  TaintSinkCategory,
  Severity,
} from '../types/index.js';
import { BUILTIN_SANITIZERS } from '../types/taint.js';
import { ASTParser, getASTParser } from '../infrastructure/ast-parser.js';
import { FileScanner, createFileScanner } from '../infrastructure/file-scanner.js';

/**
 * Generate taint source ID
 */
let sourceCounter = 0;
function generateSourceId(): string {
  return `SRC-${String(++sourceCounter).padStart(4, '0')}`;
}

/**
 * Generate taint sink ID
 */
let sinkCounter = 0;
function generateSinkId(): string {
  return `SNK-${String(++sinkCounter).padStart(4, '0')}`;
}

/**
 * Generate taint path ID
 */
let pathCounter = 0;
function generatePathId(): string {
  return `PATH-${String(++pathCounter).padStart(4, '0')}`;
}

/**
 * Reset counters (for testing)
 */
export function resetTaintCounters(): void {
  sourceCounter = 0;
  sinkCounter = 0;
  pathCounter = 0;
}

/**
 * Source pattern definition
 */
interface SourcePattern {
  category: TaintSourceCategory;
  patterns: {
    receiver?: string;
    method?: string;
    property?: string;
  }[];
  description: string;
}

/**
 * Sink pattern definition
 */
interface SinkPattern {
  category: TaintSinkCategory;
  severity: Severity;
  patterns: {
    receiver?: string;
    method: string;
    argIndex: number;
  }[];
  expectedSanitizers: string[];
  description: string;
}

/**
 * Built-in source patterns
 */
const SOURCE_PATTERNS: SourcePattern[] = [
  {
    category: 'user-input',
    patterns: [
      { receiver: 'req', property: 'body' },
      { receiver: 'req', property: 'query' },
      { receiver: 'req', property: 'params' },
      { receiver: 'req', property: 'headers' },
      { receiver: 'req', property: 'cookies' },
      { receiver: 'ctx', property: 'request' },
      { receiver: 'ctx', property: 'query' },
      { method: 'prompt' },
      { method: 'getElementById' },
      { method: 'querySelector' },
    ],
    description: 'User-controlled input',
  },
  {
    category: 'database',
    patterns: [
      { method: 'findOne' },
      { method: 'findMany' },
      { method: 'find' },
      { receiver: 'db', method: 'query' },
    ],
    description: 'Database query results',
  },
  {
    category: 'file-system',
    patterns: [
      { method: 'readFile' },
      { method: 'readFileSync' },
      { receiver: 'fs', method: 'readFile' },
    ],
    description: 'File system reads',
  },
  {
    category: 'network',
    patterns: [
      { method: 'fetch' },
      { method: 'axios' },
      { receiver: 'http', method: 'get' },
      { receiver: 'https', method: 'get' },
    ],
    description: 'Network responses',
  },
  {
    category: 'environment',
    patterns: [
      { receiver: 'process', property: 'env' },
    ],
    description: 'Environment variables',
  },
  {
    category: 'cli-args',
    patterns: [
      { receiver: 'process', property: 'argv' },
    ],
    description: 'Command line arguments',
  },
];

/**
 * Built-in sink patterns
 */
const SINK_PATTERNS: SinkPattern[] = [
  {
    category: 'sql-query',
    severity: 'critical',
    patterns: [
      { method: 'query', argIndex: 0 },
      { method: 'execute', argIndex: 0 },
      { receiver: 'knex', method: 'raw', argIndex: 0 },
    ],
    expectedSanitizers: ['escape', 'parameterize'],
    description: 'SQL query execution',
  },
  {
    category: 'command-exec',
    severity: 'critical',
    patterns: [
      { method: 'exec', argIndex: 0 },
      { method: 'execSync', argIndex: 0 },
      { receiver: 'child_process', method: 'spawn', argIndex: 0 },
    ],
    expectedSanitizers: ['quote', 'escape'],
    description: 'OS command execution',
  },
  {
    category: 'file-read',
    severity: 'high',
    patterns: [
      { method: 'readFile', argIndex: 0 },
      { method: 'readFileSync', argIndex: 0 },
      { receiver: 'fs', method: 'access', argIndex: 0 },
    ],
    expectedSanitizers: ['basename', 'resolve'],
    description: 'File system read',
  },
  {
    category: 'file-write',
    severity: 'high',
    patterns: [
      { method: 'writeFile', argIndex: 0 },
      { method: 'writeFileSync', argIndex: 0 },
    ],
    expectedSanitizers: ['basename', 'resolve'],
    description: 'File system write',
  },
  {
    category: 'html-output',
    severity: 'high',
    patterns: [
      { receiver: 'res', method: 'send', argIndex: 0 },
      { receiver: 'res', method: 'write', argIndex: 0 },
      { receiver: 'res', method: 'render', argIndex: 1 },
    ],
    expectedSanitizers: ['escapeHtml', 'encode', 'sanitizeHtml'],
    description: 'HTML response output',
  },
  {
    category: 'redirect',
    severity: 'medium',
    patterns: [
      { receiver: 'res', method: 'redirect', argIndex: 0 },
    ],
    expectedSanitizers: ['validateUrl', 'isAllowedDomain'],
    description: 'URL redirect',
  },
  {
    category: 'eval',
    severity: 'critical',
    patterns: [
      { method: 'eval', argIndex: 0 },
      { method: 'Function', argIndex: 0 },
    ],
    expectedSanitizers: [],
    description: 'Dynamic code evaluation',
  },
  {
    category: 'http-request',
    severity: 'high',
    patterns: [
      { method: 'fetch', argIndex: 0 },
      { receiver: 'axios', method: 'get', argIndex: 0 },
      { receiver: 'axios', method: 'post', argIndex: 0 },
    ],
    expectedSanitizers: ['validateUrl', 'isAllowedDomain'],
    description: 'Outbound HTTP request',
  },
];

/**
 * Taint analyzer engine
 */
export class TaintAnalyzer {
  private parser: ASTParser;
  private fileScanner: FileScanner;
  private options: TaintAnalysisOptions;
  private sourcePatterns: SourcePattern[];
  private sinkPatterns: SinkPattern[];

  constructor(options: TaintAnalysisOptions = {}) {
    this.parser = getASTParser();
    this.fileScanner = createFileScanner();
    this.options = options;
    this.sourcePatterns = [...SOURCE_PATTERNS];
    this.sinkPatterns = [...SINK_PATTERNS];

    // Add custom sources
    if (options.customSources) {
      for (const custom of options.customSources) {
        this.sourcePatterns.push({
          category: custom.category,
          patterns: [{ method: custom.pattern }],
          description: custom.description,
        });
      }
    }

    // Add custom sinks
    if (options.customSinks) {
      for (const custom of options.customSinks) {
        this.sinkPatterns.push({
          category: custom.category,
          severity: custom.severity,
          patterns: [{ method: custom.pattern, argIndex: 0 }],
          expectedSanitizers: [],
          description: custom.description,
        });
      }
    }
  }

  /**
   * Analyze a single file for taint issues
   */
  analyzeFile(filePath: string): { sources: TaintSource[]; sinks: TaintSink[] } {
    const sourceFile = this.parser.parseFile(filePath);
    return {
      sources: this.findSources(sourceFile),
      sinks: this.findSinks(sourceFile),
    };
  }

  /**
   * Find taint sources in a source file
   */
  private findSources(sourceFile: SourceFile): TaintSource[] {
    const sources: TaintSource[] = [];
    
    // Find property access expressions (req.body, process.env, etc.)
    const propertyAccesses = sourceFile.getDescendantsOfKind(SyntaxKind.PropertyAccessExpression);
    for (const access of propertyAccesses) {
      const receiver = access.getExpression();
      const property = access.getName();
      
      let receiverName: string | undefined;
      if (receiver.getKind() === SyntaxKind.Identifier) {
        receiverName = receiver.getText();
      }

      for (const pattern of this.sourcePatterns) {
        for (const p of pattern.patterns) {
          if (p.receiver && p.property) {
            if (receiverName === p.receiver && property === p.property) {
              sources.push({
                id: generateSourceId(),
                category: pattern.category,
                location: this.parser.getLocation(access),
                variableName: access.getText(),
                expression: access.getText(),
                description: pattern.description,
                confidence: 0.9,
              });
            }
          }
        }
      }
    }

    // Find call expressions (getElementById, fetch, etc.)
    const calls = sourceFile.getDescendantsOfKind(SyntaxKind.CallExpression);
    for (const call of calls) {
      const funcName = this.parser.getFunctionName(call);
      const receiverName = this.parser.getReceiverName(call);

      for (const pattern of this.sourcePatterns) {
        for (const p of pattern.patterns) {
          if (p.method && funcName === p.method) {
            if (!p.receiver || receiverName === p.receiver) {
              sources.push({
                id: generateSourceId(),
                category: pattern.category,
                location: this.parser.getLocation(call),
                variableName: call.getText(),
                expression: call.getText(),
                description: pattern.description,
                confidence: 0.85,
              });
            }
          }
        }
      }
    }

    return sources;
  }

  /**
   * Find taint sinks in a source file
   */
  private findSinks(sourceFile: SourceFile): TaintSink[] {
    const sinks: TaintSink[] = [];
    const calls = sourceFile.getDescendantsOfKind(SyntaxKind.CallExpression);

    for (const call of calls) {
      const funcName = this.parser.getFunctionName(call);
      const receiverName = this.parser.getReceiverName(call);

      for (const pattern of this.sinkPatterns) {
        for (const p of pattern.patterns) {
          if (funcName === p.method) {
            if (!p.receiver || receiverName === p.receiver) {
              sinks.push({
                id: generateSinkId(),
                category: pattern.category,
                location: this.parser.getLocation(call),
                functionName: funcName,
                argumentIndex: p.argIndex,
                expectedSanitizers: pattern.expectedSanitizers,
                description: pattern.description,
                severity: pattern.severity,
              });
            }
          }
        }
      }
    }

    return sinks;
  }

  /**
   * Trace taint flow from sources to sinks (simplified)
   * Note: Full interprocedural analysis would require more sophisticated data flow analysis
   */
  private tracePaths(
    sources: TaintSource[],
    sinks: TaintSink[],
    sourceFile: SourceFile
  ): TaintPath[] {
    const paths: TaintPath[] = [];

    // Simple intraprocedural analysis: check if source and sink are in same function
    // and source appears before sink
    for (const source of sources) {
      for (const sink of sinks) {
        // Check if in same file
        if (source.location.file !== sink.location.file) continue;

        // Check if source is before sink
        if (source.location.startLine > sink.location.startLine) continue;

        // Check if they could be connected (simplified - same function scope)
        const isConnected = this.checkConnection(source, sink, sourceFile);
        if (!isConnected) continue;

        // Check for sanitization
        const sanitized = this.checkSanitization(
          source,
          sink,
          sourceFile,
          sink.expectedSanitizers
        );

        // Only report unsanitized paths
        if (!sanitized) {
          const steps = this.buildFlowSteps(source, sink, sourceFile);
          paths.push({
            id: generatePathId(),
            source,
            sink,
            steps,
            sanitized: false,
            confidence: Math.min(source.confidence, 0.8),
            length: steps.length,
          });
        }
      }
    }

    return paths;
  }

  /**
   * Check if source and sink could be connected
   */
  private checkConnection(
    source: TaintSource,
    sink: TaintSink,
    _sourceFile: SourceFile
  ): boolean {
    // Simplified: just check if they're within reasonable line distance
    const lineDistance = sink.location.startLine - source.location.startLine;
    const maxDepth = this.options.maxPathDepth ?? 10;
    
    return lineDistance >= 0 && lineDistance <= maxDepth * 5;
  }

  /**
   * Check if there's sanitization between source and sink
   */
  private checkSanitization(
    source: TaintSource,
    sink: TaintSink,
    sourceFile: SourceFile,
    expectedSanitizers: string[]
  ): boolean {
    // Get code between source and sink
    const calls = sourceFile.getDescendantsOfKind(SyntaxKind.CallExpression);
    
    for (const call of calls) {
      const loc = this.parser.getLocation(call);
      
      // Check if call is between source and sink
      if (
        loc.startLine > source.location.startLine &&
        loc.startLine < sink.location.startLine
      ) {
        const funcName = this.parser.getFunctionName(call);
        
        // Check against expected sanitizers
        if (funcName && expectedSanitizers.includes(funcName)) {
          return true;
        }

        // Check against built-in sanitizers
        for (const sanitizer of BUILTIN_SANITIZERS) {
          if (funcName === sanitizer.name && sanitizer.protects.includes(sink.category)) {
            return true;
          }
        }

        // Check additional sanitizers from options
        if (this.options.additionalSanitizers) {
          for (const sanitizer of this.options.additionalSanitizers) {
            if (
              funcName === sanitizer.functionName &&
              sanitizer.sinkCategories.includes(sink.category)
            ) {
              return true;
            }
          }
        }
      }
    }

    return false;
  }

  /**
   * Build flow steps between source and sink
   */
  private buildFlowSteps(
    source: TaintSource,
    sink: TaintSink,
    _sourceFile: SourceFile
  ): TaintFlowStep[] {
    // Simplified: just source and sink as steps
    return [
      {
        index: 0,
        location: source.location,
        expression: source.expression,
        variableName: source.variableName,
        operation: 'assignment',
        sanitized: false,
      },
      {
        index: 1,
        location: sink.location,
        expression: `${sink.functionName}(...)`,
        operation: 'call',
        sanitized: false,
      },
    ];
  }

  /**
   * Analyze a directory for taint issues
   */
  async analyze(rootPath: string): Promise<TaintResult> {
    const startTime = Date.now();
    const files = await this.fileScanner.scan(rootPath);

    const allSources: TaintSource[] = [];
    const allSinks: TaintSink[] = [];
    const allPaths: TaintPath[] = [];
    let analyzedFiles = 0;

    for (const file of files) {
      if (this.options.excludePatterns?.some((p) => file.relativePath.includes(p))) {
        continue;
      }

      try {
        const sourceFile = this.parser.parseFile(file.path);
        const { sources, sinks } = this.analyzeFile(file.path);
        
        allSources.push(...sources);
        allSinks.push(...sinks);

        const paths = this.tracePaths(sources, sinks, sourceFile);
        allPaths.push(...paths);

        analyzedFiles++;
      } catch (error) {
        console.warn(`Warning: Failed to analyze ${file.path}: ${error}`);
      }
    }

    const duration = Date.now() - startTime;

    // Build summary
    const bySourceCategory: Record<TaintSourceCategory, number> = {
      'user-input': 0,
      'database': 0,
      'file-system': 0,
      'network': 0,
      'environment': 0,
      'config': 0,
      'cli-args': 0,
    };
    for (const source of allSources) {
      bySourceCategory[source.category]++;
    }

    const bySinkCategory: Record<TaintSinkCategory, number> = {
      'sql-query': 0,
      'nosql-query': 0,
      'command-exec': 0,
      'file-write': 0,
      'file-read': 0,
      'html-output': 0,
      'redirect': 0,
      'eval': 0,
      'deserialization': 0,
      'ldap-query': 0,
      'xpath-query': 0,
      'http-request': 0,
    };
    for (const sink of allSinks) {
      bySinkCategory[sink.category]++;
    }

    const bySeverity: Record<Severity, number> = { critical: 0, high: 0, medium: 0, low: 0, info: 0 };
    for (const path of allPaths) {
      bySeverity[path.sink.severity]++;
    }

    return {
      sources: allSources,
      sinks: allSinks,
      unsafePaths: allPaths,
      analyzedFiles,
      duration,
      timestamp: new Date(),
      summary: {
        totalSources: allSources.length,
        totalSinks: allSinks.length,
        unsafePathCount: allPaths.length,
        bySeverity,
        bySourceCategory,
        bySinkCategory,
      },
    };
  }
}

/**
 * Create a taint analyzer
 */
export function createTaintAnalyzer(options?: TaintAnalysisOptions): TaintAnalyzer {
  return new TaintAnalyzer(options);
}
