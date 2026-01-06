/**
 * @fileoverview TypeScript AST parser using ts-morph
 * @module @nahisaho/musubix-security/infrastructure/ast-parser
 * @trace REQ-SEC-SCAN-001, REQ-SEC-TAINT-001
 */

import { Project, SourceFile, Node, SyntaxKind, CallExpression, Identifier } from 'ts-morph';
import type { SourceLocation } from '../types/index.js';

/**
 * AST Parser service for TypeScript/JavaScript analysis
 */
export class ASTParser {
  private project: Project;
  private cache: Map<string, SourceFile> = new Map();

  constructor(tsConfigPath?: string) {
    this.project = new Project({
      tsConfigFilePath: tsConfigPath,
      skipAddingFilesFromTsConfig: true,
      compilerOptions: {
        allowJs: true,
        checkJs: false,
        noEmit: true,
        skipLibCheck: true,
      },
    });
  }

  /**
   * Parse a file and return its AST
   */
  parseFile(filePath: string): SourceFile {
    const cached = this.cache.get(filePath);
    if (cached) {
      return cached;
    }

    const sourceFile = this.project.addSourceFileAtPath(filePath);
    this.cache.set(filePath, sourceFile);
    return sourceFile;
  }

  /**
   * Parse source code string
   */
  parseCode(code: string, fileName = 'temp.ts'): SourceFile {
    return this.project.createSourceFile(fileName, code, { overwrite: true });
  }

  /**
   * Get source location from a node
   */
  getLocation(node: Node): SourceLocation {
    const sourceFile = node.getSourceFile();
    const start = node.getStart();
    const end = node.getEnd();
    const startPos = sourceFile.getLineAndColumnAtPos(start);
    const endPos = sourceFile.getLineAndColumnAtPos(end);

    return {
      file: sourceFile.getFilePath(),
      startLine: startPos.line,
      endLine: endPos.line,
      startColumn: startPos.column - 1, // Convert to 0-based
      endColumn: endPos.column - 1,
    };
  }

  /**
   * Find all function calls in a file
   */
  findCallExpressions(sourceFile: SourceFile): CallExpression[] {
    return sourceFile.getDescendantsOfKind(SyntaxKind.CallExpression);
  }

  /**
   * Find all string literals in a file
   */
  findStringLiterals(sourceFile: SourceFile): Node[] {
    return [
      ...sourceFile.getDescendantsOfKind(SyntaxKind.StringLiteral),
      ...sourceFile.getDescendantsOfKind(SyntaxKind.NoSubstitutionTemplateLiteral),
      ...sourceFile.getDescendantsOfKind(SyntaxKind.TemplateExpression),
    ];
  }

  /**
   * Find all identifiers in a file
   */
  findIdentifiers(sourceFile: SourceFile): Identifier[] {
    return sourceFile.getDescendantsOfKind(SyntaxKind.Identifier);
  }

  /**
   * Get function/method name from a call expression
   */
  getFunctionName(callExpr: CallExpression): string | undefined {
    const expr = callExpr.getExpression();
    
    // Direct function call: functionName()
    if (Node.isIdentifier(expr)) {
      return expr.getText();
    }
    
    // Method call: obj.methodName()
    if (Node.isPropertyAccessExpression(expr)) {
      return expr.getName();
    }

    // Element access: obj['methodName']()
    if (Node.isElementAccessExpression(expr)) {
      const arg = expr.getArgumentExpression();
      if (arg && Node.isStringLiteral(arg)) {
        return arg.getLiteralValue();
      }
    }

    return undefined;
  }

  /**
   * Get the receiver object name for a method call
   */
  getReceiverName(callExpr: CallExpression): string | undefined {
    const expr = callExpr.getExpression();
    
    if (Node.isPropertyAccessExpression(expr)) {
      const receiver = expr.getExpression();
      if (Node.isIdentifier(receiver)) {
        return receiver.getText();
      }
    }

    return undefined;
  }

  /**
   * Check if a node is inside a specific function/method
   */
  getEnclosingFunction(node: Node): Node | undefined {
    return node.getFirstAncestor((ancestor) =>
      Node.isFunctionDeclaration(ancestor) ||
      Node.isFunctionExpression(ancestor) ||
      Node.isArrowFunction(ancestor) ||
      Node.isMethodDeclaration(ancestor)
    );
  }

  /**
   * Extract code snippet around a node
   */
  extractSnippet(node: Node, contextLines = 2): string {
    const sourceFile = node.getSourceFile();
    const fullText = sourceFile.getFullText();
    const lines = fullText.split('\n');
    
    const location = this.getLocation(node);
    const startLine = Math.max(0, location.startLine - 1 - contextLines);
    const endLine = Math.min(lines.length, location.endLine + contextLines);
    
    return lines.slice(startLine, endLine).join('\n');
  }

  /**
   * Check if node represents user input source
   */
  isUserInputSource(callExpr: CallExpression): boolean {
    const funcName = this.getFunctionName(callExpr);
    const receiverName = this.getReceiverName(callExpr);
    
    // Common user input patterns
    const userInputPatterns = [
      // Express.js
      { receiver: 'req', methods: ['body', 'query', 'params', 'headers', 'cookies'] },
      // Koa
      { receiver: 'ctx', methods: ['request', 'query', 'params'] },
      // DOM
      { receiver: 'document', methods: ['getElementById', 'querySelector', 'querySelectorAll'] },
      // Forms
      { receiver: undefined, methods: ['prompt', 'confirm'] },
    ];

    for (const pattern of userInputPatterns) {
      if (pattern.receiver && receiverName !== pattern.receiver) continue;
      if (funcName && pattern.methods.includes(funcName)) {
        return true;
      }
    }

    // Property access on request objects
    const expr = callExpr.getExpression();
    if (Node.isPropertyAccessExpression(expr)) {
      const receiver = expr.getExpression();
      if (Node.isPropertyAccessExpression(receiver)) {
        const text = receiver.getText();
        if (text.includes('req.') || text.includes('request.') || text.includes('ctx.')) {
          return true;
        }
      }
    }

    return false;
  }

  /**
   * Check if node is a dangerous sink
   */
  isDangerousSink(callExpr: CallExpression): { isDangerous: boolean; category?: string } {
    const funcName = this.getFunctionName(callExpr);
    const receiverName = this.getReceiverName(callExpr);

    const dangerousSinks: Record<string, { receiver?: string; category: string }[]> = {
      // SQL
      query: [
        { receiver: 'db', category: 'sql-query' },
        { receiver: 'connection', category: 'sql-query' },
        { receiver: 'pool', category: 'sql-query' },
      ],
      execute: [{ receiver: 'db', category: 'sql-query' }],
      raw: [{ receiver: 'knex', category: 'sql-query' }],
      
      // Command execution
      exec: [
        { receiver: 'child_process', category: 'command-exec' },
        { receiver: undefined, category: 'command-exec' },
      ],
      execSync: [{ receiver: 'child_process', category: 'command-exec' }],
      spawn: [{ receiver: 'child_process', category: 'command-exec' }],
      
      // File system
      readFile: [{ receiver: 'fs', category: 'file-read' }],
      readFileSync: [{ receiver: 'fs', category: 'file-read' }],
      writeFile: [{ receiver: 'fs', category: 'file-write' }],
      writeFileSync: [{ receiver: 'fs', category: 'file-write' }],
      
      // Eval/code execution
      eval: [{ receiver: undefined, category: 'eval' }],
      Function: [{ receiver: undefined, category: 'eval' }],
      
      // HTML output
      innerHTML: [{ receiver: undefined, category: 'html-output' }],
      html: [{ receiver: undefined, category: 'html-output' }],
      render: [{ receiver: 'res', category: 'html-output' }],
      send: [{ receiver: 'res', category: 'html-output' }],
      
      // Redirects
      redirect: [{ receiver: 'res', category: 'redirect' }],
      
      // Deserialization
      parse: [{ receiver: 'JSON', category: 'deserialization' }],
      deserialize: [{ receiver: undefined, category: 'deserialization' }],
    };

    if (funcName && dangerousSinks[funcName]) {
      for (const sink of dangerousSinks[funcName]) {
        if (!sink.receiver || sink.receiver === receiverName) {
          return { isDangerous: true, category: sink.category };
        }
      }
    }

    return { isDangerous: false };
  }

  /**
   * Clear cache for a file
   */
  invalidateCache(filePath: string): void {
    this.cache.delete(filePath);
    const sourceFile = this.project.getSourceFile(filePath);
    if (sourceFile) {
      this.project.removeSourceFile(sourceFile);
    }
  }

  /**
   * Clear all caches
   */
  clearCache(): void {
    this.cache.clear();
    for (const sourceFile of this.project.getSourceFiles()) {
      this.project.removeSourceFile(sourceFile);
    }
  }

  /**
   * Get project instance for advanced usage
   */
  getProject(): Project {
    return this.project;
  }
}

/**
 * Singleton instance
 */
let parserInstance: ASTParser | null = null;

/**
 * Get or create AST parser instance
 */
export function getASTParser(tsConfigPath?: string): ASTParser {
  if (!parserInstance) {
    parserInstance = new ASTParser(tsConfigPath);
  }
  return parserInstance;
}

/**
 * Reset parser instance (for testing)
 */
export function resetASTParser(): void {
  if (parserInstance) {
    parserInstance.clearCache();
    parserInstance = null;
  }
}
