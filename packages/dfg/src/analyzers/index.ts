/**
 * DFG/CFG Analyzers
 *
 * TypeScript AST to Data Flow Graph and Control Flow Graph conversion
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-dfg/analyzers
 */

import * as ts from 'typescript';
import type {
  DFGNode,
  DFGEdge,
  CFGBlock,
  DataFlowGraph,
  ControlFlowGraph,
  DFGAnalysisOptions,
  CFGAnalysisOptions,
  SourceLocation,
} from '../types/index.js';
import {
  DFGBuilder,
  DFGAnalyzer,
  CFGBuilder,
  CFGAnalyzer,
} from '../graph/index.js';

// ============================================================================
// Data Flow Analyzer
// ============================================================================

/**
 * Data Flow Graph analyzer for TypeScript/JavaScript code
 *
 * @example
 * ```typescript
 * const analyzer = new DataFlowAnalyzer();
 * const dfg = await analyzer.analyze('src/user-service.ts');
 *
 * // Query dependencies
 * const deps = dfg.getDataDependencies('userId');
 * ```
 *
 * @traces REQ-DFG-001
 */
export class DataFlowAnalyzer {
  private options: DFGAnalysisOptions;

  constructor(options: Partial<DFGAnalysisOptions> = {}) {
    this.options = {
      interprocedural: options.interprocedural ?? false,
      trackAliasing: options.trackAliasing ?? true,
      includeTypes: options.includeTypes ?? true,
      maxDepth: options.maxDepth ?? 10,
      timeout: options.timeout ?? 30000,
      includeExternal: options.includeExternal ?? false,
    };
  }

  /**
   * Analyze a TypeScript/JavaScript file
   */
  async analyze(filePath: string): Promise<DataFlowGraph> {
    const fs = await import('fs');
    const sourceCode = fs.readFileSync(filePath, 'utf-8');
    return this.analyzeSource(sourceCode, filePath);
  }

  /**
   * Analyze source code directly
   */
  analyzeSource(sourceCode: string, filePath: string): DataFlowGraph {
    const sourceFile = ts.createSourceFile(
      filePath,
      sourceCode,
      ts.ScriptTarget.Latest,
      true,
      ts.ScriptKind.TS
    );

    const builder = new DFGBuilder(filePath);
    const scopeStack: string[] = ['module'];
    const variableMap = new Map<string, string>(); // variable name -> node id

    const visit = (node: ts.Node): void => {
      const location = this.getSourceLocation(sourceFile, node);

      switch (node.kind) {
        case ts.SyntaxKind.VariableDeclaration:
          this.handleVariableDeclaration(
            node as ts.VariableDeclaration,
            builder,
            scopeStack,
            variableMap,
            location
          );
          break;

        case ts.SyntaxKind.Parameter:
          this.handleParameter(
            node as ts.ParameterDeclaration,
            builder,
            scopeStack,
            variableMap,
            location
          );
          break;

        case ts.SyntaxKind.FunctionDeclaration:
        case ts.SyntaxKind.FunctionExpression:
        case ts.SyntaxKind.ArrowFunction:
          this.handleFunction(
            node as ts.FunctionLikeDeclaration,
            builder,
            scopeStack,
            variableMap,
            location,
            visit
          );
          return; // Don't recurse automatically, handled in handleFunction

        case ts.SyntaxKind.ClassDeclaration:
          this.handleClass(
            node as ts.ClassDeclaration,
            builder,
            scopeStack,
            location,
            visit
          );
          return;

        case ts.SyntaxKind.CallExpression:
          this.handleCallExpression(
            node as ts.CallExpression,
            builder,
            scopeStack,
            variableMap,
            location
          );
          break;

        case ts.SyntaxKind.BinaryExpression:
          this.handleBinaryExpression(
            node as ts.BinaryExpression,
            builder,
            scopeStack,
            variableMap,
            location
          );
          break;

        case ts.SyntaxKind.Identifier:
          this.handleIdentifier(
            node as ts.Identifier,
            builder,
            scopeStack,
            variableMap,
            location
          );
          break;

        case ts.SyntaxKind.ReturnStatement:
          this.handleReturn(
            node as ts.ReturnStatement,
            builder,
            scopeStack,
            variableMap,
            location
          );
          break;
      }

      ts.forEachChild(node, visit);
    };

    ts.forEachChild(sourceFile, visit);

    return builder.build();
  }

  private handleVariableDeclaration(
    node: ts.VariableDeclaration,
    builder: DFGBuilder,
    scopeStack: string[],
    variableMap: Map<string, string>,
    location: SourceLocation
  ): void {
    const name = node.name.getText();
    const nodeId = builder.generateNodeId('var');
    const scope = scopeStack.join('.');

    const dfgNode: DFGNode = {
      id: nodeId,
      type: 'variable',
      name,
      location,
      scope,
      metadata: {
        isConst:
          (node.parent as ts.VariableDeclarationList).flags &
          ts.NodeFlags.Const,
      },
    };

    if (this.options.includeTypes && node.type) {
      dfgNode.typeInfo = {
        name: node.type.getText(),
        fullType: node.type.getText(),
        nullable: false,
        isArray: ts.isArrayTypeNode(node.type),
        isPromise: node.type.getText().startsWith('Promise'),
      };
    }

    builder.addNode(dfgNode);
    variableMap.set(`${scope}.${name}`, nodeId);

    // Handle initializer
    if (node.initializer) {
      this.createDataFlowEdges(
        node.initializer,
        nodeId,
        builder,
        scopeStack,
        variableMap
      );
    }
  }

  private handleParameter(
    node: ts.ParameterDeclaration,
    builder: DFGBuilder,
    scopeStack: string[],
    variableMap: Map<string, string>,
    location: SourceLocation
  ): void {
    const name = node.name.getText();
    const nodeId = builder.generateNodeId('param');
    const scope = scopeStack.join('.');

    const dfgNode: DFGNode = {
      id: nodeId,
      type: 'parameter',
      name,
      location,
      scope,
      metadata: {
        isOptional: !!node.questionToken,
        isRest: !!node.dotDotDotToken,
      },
    };

    builder.addNode(dfgNode);
    builder.addEntryPoint(nodeId);
    variableMap.set(`${scope}.${name}`, nodeId);
  }

  private handleFunction(
    node: ts.FunctionLikeDeclaration,
    builder: DFGBuilder,
    scopeStack: string[],
    _variableMap: Map<string, string>,
    location: SourceLocation,
    visit: (n: ts.Node) => void
  ): void {
    const name =
      node.name?.getText() || `anonymous_${builder.generateNodeId('fn')}`;
    const nodeId = builder.generateNodeId('fn');
    const parentScope = scopeStack.join('.');

    const dfgNode: DFGNode = {
      id: nodeId,
      type: 'function',
      name,
      location,
      scope: parentScope,
      metadata: {
        isAsync: !!node.modifiers?.some(
          (m) => m.kind === ts.SyntaxKind.AsyncKeyword
        ),
        isGenerator: !!node.asteriskToken,
        parameterCount: node.parameters.length,
      },
    };

    builder.addNode(dfgNode);
    builder.addEntryPoint(nodeId);

    // Push function scope and visit children
    scopeStack.push(name);

    // Visit parameters
    node.parameters.forEach((param) => visit(param));

    // Visit body
    if (node.body) {
      ts.forEachChild(node.body, visit);
    }

    scopeStack.pop();
  }

  private handleClass(
    node: ts.ClassDeclaration,
    builder: DFGBuilder,
    scopeStack: string[],
    location: SourceLocation,
    visit: (n: ts.Node) => void
  ): void {
    const name = node.name?.getText() || 'AnonymousClass';
    const nodeId = builder.generateNodeId('class');
    const scope = scopeStack.join('.');

    const dfgNode: DFGNode = {
      id: nodeId,
      type: 'class',
      name,
      location,
      scope,
      metadata: {
        isAbstract: !!node.modifiers?.some(
          (m) => m.kind === ts.SyntaxKind.AbstractKeyword
        ),
        memberCount: node.members.length,
      },
    };

    builder.addNode(dfgNode);

    scopeStack.push(name);
    node.members.forEach((member) => visit(member));
    scopeStack.pop();
  }

  private handleCallExpression(
    node: ts.CallExpression,
    builder: DFGBuilder,
    scopeStack: string[],
    variableMap: Map<string, string>,
    location: SourceLocation
  ): void {
    const callName = node.expression.getText();
    const nodeId = builder.generateNodeId('call');
    const scope = scopeStack.join('.');

    const dfgNode: DFGNode = {
      id: nodeId,
      type: 'call',
      name: callName,
      location,
      scope,
      metadata: {
        argumentCount: node.arguments.length,
      },
    };

    builder.addNode(dfgNode);

    // Create edges from arguments
    node.arguments.forEach((arg, _index) => {
      this.createDataFlowEdges(arg, nodeId, builder, scopeStack, variableMap);
    });
  }

  private handleBinaryExpression(
    node: ts.BinaryExpression,
    builder: DFGBuilder,
    scopeStack: string[],
    variableMap: Map<string, string>,
    location: SourceLocation
  ): void {
    // Handle assignments
    if (
      node.operatorToken.kind === ts.SyntaxKind.EqualsToken ||
      node.operatorToken.kind === ts.SyntaxKind.PlusEqualsToken ||
      node.operatorToken.kind === ts.SyntaxKind.MinusEqualsToken
    ) {
      const leftName = node.left.getText();
      const scope = scopeStack.join('.');
      const existingNodeId = variableMap.get(`${scope}.${leftName}`);

      if (existingNodeId) {
        // Create assignment node
        const assignId = builder.generateNodeId('assign');
        const assignNode: DFGNode = {
          id: assignId,
          type: 'assignment',
          name: leftName,
          location,
          scope,
          metadata: {
            operator: node.operatorToken.getText(),
          },
        };
        builder.addNode(assignNode);

        // Edge from right side to assignment
        this.createDataFlowEdges(
          node.right,
          assignId,
          builder,
          scopeStack,
          variableMap
        );

        // Edge from assignment to variable
        const edge: DFGEdge = {
          id: builder.generateEdgeId('e'),
          type: 'def-use',
          source: assignId,
          target: existingNodeId,
          weight: 1,
          metadata: {},
        };
        builder.addEdge(edge);
      }
    }
  }

  private handleIdentifier(
    node: ts.Identifier,
    builder: DFGBuilder,
    scopeStack: string[],
    variableMap: Map<string, string>,
    location: SourceLocation
  ): void {
    // Skip if parent is a declaration (handled separately)
    const parent = node.parent;
    if (
      ts.isVariableDeclaration(parent) ||
      ts.isParameter(parent) ||
      ts.isFunctionDeclaration(parent) ||
      ts.isClassDeclaration(parent)
    ) {
      return;
    }

    const name = node.getText();
    const scope = scopeStack.join('.');

    // Look up variable in current or parent scopes
    let varNodeId: string | undefined;
    const scopeParts = scope.split('.');

    for (let i = scopeParts.length; i > 0; i--) {
      const checkScope = scopeParts.slice(0, i).join('.');
      varNodeId = variableMap.get(`${checkScope}.${name}`);
      if (varNodeId) break;
    }

    // If not found, might be external reference
    if (!varNodeId && this.options.includeExternal) {
      const externalId = builder.generateNodeId('ext');
      const externalNode: DFGNode = {
        id: externalId,
        type: 'variable',
        name,
        location,
        scope: 'external',
        metadata: { isExternal: true },
      };
      builder.addNode(externalNode);
      varNodeId = externalId;
    }
  }

  private handleReturn(
    node: ts.ReturnStatement,
    builder: DFGBuilder,
    scopeStack: string[],
    variableMap: Map<string, string>,
    location: SourceLocation
  ): void {
    const nodeId = builder.generateNodeId('ret');
    const scope = scopeStack.join('.');

    const dfgNode: DFGNode = {
      id: nodeId,
      type: 'return',
      name: 'return',
      location,
      scope,
      metadata: {},
    };

    builder.addNode(dfgNode);
    builder.addExitPoint(nodeId);

    if (node.expression) {
      this.createDataFlowEdges(
        node.expression,
        nodeId,
        builder,
        scopeStack,
        variableMap
      );
    }
  }

  private createDataFlowEdges(
    expr: ts.Expression,
    targetNodeId: string,
    builder: DFGBuilder,
    scopeStack: string[],
    variableMap: Map<string, string>
  ): void {
    const scope = scopeStack.join('.');

    if (ts.isIdentifier(expr)) {
      const name = expr.getText();

      // Look up in scope chain
      let sourceNodeId: string | undefined;
      const scopeParts = scope.split('.');

      for (let i = scopeParts.length; i > 0; i--) {
        const checkScope = scopeParts.slice(0, i).join('.');
        sourceNodeId = variableMap.get(`${checkScope}.${name}`);
        if (sourceNodeId) break;
      }

      if (sourceNodeId) {
        const edge: DFGEdge = {
          id: builder.generateEdgeId('e'),
          type: 'data-dep',
          source: sourceNodeId,
          target: targetNodeId,
          weight: 1,
          metadata: {},
        };
        builder.addEdge(edge);
      }
    } else if (ts.isBinaryExpression(expr)) {
      this.createDataFlowEdges(
        expr.left,
        targetNodeId,
        builder,
        scopeStack,
        variableMap
      );
      this.createDataFlowEdges(
        expr.right,
        targetNodeId,
        builder,
        scopeStack,
        variableMap
      );
    } else if (ts.isCallExpression(expr)) {
      // Call result flows to target
      const callNodeId = builder.generateNodeId('call');
      const location = this.getSourceLocation(
        expr.getSourceFile(),
        expr
      );

      const callNode: DFGNode = {
        id: callNodeId,
        type: 'call',
        name: expr.expression.getText(),
        location,
        scope,
        metadata: {},
      };
      builder.addNode(callNode);

      const edge: DFGEdge = {
        id: builder.generateEdgeId('e'),
        type: 'call-return',
        source: callNodeId,
        target: targetNodeId,
        weight: 1,
        metadata: {},
      };
      builder.addEdge(edge);
    }
  }

  private getSourceLocation(
    sourceFile: ts.SourceFile,
    node: ts.Node
  ): SourceLocation {
    const start = sourceFile.getLineAndCharacterOfPosition(node.getStart());
    const end = sourceFile.getLineAndCharacterOfPosition(node.getEnd());

    return {
      filePath: sourceFile.fileName,
      startLine: start.line + 1,
      startColumn: start.character,
      endLine: end.line + 1,
      endColumn: end.character,
    };
  }

  /**
   * Create analyzer for a built graph
   */
  createAnalyzer(graph: DataFlowGraph): DFGAnalyzer {
    return new DFGAnalyzer(graph);
  }
}

// ============================================================================
// Control Flow Analyzer
// ============================================================================

/**
 * Control Flow Graph analyzer for TypeScript/JavaScript code
 *
 * @example
 * ```typescript
 * const analyzer = new ControlFlowAnalyzer();
 * const cfg = await analyzer.analyze('src/user-service.ts', 'getUserById');
 *
 * // Get cyclomatic complexity
 * const complexity = cfg.getCyclomaticComplexity();
 * ```
 *
 * @traces REQ-DFG-002
 */
export class ControlFlowAnalyzer {
  private options: CFGAnalysisOptions;

  constructor(options: Partial<CFGAnalysisOptions> = {}) {
    this.options = {
      computeDominators: options.computeDominators ?? true,
      computePostDominators: options.computePostDominators ?? true,
      identifyLoops: options.identifyLoops ?? true,
      includeExceptions: options.includeExceptions ?? true,
      maxDepth: options.maxDepth ?? 10,
      timeout: options.timeout ?? 30000,
    };
  }

  /**
   * Analyze a specific function in a file
   */
  async analyze(
    filePath: string,
    functionName?: string
  ): Promise<ControlFlowGraph[]> {
    const fs = await import('fs');
    const sourceCode = fs.readFileSync(filePath, 'utf-8');
    return this.analyzeSource(sourceCode, filePath, functionName);
  }

  /**
   * Analyze source code directly
   */
  analyzeSource(
    sourceCode: string,
    filePath: string,
    functionName?: string
  ): ControlFlowGraph[] {
    const sourceFile = ts.createSourceFile(
      filePath,
      sourceCode,
      ts.ScriptTarget.Latest,
      true,
      ts.ScriptKind.TS
    );

    const graphs: ControlFlowGraph[] = [];

    const visit = (node: ts.Node): void => {
      if (
        ts.isFunctionDeclaration(node) ||
        ts.isMethodDeclaration(node) ||
        ts.isArrowFunction(node) ||
        ts.isFunctionExpression(node)
      ) {
        const name = this.getFunctionName(node);
        if (!functionName || name === functionName) {
          const cfg = this.analyzeFunction(node, sourceFile, filePath, name);
          graphs.push(cfg);
        }
      }

      ts.forEachChild(node, visit);
    };

    ts.forEachChild(sourceFile, visit);
    return graphs;
  }

  private getFunctionName(node: ts.Node): string {
    if (ts.isFunctionDeclaration(node) && node.name) {
      return node.name.getText();
    }
    if (ts.isMethodDeclaration(node) && node.name) {
      return node.name.getText();
    }
    return `anonymous_${Math.random().toString(36).substr(2, 9)}`;
  }

  private analyzeFunction(
    node: ts.FunctionLikeDeclaration,
    sourceFile: ts.SourceFile,
    filePath: string,
    functionName: string
  ): ControlFlowGraph {
    const builder = new CFGBuilder(functionName, filePath);
    let loopDepth = 0;

    // Create entry block
    const entryId = builder.generateBlockId('entry');
    const entryBlock: CFGBlock = {
      id: entryId,
      type: 'entry',
      label: 'entry',
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth: 0,
      location: this.getSourceLocation(sourceFile, node),
    };
    builder.addBlock(entryBlock);
    builder.setEntryBlock(entryId);

    // Create exit block
    const exitId = builder.generateBlockId('exit');
    const exitBlock: CFGBlock = {
      id: exitId,
      type: 'exit',
      label: 'exit',
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth: 0,
      location: this.getSourceLocation(sourceFile, node),
    };
    builder.addBlock(exitBlock);
    builder.addExitBlock(exitId);

    const processStatement = (
      stmt: ts.Statement,
      blockId: string
    ): string | null => {
      const location = this.getSourceLocation(sourceFile, stmt);

      if (ts.isIfStatement(stmt)) {
        return this.processIfStatement(
          stmt,
          blockId,
          exitId,
          builder,
          sourceFile,
          loopDepth,
          processStatement
        );
      }

      if (ts.isWhileStatement(stmt) || ts.isForStatement(stmt)) {
        loopDepth++;
        const result = this.processLoopStatement(
          stmt,
          blockId,
          exitId,
          builder,
          sourceFile,
          loopDepth,
          processStatement
        );
        loopDepth--;
        return result;
      }

      if (ts.isReturnStatement(stmt)) {
        // Add return to current block and connect to exit
        const block = builder.getBlock(blockId);
        if (block) {
          block.statements.push({
            index: block.statements.length,
            type: 'return',
            text: stmt.getText(),
            location,
          });
        }

        const edgeId = builder.generateEdgeId('e');
        builder.addEdge({
          id: edgeId,
          type: 'return',
          source: blockId,
          target: exitId,
          isBackEdge: false,
        });

        return null; // No continuation
      }

      if (ts.isTryStatement(stmt) && this.options.includeExceptions) {
        return this.processTryStatement(
          stmt,
          blockId,
          exitId,
          builder,
          sourceFile,
          loopDepth,
          processStatement
        );
      }

      // Regular statement - add to current block
      const block = builder.getBlock(blockId);
      if (block) {
        block.statements.push({
          index: block.statements.length,
          type: stmt.kind.toString(),
          text: stmt.getText().slice(0, 100), // Truncate long statements
          location,
        });
      }

      return blockId;
    };

    // Process function body
    if (node.body) {
      if (ts.isBlock(node.body)) {
        let blockId: string | null = entryId;
        for (const stmt of node.body.statements) {
          if (blockId) {
            blockId = processStatement(stmt, blockId);
          }
        }

        // Connect last block to exit if not already connected
        if (blockId && blockId !== exitId) {
          const block = builder.getBlock(blockId);
          if (block && !block.successors.includes(exitId)) {
            const edgeId = builder.generateEdgeId('e');
            builder.addEdge({
              id: edgeId,
              type: 'sequential',
              source: blockId,
              target: exitId,
              isBackEdge: false,
            });
          }
        }
      }
    }

    return builder.build();
  }

  private processIfStatement(
    stmt: ts.IfStatement,
    blockId: string,
    exitId: string,
    builder: CFGBuilder,
    sourceFile: ts.SourceFile,
    loopDepth: number,
    processStatement: (s: ts.Statement, b: string) => string | null
  ): string | null {
    const location = this.getSourceLocation(sourceFile, stmt);

    // Create conditional block
    const condBlockId = builder.generateBlockId('cond');
    const condBlock: CFGBlock = {
      id: condBlockId,
      type: 'conditional',
      label: `if (${stmt.expression.getText()})`,
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth,
      location,
    };
    builder.addBlock(condBlock);

    // Connect from previous block
    builder.addEdge({
      id: builder.generateEdgeId('e'),
      type: 'sequential',
      source: blockId,
      target: condBlockId,
      isBackEdge: false,
    });

    // Create merge block
    const mergeBlockId = builder.generateBlockId('merge');
    const mergeBlock: CFGBlock = {
      id: mergeBlockId,
      type: 'basic',
      label: 'merge',
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth,
      location,
    };
    builder.addBlock(mergeBlock);

    // Process then branch
    const thenBlockId = builder.generateBlockId('then');
    const thenBlock: CFGBlock = {
      id: thenBlockId,
      type: 'basic',
      label: 'then',
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth,
      location: this.getSourceLocation(sourceFile, stmt.thenStatement),
    };
    builder.addBlock(thenBlock);

    builder.addEdge({
      id: builder.generateEdgeId('e'),
      type: 'conditional-true',
      source: condBlockId,
      target: thenBlockId,
      condition: stmt.expression.getText(),
      isBackEdge: false,
    });

    let thenEndBlock: string | null = thenBlockId;
    if (ts.isBlock(stmt.thenStatement)) {
      for (const s of stmt.thenStatement.statements) {
        if (thenEndBlock) {
          thenEndBlock = processStatement(s, thenEndBlock);
        }
      }
    }

    if (thenEndBlock) {
      builder.addEdge({
        id: builder.generateEdgeId('e'),
        type: 'sequential',
        source: thenEndBlock,
        target: mergeBlockId,
        isBackEdge: false,
      });
    }

    // Process else branch
    if (stmt.elseStatement) {
      const elseBlockId = builder.generateBlockId('else');
      const elseBlock: CFGBlock = {
        id: elseBlockId,
        type: 'basic',
        label: 'else',
        statements: [],
        predecessors: [],
        successors: [],
        loopDepth,
        location: this.getSourceLocation(sourceFile, stmt.elseStatement),
      };
      builder.addBlock(elseBlock);

      builder.addEdge({
        id: builder.generateEdgeId('e'),
        type: 'conditional-false',
        source: condBlockId,
        target: elseBlockId,
        condition: `!(${stmt.expression.getText()})`,
        isBackEdge: false,
      });

      let elseEndBlock: string | null = elseBlockId;
      if (ts.isBlock(stmt.elseStatement)) {
        for (const s of stmt.elseStatement.statements) {
          if (elseEndBlock) {
            elseEndBlock = processStatement(s, elseEndBlock);
          }
        }
      } else if (ts.isIfStatement(stmt.elseStatement)) {
        elseEndBlock = this.processIfStatement(
          stmt.elseStatement,
          elseBlockId,
          exitId,
          builder,
          sourceFile,
          loopDepth,
          processStatement
        );
      }

      if (elseEndBlock) {
        builder.addEdge({
          id: builder.generateEdgeId('e'),
          type: 'sequential',
          source: elseEndBlock,
          target: mergeBlockId,
          isBackEdge: false,
        });
      }
    } else {
      // No else - connect condition directly to merge
      builder.addEdge({
        id: builder.generateEdgeId('e'),
        type: 'conditional-false',
        source: condBlockId,
        target: mergeBlockId,
        isBackEdge: false,
      });
    }

    return mergeBlockId;
  }

  private processLoopStatement(
    stmt: ts.WhileStatement | ts.ForStatement,
    blockId: string,
    _exitId: string,
    builder: CFGBuilder,
    sourceFile: ts.SourceFile,
    loopDepth: number,
    processStatement: (s: ts.Statement, b: string) => string | null
  ): string | null {
    const location = this.getSourceLocation(sourceFile, stmt);

    // Create loop header
    const headerBlockId = builder.generateBlockId('loop_header');
    const headerBlock: CFGBlock = {
      id: headerBlockId,
      type: 'loop-header',
      label: ts.isWhileStatement(stmt)
        ? `while (${stmt.expression.getText()})`
        : `for (...)`,
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth,
      location,
    };
    builder.addBlock(headerBlock);

    builder.addEdge({
      id: builder.generateEdgeId('e'),
      type: 'sequential',
      source: blockId,
      target: headerBlockId,
      isBackEdge: false,
    });

    // Create loop body
    const bodyBlockId = builder.generateBlockId('loop_body');
    const bodyBlock: CFGBlock = {
      id: bodyBlockId,
      type: 'loop-body',
      label: 'loop body',
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth,
      location: this.getSourceLocation(sourceFile, stmt.statement),
    };
    builder.addBlock(bodyBlock);

    builder.addEdge({
      id: builder.generateEdgeId('e'),
      type: 'conditional-true',
      source: headerBlockId,
      target: bodyBlockId,
      condition: ts.isWhileStatement(stmt)
        ? stmt.expression.getText()
        : 'condition',
      isBackEdge: false,
    });

    // Process body statements
    let bodyEndBlock: string | null = bodyBlockId;
    if (ts.isBlock(stmt.statement)) {
      for (const s of stmt.statement.statements) {
        if (bodyEndBlock) {
          bodyEndBlock = processStatement(s, bodyEndBlock);
        }
      }
    }

    // Back edge from body to header
    if (bodyEndBlock) {
      builder.addEdge({
        id: builder.generateEdgeId('e'),
        type: 'loop-back',
        source: bodyEndBlock,
        target: headerBlockId,
        isBackEdge: true,
      });
    }

    // Create loop exit
    const exitBlockId = builder.generateBlockId('loop_exit');
    const loopExitBlock: CFGBlock = {
      id: exitBlockId,
      type: 'loop-exit',
      label: 'loop exit',
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth: loopDepth - 1,
      location,
    };
    builder.addBlock(loopExitBlock);

    builder.addEdge({
      id: builder.generateEdgeId('e'),
      type: 'loop-exit',
      source: headerBlockId,
      target: exitBlockId,
      isBackEdge: false,
    });

    return exitBlockId;
  }

  private processTryStatement(
    stmt: ts.TryStatement,
    blockId: string,
    _exitId: string,
    builder: CFGBuilder,
    sourceFile: ts.SourceFile,
    loopDepth: number,
    processStatement: (s: ts.Statement, b: string) => string | null
  ): string | null {
    const location = this.getSourceLocation(sourceFile, stmt);

    // Create try block
    const tryBlockId = builder.generateBlockId('try');
    const tryBlock: CFGBlock = {
      id: tryBlockId,
      type: 'try',
      label: 'try',
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth,
      location,
    };
    builder.addBlock(tryBlock);

    builder.addEdge({
      id: builder.generateEdgeId('e'),
      type: 'sequential',
      source: blockId,
      target: tryBlockId,
      isBackEdge: false,
    });

    // Process try body
    let tryEndBlock: string | null = tryBlockId;
    for (const s of stmt.tryBlock.statements) {
      if (tryEndBlock) {
        tryEndBlock = processStatement(s, tryEndBlock);
      }
    }

    // Create merge block after try-catch
    const mergeBlockId = builder.generateBlockId('try_merge');
    const mergeBlock: CFGBlock = {
      id: mergeBlockId,
      type: 'basic',
      label: 'try merge',
      statements: [],
      predecessors: [],
      successors: [],
      loopDepth,
      location,
    };
    builder.addBlock(mergeBlock);

    if (tryEndBlock) {
      builder.addEdge({
        id: builder.generateEdgeId('e'),
        type: 'sequential',
        source: tryEndBlock,
        target: mergeBlockId,
        isBackEdge: false,
      });
    }

    // Process catch clause
    if (stmt.catchClause) {
      const catchBlockId = builder.generateBlockId('catch');
      const catchBlock: CFGBlock = {
        id: catchBlockId,
        type: 'catch',
        label: 'catch',
        statements: [],
        predecessors: [],
        successors: [],
        loopDepth,
        location: this.getSourceLocation(sourceFile, stmt.catchClause),
      };
      builder.addBlock(catchBlock);

      // Exception edge from try to catch
      builder.addEdge({
        id: builder.generateEdgeId('e'),
        type: 'exception',
        source: tryBlockId,
        target: catchBlockId,
        isBackEdge: false,
      });

      let catchEndBlock: string | null = catchBlockId;
      for (const s of stmt.catchClause.block.statements) {
        if (catchEndBlock) {
          catchEndBlock = processStatement(s, catchEndBlock);
        }
      }

      if (catchEndBlock) {
        builder.addEdge({
          id: builder.generateEdgeId('e'),
          type: 'sequential',
          source: catchEndBlock,
          target: mergeBlockId,
          isBackEdge: false,
        });
      }
    }

    // Process finally clause
    if (stmt.finallyBlock) {
      const finallyBlockId = builder.generateBlockId('finally');
      const finallyBlock: CFGBlock = {
        id: finallyBlockId,
        type: 'finally',
        label: 'finally',
        statements: [],
        predecessors: [],
        successors: [],
        loopDepth,
        location: this.getSourceLocation(sourceFile, stmt.finallyBlock),
      };
      builder.addBlock(finallyBlock);

      // Connect merge to finally
      builder.addEdge({
        id: builder.generateEdgeId('e'),
        type: 'sequential',
        source: mergeBlockId,
        target: finallyBlockId,
        isBackEdge: false,
      });

      let finallyEndBlock: string | null = finallyBlockId;
      for (const s of stmt.finallyBlock.statements) {
        if (finallyEndBlock) {
          finallyEndBlock = processStatement(s, finallyEndBlock);
        }
      }

      return finallyEndBlock;
    }

    return mergeBlockId;
  }

  private getSourceLocation(
    sourceFile: ts.SourceFile,
    node: ts.Node
  ): SourceLocation {
    const start = sourceFile.getLineAndCharacterOfPosition(node.getStart());
    const end = sourceFile.getLineAndCharacterOfPosition(node.getEnd());

    return {
      filePath: sourceFile.fileName,
      startLine: start.line + 1,
      startColumn: start.character,
      endLine: end.line + 1,
      endColumn: end.character,
    };
  }

  /**
   * Create analyzer for a built graph
   */
  createAnalyzer(graph: ControlFlowGraph): CFGAnalyzer {
    return new CFGAnalyzer(graph);
  }
}

// Add getBlock method to CFGBuilder
declare module '../graph/index.js' {
  interface CFGBuilder {
    getBlock(blockId: string): CFGBlock | undefined;
  }
}

// Extend CFGBuilder prototype
(CFGBuilder.prototype as any).getBlock = function (
  blockId: string
): CFGBlock | undefined {
  return this.blocks.get(blockId);
};
