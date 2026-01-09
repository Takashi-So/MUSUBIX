/**
 * Type declarations for optional tree-sitter dependencies
 * These modules are dynamically imported and may not be installed
 */

declare module 'tree-sitter' {
  class Parser {
    setLanguage(language: unknown): void;
    parse(input: string): SyntaxTree;
  }

  interface SyntaxTree {
    rootNode: SyntaxNode;
  }

  interface SyntaxNode {
    type: string;
    text: string;
    startPosition: { row: number; column: number };
    endPosition: { row: number; column: number };
    children: SyntaxNode[];
    namedChildren: SyntaxNode[];
    childForFieldName(name: string): SyntaxNode | null;
    parent: SyntaxNode | null;
  }

  export default Parser;
  export { SyntaxTree, SyntaxNode };
}

declare module 'tree-sitter-typescript' {
  interface Languages {
    typescript: unknown;
    tsx: unknown;
  }
  const languages: Languages;
  export default languages;
}

declare module 'tree-sitter-python' {
  const language: unknown;
  export default language;
}

declare module 'better-sqlite3' {
  interface Database {
    prepare(sql: string): Statement;
    exec(sql: string): void;
    close(): void;
    transaction<T>(fn: () => T): () => T;
  }

  interface Statement {
    run(...params: unknown[]): { changes: number; lastInsertRowid: number | bigint };
    get(...params: unknown[]): unknown;
    all(...params: unknown[]): unknown[];
  }

  class BetterSqlite3 implements Database {
    constructor(filename: string, options?: unknown);
    prepare(sql: string): Statement;
    exec(sql: string): void;
    close(): void;
    transaction<T>(fn: () => T): () => T;
  }

  export default BetterSqlite3;
  export { Database, Statement };
}
