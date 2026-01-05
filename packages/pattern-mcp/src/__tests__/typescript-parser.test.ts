/**
 * @fileoverview TypeScript parser tests
 * @traceability TSK-PATTERN-001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { TypeScriptParser } from '../extractor/typescript-parser.js';

describe('TypeScriptParser', () => {
  let parser: TypeScriptParser;

  beforeEach(() => {
    parser = new TypeScriptParser();
  });

  describe('parse', () => {
    it('should parse simple variable declaration', () => {
      const source = 'const x = 1;';
      const ast = parser.parse(source);

      expect(ast.type).toBe('SourceFile');
      expect(ast.children.length).toBeGreaterThan(0);
    });

    it('should parse function declaration', () => {
      const source = `
function greet(name: string): string {
  return 'Hello, ' + name;
}
`;
      const ast = parser.parse(source);

      expect(ast.type).toBe('SourceFile');
      // Should contain FunctionDeclaration
      const hasFunctionDecl = JSON.stringify(ast).includes('FunctionDeclaration');
      expect(hasFunctionDecl).toBe(true);
    });

    it('should parse class declaration', () => {
      const source = `
class Person {
  name: string;
  
  constructor(name: string) {
    this.name = name;
  }
  
  greet(): string {
    return 'Hello, ' + this.name;
  }
}
`;
      const ast = parser.parse(source);

      expect(ast.type).toBe('SourceFile');
      const hasClassDecl = JSON.stringify(ast).includes('ClassDeclaration');
      expect(hasClassDecl).toBe(true);
    });

    it('should include position information', () => {
      const source = 'const x = 1;';
      const ast = parser.parse(source);

      expect(ast.startPosition).toBeDefined();
      expect(ast.endPosition).toBeDefined();
      expect(ast.startPosition.row).toBe(0);
    });

    it('should include identifier values', () => {
      const source = 'const myVariable = 42;';
      const ast = parser.parse(source);

      const json = JSON.stringify(ast);
      expect(json).toContain('myVariable');
    });
  });

  describe('getFunctions', () => {
    it('should extract function declarations', () => {
      const source = `
function add(a: number, b: number): number {
  return a + b;
}

function subtract(a: number, b: number): number {
  return a - b;
}
`;
      const functions = parser.getFunctions(source);

      expect(functions).toHaveLength(2);
      expect(functions[0].name).toBe('add');
      expect(functions[0].parameters).toHaveLength(2);
      expect(functions[1].name).toBe('subtract');
    });

    it('should extract arrow functions with names', () => {
      const source = `
const multiply = (a: number, b: number): number => a * b;
`;
      const functions = parser.getFunctions(source);

      expect(functions.length).toBeGreaterThan(0);
      expect(functions.some(f => f.name === 'multiply')).toBe(true);
    });

    it('should extract method declarations', () => {
      const source = `
class Calculator {
  add(a: number, b: number): number {
    return a + b;
  }
}
`;
      const functions = parser.getFunctions(source);

      expect(functions.some(f => f.name === 'add')).toBe(true);
    });
  });

  describe('getClasses', () => {
    it('should extract class information', () => {
      const source = `
class Person {
  name: string;
  age: number;
  
  greet(): void {}
  getName(): string { return this.name; }
}
`;
      const classes = parser.getClasses(source);

      expect(classes).toHaveLength(1);
      expect(classes[0].name).toBe('Person');
      expect(classes[0].properties).toContain('name');
      expect(classes[0].properties).toContain('age');
      expect(classes[0].methods).toContain('greet');
      expect(classes[0].methods).toContain('getName');
    });
  });

  describe('getImports', () => {
    it('should extract import statements', () => {
      const source = `
import { readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import type { Config } from './types';
`;
      const imports = parser.getImports(source);

      expect(imports.length).toBeGreaterThanOrEqual(2);
      
      const fsImport = imports.find(i => i.module === 'node:fs/promises');
      expect(fsImport).toBeDefined();
      expect(fsImport?.namedImports).toContain('readFile');
      expect(fsImport?.namedImports).toContain('writeFile');

      const pathImport = imports.find(i => i.module === 'node:path');
      expect(pathImport).toBeDefined();
      expect(pathImport?.defaultImport).toBe('path');
    });
  });
});
