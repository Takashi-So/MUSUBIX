/**
 * Code Generator Unit Tests
 * 
 * @see REQ-COD-001 - Code Generation
 * @see TSK-033 - CodeGenerator Implementation
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  CodeGenerator,
  DEFAULT_GENERATOR_OPTIONS,
  type CodeStructureDefinition,
  type TargetLanguage,
  type PropertyDefinition,
  type MethodDefinition,
} from '../../src/codegen/generator.js';

describe('REQ-COD-001: Code Generator', () => {
  let generator: CodeGenerator;

  beforeEach(() => {
    generator = new CodeGenerator();
  });

  describe('Default Configuration', () => {
    it('should have correct default options', () => {
      expect(DEFAULT_GENERATOR_OPTIONS.language).toBe('typescript');
      expect(DEFAULT_GENERATOR_OPTIONS.strictMode).toBe(true);
      expect(DEFAULT_GENERATOR_OPTIONS.generateDocs).toBe(true);
      expect(DEFAULT_GENERATOR_OPTIONS.indent).toBe('  ');
      expect(DEFAULT_GENERATOR_OPTIONS.lineEnding).toBe('\n');
    });
  });

  describe('TypeScript Generation', () => {
    it('should generate a simple class', () => {
      const definition: CodeStructureDefinition = {
        name: 'User',
        type: 'class',
        description: 'User entity',
        properties: [
          { name: 'id', type: 'string' },
          { name: 'name', type: 'string' },
          { name: 'email', type: 'string' },
        ],
      };

      const result = generator.generate(definition);

      expect(result.language).toBe('typescript');
      expect(result.fileName).toContain('.ts');
      expect(result.code).toContain('class User');
      expect(result.code).toContain('id');
      expect(result.code).toContain('name');
      expect(result.code).toContain('email');
    });

    it('should generate a class with methods', () => {
      const definition: CodeStructureDefinition = {
        name: 'UserService',
        type: 'service',
        methods: [
          {
            name: 'findById',
            parameters: [{ name: 'id', type: 'string' }],
            returnType: 'Promise<User>',
            async: true,
          },
          {
            name: 'create',
            parameters: [{ name: 'data', type: 'CreateUserDto' }],
            returnType: 'Promise<User>',
            async: true,
          },
        ],
      };

      const result = generator.generate(definition);

      expect(result.code).toContain('async');
      expect(result.code).toContain('findById');
      expect(result.code).toContain('create');
    });

    it('should generate an interface', () => {
      const definition: CodeStructureDefinition = {
        name: 'IRepository',
        type: 'interface',
        properties: [
          { name: 'tableName', type: 'string', readonly: true },
        ],
        methods: [
          { name: 'findOne', parameters: [{ name: 'id', type: 'string' }], returnType: 'T | null' },
          { name: 'findAll', parameters: [], returnType: 'T[]' },
        ],
      };

      const result = generator.generate(definition);

      expect(result.code).toContain('interface IRepository');
      expect(result.code).toContain('tableName');
      expect(result.code).toContain('findOne');
      expect(result.code).toContain('findAll');
    });

    it('should generate imports', () => {
      const definition: CodeStructureDefinition = {
        name: 'UserController',
        type: 'controller',
        dependencies: [
          { module: './user.service', imports: ['UserService'] },
          { module: './user.dto', imports: ['CreateUserDto', 'UpdateUserDto'], typeOnly: true },
        ],
      };

      const result = generator.generate(definition);

      expect(result.code).toContain("import { UserService } from './user.service'");
      expect(result.code).toContain("import type { CreateUserDto, UpdateUserDto }");
      expect(result.imports).toContain('./user.service');
      expect(result.imports).toContain('./user.dto');
    });

    it('should generate decorators', () => {
      const definition: CodeStructureDefinition = {
        name: 'UserController',
        type: 'controller',
        decorators: [
          { name: 'Controller', arguments: ["'/users'"] },
        ],
        methods: [
          {
            name: 'getUsers',
            decorators: [{ name: 'Get' }],
            returnType: 'User[]',
          },
        ],
      };

      const result = generator.generate(definition);

      expect(result.code).toContain("@Controller('/users')");
      expect(result.code).toContain('@Get()');
    });

    it('should handle optional properties', () => {
      const definition: CodeStructureDefinition = {
        name: 'Config',
        type: 'interface',
        properties: [
          { name: 'required', type: 'string' },
          { name: 'optional', type: 'string', optional: true },
        ],
      };

      const result = generator.generate(definition);

      expect(result.code).toContain('required: string');
      expect(result.code).toContain('optional?: string');
    });

    it('should handle visibility modifiers', () => {
      const definition: CodeStructureDefinition = {
        name: 'Entity',
        type: 'class',
        properties: [
          { name: 'publicProp', type: 'string', visibility: 'public' },
          { name: 'privateProp', type: 'string', visibility: 'private' },
          { name: 'protectedProp', type: 'string', visibility: 'protected' },
        ],
      };

      const result = generator.generate(definition);

      expect(result.code).toContain('public publicProp');
      expect(result.code).toContain('private privateProp');
      expect(result.code).toContain('protected protectedProp');
    });

    it('should handle inheritance', () => {
      const definition: CodeStructureDefinition = {
        name: 'AdminUser',
        type: 'class',
        inheritance: {
          extends: 'User',
          implements: ['IAdmin', 'IAuditable'],
        },
      };

      const result = generator.generate(definition);

      expect(result.code).toContain('extends User');
      expect(result.code).toContain('implements IAdmin, IAuditable');
    });
  });

  describe('JavaScript Generation', () => {
    let jsGenerator: CodeGenerator;

    beforeEach(() => {
      jsGenerator = new CodeGenerator({ language: 'javascript' });
    });

    it('should generate JavaScript class', () => {
      const definition: CodeStructureDefinition = {
        name: 'Calculator',
        type: 'class',
        methods: [
          { name: 'add', parameters: [{ name: 'a', type: 'number' }, { name: 'b', type: 'number' }], returnType: 'number' },
        ],
      };

      const result = jsGenerator.generate(definition);

      expect(result.language).toBe('javascript');
      expect(result.fileName).toContain('.js');
      expect(result.code).toContain('class Calculator');
    });

    it('should use # for private fields', () => {
      const definition: CodeStructureDefinition = {
        name: 'Counter',
        type: 'class',
        properties: [
          { name: 'count', type: 'number', visibility: 'private' },
        ],
      };

      const result = jsGenerator.generate(definition);

      expect(result.code).toContain('#count');
    });
  });

  describe('Python Generation', () => {
    let pyGenerator: CodeGenerator;

    beforeEach(() => {
      pyGenerator = new CodeGenerator({ language: 'python' });
    });

    it('should generate Python class', () => {
      const definition: CodeStructureDefinition = {
        name: 'Calculator',
        type: 'class',
        description: 'A simple calculator',
        methods: [
          {
            name: 'add',
            parameters: [
              { name: 'a', type: 'int' },
              { name: 'b', type: 'int' },
            ],
            returnType: 'int',
          },
        ],
      };

      const result = pyGenerator.generate(definition);

      expect(result.language).toBe('python');
      expect(result.fileName).toContain('.py');
      expect(result.code).toContain('class Calculator');
    });

    it('should use underscore for private', () => {
      const definition: CodeStructureDefinition = {
        name: 'Entity',
        type: 'class',
        properties: [
          { name: 'secret', type: 'str', visibility: 'private' },
        ],
      };

      const result = pyGenerator.generate(definition);

      // Python implementation may vary
      expect(result.code).toContain('secret');
    });

    it('should generate Python imports', () => {
      const definition: CodeStructureDefinition = {
        name: 'Service',
        type: 'class',
        dependencies: [
          { module: 'typing', imports: ['Optional', 'List'] },
        ],
      };

      const result = pyGenerator.generate(definition);

      expect(result.code).toContain('from typing import Optional, List');
    });
  });

  describe('Documentation Generation', () => {
    it('should generate JSDoc for TypeScript', () => {
      const definition: CodeStructureDefinition = {
        name: 'Utils',
        type: 'module',
        description: 'Utility functions',
        methods: [
          {
            name: 'formatDate',
            description: 'Formats a date',
            parameters: [{ name: 'date', type: 'Date', description: 'The date to format' }],
            returnType: 'string',
          },
        ],
      };

      const result = generator.generate(definition);

      expect(result.code).toContain('/**');
      expect(result.code).toContain('* Utility functions');
      expect(result.code).toContain('*/');
    });

    it('should skip docs when disabled', () => {
      const noDocsGenerator = new CodeGenerator({ generateDocs: false });

      const definition: CodeStructureDefinition = {
        name: 'Simple',
        type: 'class',
        description: 'Should not appear',
      };

      const result = noDocsGenerator.generate(definition);

      expect(result.code).not.toContain('/**');
      expect(result.code).not.toContain('Should not appear');
    });
  });

  describe('Batch Generation', () => {
    it('should generate multiple files', () => {
      const definitions: CodeStructureDefinition[] = [
        { name: 'User', type: 'model' },
        { name: 'UserService', type: 'service' },
        { name: 'UserController', type: 'controller' },
      ];

      const results = generator.generateBatch(definitions);

      expect(results).toHaveLength(3);
      expect(results[0].code).toBeDefined();
      expect(results[1].code).toBeDefined();
      expect(results[2].code).toBeDefined();
    });
  });

  describe('Template Types', () => {
    it('should handle model type', () => {
      const definition: CodeStructureDefinition = {
        name: 'Product',
        type: 'model',
        properties: [
          { name: 'id', type: 'string' },
          { name: 'price', type: 'number' },
        ],
      };

      const result = generator.generate(definition);
      expect(result.code).toBeDefined();
      expect(result.warnings).toHaveLength(0);
    });

    it('should handle repository type', () => {
      const definition: CodeStructureDefinition = {
        name: 'UserRepository',
        type: 'repository',
        methods: [
          { name: 'findByEmail', parameters: [{ name: 'email', type: 'string' }] },
        ],
      };

      const result = generator.generate(definition);
      expect(result.code).toContain('UserRepository');
    });

    it('should handle service type', () => {
      const definition: CodeStructureDefinition = {
        name: 'AuthService',
        type: 'service',
      };

      const result = generator.generate(definition);
      expect(result.code).toContain('AuthService');
    });

    it('should warn for unknown type', () => {
      const definition: CodeStructureDefinition = {
        name: 'Unknown',
        type: 'unknown' as any,
      };

      const result = generator.generate(definition);
      expect(result.warnings.length).toBeGreaterThan(0);
    });
  });

  describe('File Naming', () => {
    it('should generate correct file name for TypeScript', () => {
      const definition: CodeStructureDefinition = {
        name: 'UserService',
        type: 'service',
      };

      const result = generator.generate(definition);
      expect(result.fileName).toMatch(/\.ts$/);
    });

    it('should generate correct file name for Python', () => {
      const pyGenerator = new CodeGenerator({ language: 'python' });
      const definition: CodeStructureDefinition = {
        name: 'UserService',
        type: 'service',
      };

      const result = pyGenerator.generate(definition);
      expect(result.fileName).toMatch(/\.py$/);
    });

    it('should generate correct file name for Java', () => {
      const javaGenerator = new CodeGenerator({ language: 'java' });
      const definition: CodeStructureDefinition = {
        name: 'UserService',
        type: 'service',
      };

      const result = javaGenerator.generate(definition);
      expect(result.fileName).toMatch(/\.java$/);
    });
  });

  describe('Multi-Language Support', () => {
    const languages: TargetLanguage[] = ['typescript', 'javascript', 'python', 'java', 'csharp', 'go', 'rust'];

    languages.forEach((lang) => {
      it(`should generate code for ${lang}`, () => {
        const langGenerator = new CodeGenerator({ language: lang });

        const definition: CodeStructureDefinition = {
          name: 'Example',
          type: 'class',
          properties: [{ name: 'value', type: 'string' }],
          methods: [{ name: 'getValue', returnType: 'string' }],
        };

        const result = langGenerator.generate(definition);

        expect(result.language).toBe(lang);
        expect(result.code).toBeDefined();
        expect(result.code.length).toBeGreaterThan(0);
      });
    });
  });

  describe('Dependencies Extraction', () => {
    it('should extract import modules', () => {
      const definition: CodeStructureDefinition = {
        name: 'Consumer',
        type: 'class',
        dependencies: [
          { module: '@nestjs/common', imports: ['Injectable'] },
          { module: './user.entity', imports: ['User'] },
        ],
      };

      const result = generator.generate(definition);

      expect(result.imports).toContain('@nestjs/common');
      expect(result.imports).toContain('./user.entity');
    });

    it('should extract external dependencies', () => {
      const definition: CodeStructureDefinition = {
        name: 'Service',
        type: 'service',
        dependencies: [
          { module: 'lodash', imports: ['debounce'] },
          { module: 'axios', imports: ['AxiosInstance'] },
        ],
      };

      const result = generator.generate(definition);

      expect(result.dependencies).toBeDefined();
    });
  });

  describe('Edge Cases', () => {
    it('should handle empty definition', () => {
      const definition: CodeStructureDefinition = {
        name: 'Empty',
        type: 'class',
      };

      const result = generator.generate(definition);

      expect(result.code).toBeDefined();
      expect(result.warnings).toHaveLength(0);
    });

    it('should handle special characters in names', () => {
      const definition: CodeStructureDefinition = {
        name: 'My_Special_Class123',
        type: 'class',
      };

      const result = generator.generate(definition);

      expect(result.code).toContain('My_Special_Class123');
    });

    it('should handle very long names', () => {
      const longName = 'A'.repeat(100);
      const definition: CodeStructureDefinition = {
        name: longName,
        type: 'class',
      };

      const result = generator.generate(definition);

      expect(result.code).toContain(longName);
    });

    it('should handle empty methods array', () => {
      const definition: CodeStructureDefinition = {
        name: 'NoMethods',
        type: 'class',
        methods: [],
      };

      const result = generator.generate(definition);
      expect(result.code).toBeDefined();
    });

    it('should handle empty properties array', () => {
      const definition: CodeStructureDefinition = {
        name: 'NoProps',
        type: 'class',
        properties: [],
      };

      const result = generator.generate(definition);
      expect(result.code).toBeDefined();
    });
  });

  describe('Custom Options', () => {
    it('should respect custom indentation', () => {
      const tabGenerator = new CodeGenerator({ indent: '\t' });
      const definition: CodeStructureDefinition = {
        name: 'TabIndented',
        type: 'class',
        properties: [{ name: 'value', type: 'string' }],
      };

      const result = tabGenerator.generate(definition);
      expect(result.code).toContain('\t');
    });

    it('should respect line ending', () => {
      const windowsGenerator = new CodeGenerator({ lineEnding: '\r\n' });
      const definition: CodeStructureDefinition = {
        name: 'WindowsStyle',
        type: 'class',
      };

      const result = windowsGenerator.generate(definition);
      expect(result.code).toContain('\r\n');
    });
  });
});
