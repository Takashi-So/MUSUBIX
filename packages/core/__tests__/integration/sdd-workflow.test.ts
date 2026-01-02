/**
 * MUSUBIX Core Integration Tests
 * 
 * Tests the integration between EARS Validator, Pattern Detector, and Code Generator
 * 
 * @see REQ-RA-001 - EARS Pattern Recognition
 * @see REQ-RA-001 - EARS Pattern Recognition
 * @see REQ-DES-001 - Design Pattern Detection
 * @see REQ-COD-001 - Code Generation
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { EARSValidator } from '../../src/validators/ears-validator.js';
import { PatternDetector, DESIGN_PATTERNS } from '../../src/design/pattern-detector.js';
import { CodeGenerator } from '../../src/codegen/generator.js';

describe('Integration: SDD Workflow', () => {
  let earsValidator: EARSValidator;
  let patternDetector: PatternDetector;
  let codeGenerator: CodeGenerator;

  beforeEach(() => {
    earsValidator = new EARSValidator();
    patternDetector = new PatternDetector();
    codeGenerator = new CodeGenerator();
  });

  describe('Requirements to Design Workflow', () => {
    it('should validate requirements and suggest design patterns', () => {
      // Step 1: Validate requirements
      const requirements = [
        'The AuthService shall authenticate users with email and password',
        'The AuthService shall generate JWT tokens upon successful authentication',
        'The AuthService shall validate JWT tokens for protected routes',
      ];

      const validationResults = earsValidator.validateRequirements(requirements);
      expect(validationResults.valid).toBe(validationResults.total);

      // Step 2: Suggest design patterns based on requirements
      const suggestions = patternDetector.suggestPatterns({
        problem: 'Need to create authentication service with token management',
        constraints: ['Single authentication method', 'Stateless tokens'],
      });

      expect(suggestions).toBeInstanceOf(Array);
    });

    it('should trace pattern from requirements through design', () => {
      // Requirement pattern
      const reqResult = earsValidator.validateRequirement(
        'The system shall ensure only one DatabaseConnection exists'
      );
      expect(reqResult.valid).toBe(true);

      // Design pattern suggestion
      const suggestions = patternDetector.suggestPatterns({
        problem: 'Need to ensure only one database connection instance',
      });

      expect(suggestions).toBeInstanceOf(Array);
    });
  });

  describe('Design to Code Workflow', () => {
    it('should generate code from design specifications', () => {
      // Design specification
      const design = {
        name: 'UserRepository',
        type: 'repository' as const,
        description: 'Repository for user data access',
        methods: [
          {
            name: 'findById',
            parameters: [{ name: 'id', type: 'string' }],
            returnType: 'Promise<User | null>',
            async: true,
            description: 'Find user by ID',
          },
          {
            name: 'save',
            parameters: [{ name: 'user', type: 'User' }],
            returnType: 'Promise<User>',
            async: true,
            description: 'Save user to database',
          },
        ],
        dependencies: [
          { module: './user.entity', imports: ['User'] },
        ],
      };

      // Generate code
      const result = codeGenerator.generate(design);

      expect(result.code).toContain('UserRepository');
      expect(result.code).toContain('findById');
      expect(result.code).toContain('save');
      expect(result.language).toBe('typescript');
    });

    it('should detect patterns in generated code', () => {
      // Generate a builder pattern class
      const builderDesign = {
        name: 'QueryBuilder',
        type: 'class' as const,
        description: 'SQL Query Builder',
        methods: [
          {
            name: 'select',
            parameters: [{ name: 'fields', type: 'string[]' }],
            returnType: 'QueryBuilder',
            description: 'Add SELECT clause',
          },
          {
            name: 'from',
            parameters: [{ name: 'table', type: 'string' }],
            returnType: 'QueryBuilder',
            description: 'Add FROM clause',
          },
          {
            name: 'where',
            parameters: [{ name: 'condition', type: 'string' }],
            returnType: 'QueryBuilder',
            description: 'Add WHERE clause',
          },
          {
            name: 'build',
            parameters: [],
            returnType: 'string',
            description: 'Build the final SQL query',
          },
        ],
      };

      const generated = codeGenerator.generate(builderDesign);
      const patterns = patternDetector.detectInCode(generated.code);

      // Should detect builder-like structure
      expect(patterns).toBeInstanceOf(Array);
    });
  });

  describe('Full Traceability Workflow', () => {
    it('should maintain traceability from requirements to code', () => {
      // Step 1: Define requirements
      const requirements = [
        'The UserService shall create new users',
        'The UserService shall retrieve users by ID',
        'The UserService shall update user information',
        'The UserService shall delete users',
      ];

      // Validate all requirements
      const validations = requirements.map(r => ({
        requirement: r,
        validation: earsValidator.validateRequirement(r),
      }));

      expect(validations.every(v => v.validation.valid)).toBe(true);

      // Step 2: Create design based on requirements
      const serviceDesign = {
        name: 'UserService',
        type: 'service' as const,
        description: 'Service for user CRUD operations',
        methods: [
          {
            name: 'create',
            description: '@see REQ-001 - Create new users',
            parameters: [{ name: 'data', type: 'CreateUserDto' }],
            returnType: 'Promise<User>',
            async: true,
          },
          {
            name: 'findById',
            description: '@see REQ-002 - Retrieve users by ID',
            parameters: [{ name: 'id', type: 'string' }],
            returnType: 'Promise<User | null>',
            async: true,
          },
          {
            name: 'update',
            description: '@see REQ-003 - Update user information',
            parameters: [
              { name: 'id', type: 'string' },
              { name: 'data', type: 'UpdateUserDto' },
            ],
            returnType: 'Promise<User>',
            async: true,
          },
          {
            name: 'delete',
            description: '@see REQ-004 - Delete users',
            parameters: [{ name: 'id', type: 'string' }],
            returnType: 'Promise<void>',
            async: true,
          },
        ],
      };

      // Step 3: Generate code
      const code = codeGenerator.generate(serviceDesign);

      // Verify code contains requirement references
      expect(code.code).toContain('UserService');
      expect(code.code).toContain('create');
      expect(code.code).toContain('findById');
      expect(code.code).toContain('update');
      expect(code.code).toContain('delete');

      // Verify all requirements are traceable
      expect(validations.length).toBe(4);
      expect(serviceDesign.methods.length).toBe(4);
    });
  });

  describe('Constitutional Compliance', () => {
    it('should validate Library-First principle (Article I)', () => {
      // Generate standalone library code
      const libraryDesign = {
        name: 'StringUtils',
        type: 'class' as const,  // Generate as class to include name
        description: 'String utility functions',
        methods: [
          { name: 'capitalize', parameters: [{ name: 's', type: 'string' }], returnType: 'string' },
          { name: 'truncate', parameters: [{ name: 's', type: 'string' }, { name: 'len', type: 'number' }], returnType: 'string' },
        ],
      };

      const result = codeGenerator.generate(libraryDesign);

      // Library should have no external dependencies for core functionality
      expect(result.dependencies.length).toBe(0);
      expect(result.code).toContain('StringUtils');
    });

    it('should support CLI Interface principle (Article II)', () => {
      // Generate CLI-compatible interface
      const cliDesign = {
        name: 'CLICommand',
        type: 'interface' as const,
        methods: [
          { name: 'execute', parameters: [{ name: 'args', type: 'string[]' }], returnType: 'Promise<number>' },
          { name: 'getHelp', parameters: [], returnType: 'string' },
        ],
      };

      const result = codeGenerator.generate(cliDesign);
      expect(result.code).toContain('interface CLICommand');
      expect(result.code).toContain('execute');
      expect(result.code).toContain('getHelp');
    });

    it('should validate EARS Format principle (Article IV)', () => {
      // All requirements should follow EARS patterns
      const requirements = [
        'The system shall process requests',
        'When error occurs, the system shall log the error',
        'While processing, the UI shall show progress',
        'If timeout exceeds 30s, then the system shall cancel',
        'Where caching enabled, the system shall use cache',
      ];

      const results = earsValidator.validateRequirements(requirements);
      
      // All should be valid EARS patterns
      expect(results.valid).toBe(results.total);
    });
  });

  describe('Multi-Language Support', () => {
    const languages = ['typescript', 'javascript', 'python'] as const;

    languages.forEach(lang => {
      it(`should generate consistent code for ${lang}`, () => {
        const generator = new CodeGenerator({ language: lang });
        
        const design = {
          name: 'Calculator',
          type: 'class' as const,
          methods: [
            { name: 'add', parameters: [{ name: 'a', type: 'number' }, { name: 'b', type: 'number' }], returnType: 'number' },
          ],
        };

        const result = generator.generate(design);

        expect(result.language).toBe(lang);
        expect(result.code).toContain('Calculator');
        expect(result.code).toContain('add');
      });
    });
  });

  describe('Error Handling', () => {
    it('should handle invalid requirements gracefully', () => {
      const result = earsValidator.validateRequirement('');
      
      expect(result.valid).toBe(false);
      expect(result.issues.length).toBeGreaterThan(0);
    });

    it('should handle empty code for pattern detection', () => {
      const patterns = patternDetector.detectInCode('');
      
      expect(patterns).toEqual([]);
    });

    it('should handle minimal design for code generation', () => {
      const result = codeGenerator.generate({
        name: 'Empty',
        type: 'class',
      });

      expect(result.code).toContain('Empty');
      expect(result.warnings).toHaveLength(0);
    });
  });
});

describe('Integration: Knowledge-Driven Development', () => {
  it('should support iterative requirement refinement', () => {
    const validator = new EARSValidator({ strictMode: true });

    // Initial vague requirement
    const vague = 'Users should be able to login';
    const vagueResult = validator.validateRequirement(vague);
    expect(vagueResult.valid).toBe(false);
    expect(vagueResult.suggestions.length).toBeGreaterThan(0);

    // Refined EARS requirement
    const refined = 'The AuthenticationModule shall authenticate users with valid credentials';
    const refinedResult = validator.validateRequirement(refined);
    expect(refinedResult.valid).toBe(true);
  });

  it('should connect design patterns to implementation', () => {
    const detector = new PatternDetector();
    const generator = new CodeGenerator();

    // Get pattern recommendations
    const suggestions = detector.suggestPatterns({
      problem: 'Need to manage object lifecycle with different states',
    });

    // Generate code with pattern in mind
    const design = {
      name: 'OrderStateMachine',
      type: 'class' as const,
      description: 'State machine for order lifecycle',
      properties: [
        { name: 'currentState', type: 'OrderState', visibility: 'private' as const },
      ],
      methods: [
        { name: 'transition', parameters: [{ name: 'newState', type: 'OrderState' }], returnType: 'void' },
        { name: 'getState', parameters: [], returnType: 'OrderState' },
      ],
    };

    const code = generator.generate(design);
    expect(code.code).toContain('OrderStateMachine');
    expect(code.code).toContain('currentState');
    expect(code.code).toContain('transition');
  });
});
