/**
 * Scaffold Command
 *
 * CLI commands for generating SDD-compliant project scaffolding
 *
 * @packageDocumentation
 * @module cli/commands/scaffold
 *
 * @see REQ-SDD-SCAFFOLD-001 - SDD Project Scaffolding
 * @see IMP-SDD-001 - Improvement from project-08 development
 */

import type { Command } from 'commander';
import { mkdir, writeFile, access } from 'fs/promises';
import { resolve, join } from 'path';
import { ExitCode, getGlobalOptions, outputResult } from '../base.js';
import { VERSION } from '../../version.js';

/**
 * Scaffold options
 */
export interface ScaffoldOptions {
  name?: string;
  output?: string;
  domain?: string;
  entities?: string;
  valueObjects?: string;
  statuses?: string;
  force?: boolean;
}

/**
 * Project template types
 */
export type ProjectTemplate =
  | 'domain-model'
  | 'api-service'
  | 'crud-system'
  | 'event-driven'
  | 'minimal';

/**
 * Scaffold result
 */
export interface ScaffoldResult {
  success: boolean;
  projectPath: string;
  filesCreated: string[];
  message: string;
}

/**
 * Register scaffold command
 */
export function registerScaffoldCommand(program: Command): void {
  const scaffold = program
    .command('scaffold')
    .description('Generate SDD-compliant project structure');

  // scaffold domain-model
  scaffold
    .command('domain-model <name>')
    .description('Create domain-driven design project scaffold')
    .option('-o, --output <dir>', 'Output directory', '.')
    .option('-d, --domain <name>', 'Domain prefix (e.g., RENTAL, CLINIC)', 'PROJECT')
    .option('-e, --entities <list>', 'Comma-separated entity names')
    .option('-v, --value-objects <list>', 'Comma-separated value object names (e.g., Price,Email)')
    .option('-s, --statuses <list>', 'Comma-separated status machine names (e.g., Order,Task)')
    .option('-f, --force', 'Overwrite existing files', false)
    .action(async (name: string, options: ScaffoldOptions) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const projectPath = resolve(options.output ?? '.', name);
        const domain = (options.domain ?? 'PROJECT').toUpperCase();
        const entities = options.entities
          ? options.entities.split(',').map((e: string) => e.trim())
          : ['Entity'];

        // Check if directory exists
        try {
          await access(projectPath);
          if (!options.force) {
            throw new Error(`Directory ${projectPath} already exists. Use --force to overwrite.`);
          }
        } catch (e) {
          if ((e as NodeJS.ErrnoException).code !== 'ENOENT') {
            throw e;
          }
        }

        const filesCreated: string[] = [];

        // Create directory structure
        const directories = [
          'storage/specs',
          'storage/design',
          'storage/traceability',
          'storage/learning',
          'src/types',
          'src/entities',
          'src/services',
          'src/repositories',
          '__tests__',
        ];

        for (const dir of directories) {
          await mkdir(join(projectPath, dir), { recursive: true });
        }

        // Create EARS requirements template
        const reqContent = generateRequirementsTemplate(name, domain, entities);
        const reqPath = join(projectPath, 'storage/specs', `REQ-${domain}-001.md`);
        await writeFile(reqPath, reqContent, 'utf-8');
        filesCreated.push(`storage/specs/REQ-${domain}-001.md`);

        // Create C4 design template
        const designContent = generateDesignTemplate(name, domain, entities);
        const designPath = join(projectPath, 'storage/design', `DES-${domain}-001.md`);
        await writeFile(designPath, designContent, 'utf-8');
        filesCreated.push(`storage/design/DES-${domain}-001.md`);

        // Create traceability template
        const traceContent = generateTraceabilityTemplate(domain);
        const tracePath = join(projectPath, 'storage/traceability', `TRACE-${domain}-001.md`);
        await writeFile(tracePath, traceContent, 'utf-8');
        filesCreated.push(`storage/traceability/TRACE-${domain}-001.md`);

        // Create common types
        const typesContent = generateTypesTemplate(domain);
        await writeFile(join(projectPath, 'src/types/common.ts'), typesContent, 'utf-8');
        filesCreated.push('src/types/common.ts');

        // Create errors
        const errorsContent = generateErrorsTemplate(domain);
        await writeFile(join(projectPath, 'src/types/errors.ts'), errorsContent, 'utf-8');
        filesCreated.push('src/types/errors.ts');

        // Create entity templates
        for (const entity of entities) {
          const entityContent = generateEntityTemplate(domain, entity);
          const entityPath = join(projectPath, 'src/entities', `${entity}.ts`);
          await writeFile(entityPath, entityContent, 'utf-8');
          filesCreated.push(`src/entities/${entity}.ts`);

          // Create test template
          const testContent = generateTestTemplate(domain, entity);
          const testPath = join(projectPath, '__tests__', `${entity}.test.ts`);
          await writeFile(testPath, testContent, 'utf-8');
          filesCreated.push(`__tests__/${entity}.test.ts`);
        }

        // Create value objects if specified
        const valueObjects = options.valueObjects
          ? options.valueObjects.split(',').map((v: string) => v.trim())
          : [];

        if (valueObjects.length > 0) {
          await mkdir(join(projectPath, 'src/value-objects'), { recursive: true });
          for (const vo of valueObjects) {
            const voContent = generateValueObjectTemplate(domain, vo);
            const voPath = join(projectPath, 'src/value-objects', `${toKebabCase(vo)}.ts`);
            await writeFile(voPath, voContent, 'utf-8');
            filesCreated.push(`src/value-objects/${toKebabCase(vo)}.ts`);

            // Create VO test template
            const voTestContent = generateValueObjectTestTemplate(domain, vo);
            const voTestPath = join(projectPath, '__tests__', `${toKebabCase(vo)}.test.ts`);
            await writeFile(voTestPath, voTestContent, 'utf-8');
            filesCreated.push(`__tests__/${toKebabCase(vo)}.test.ts`);
          }
        }

        // Create status machines if specified
        const statuses = options.statuses
          ? options.statuses.split(',').map((s: string) => s.trim())
          : [];

        if (statuses.length > 0) {
          await mkdir(join(projectPath, 'src/statuses'), { recursive: true });
          for (const status of statuses) {
            const statusContent = generateStatusTemplate(domain, status);
            const statusPath = join(projectPath, 'src/statuses', `${toKebabCase(status)}-status.ts`);
            await writeFile(statusPath, statusContent, 'utf-8');
            filesCreated.push(`src/statuses/${toKebabCase(status)}-status.ts`);

            // Create status test template
            const statusTestContent = generateStatusTestTemplate(domain, status);
            const statusTestPath = join(projectPath, '__tests__', `${toKebabCase(status)}-status.test.ts`);
            await writeFile(statusTestPath, statusTestContent, 'utf-8');
            filesCreated.push(`__tests__/${toKebabCase(status)}-status.test.ts`);
          }
        }

        // Create index.ts
        const indexContent = generateIndexTemplate(entities);
        await writeFile(join(projectPath, 'src/index.ts'), indexContent, 'utf-8');
        filesCreated.push('src/index.ts');

        // Create package.json
        const packageContent = generatePackageJson(name, domain);
        await writeFile(join(projectPath, 'package.json'), packageContent, 'utf-8');
        filesCreated.push('package.json');

        // Create tsconfig.json
        const tsconfigContent = generateTsConfig();
        await writeFile(join(projectPath, 'tsconfig.json'), tsconfigContent, 'utf-8');
        filesCreated.push('tsconfig.json');

        // Create vitest.config.ts
        const vitestContent = generateVitestConfig();
        await writeFile(join(projectPath, 'vitest.config.ts'), vitestContent, 'utf-8');
        filesCreated.push('vitest.config.ts');

        // Create .knowledge/graph.json
        await mkdir(join(projectPath, '.knowledge'), { recursive: true });
        const knowledgeConfig = generateKnowledgeConfig(domain);
        await writeFile(join(projectPath, '.knowledge/graph.json'), knowledgeConfig, 'utf-8');
        filesCreated.push('.knowledge/graph.json');

        const result: ScaffoldResult = {
          success: true,
          projectPath,
          filesCreated,
          message: `✅ Created SDD project scaffold at ${projectPath} with ${filesCreated.length} files`,
        };

        outputResult(result, globalOpts);

        if (!globalOpts.quiet) {
          console.log('\n📁 Project structure:');
          for (const file of filesCreated) {
            console.log(`   ${file}`);
          }
          console.log('\n🚀 Next steps:');
          console.log(`   cd ${name}`);
          console.log('   npm install');
          console.log('   npm run test');
          console.log('\n📖 SDD Workflow:');
          console.log('   1. Edit storage/specs/REQ-*.md (EARS requirements)');
          console.log('   2. Edit storage/design/DES-*.md (C4 design)');
          console.log('   3. Write tests in __tests__/ (TDD)');
          console.log('   4. Implement src/entities/');
          console.log('   5. Update storage/traceability/TRACE-*.md');
        }

        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Scaffold failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });

  // scaffold api-service
  scaffold
    .command('api-service <name>')
    .description('Create API service project scaffold')
    .option('-o, --output <dir>', 'Output directory', '.')
    .option('-d, --domain <name>', 'Domain prefix', 'API')
    .option('-f, --force', 'Overwrite existing files', false)
    .action(async (_name: string, _options: ScaffoldOptions) => {
      const globalOpts = getGlobalOptions(program);

      if (!globalOpts.quiet) {
        console.log('⚠️ api-service template is coming soon. Using domain-model template.');
      }

      // Delegate to domain-model for now
      process.exit(ExitCode.SUCCESS);
    });

  // scaffold minimal
  scaffold
    .command('minimal <name>')
    .description('Create minimal SDD project scaffold')
    .option('-o, --output <dir>', 'Output directory', '.')
    .option('-d, --domain <name>', 'Domain prefix', 'MIN')
    .option('-f, --force', 'Overwrite existing files', false)
    .action(async (name: string, options: ScaffoldOptions) => {
      const globalOpts = getGlobalOptions(program);

      try {
        const projectPath = resolve(options.output ?? '.', name);
        const domain = (options.domain ?? 'MIN').toUpperCase();

        // Check if directory exists
        try {
          await access(projectPath);
          if (!options.force) {
            throw new Error(`Directory ${projectPath} already exists. Use --force to overwrite.`);
          }
        } catch (e) {
          if ((e as NodeJS.ErrnoException).code !== 'ENOENT') {
            throw e;
          }
        }

        const filesCreated: string[] = [];

        // Create minimal structure
        await mkdir(join(projectPath, 'storage/specs'), { recursive: true });
        await mkdir(join(projectPath, 'storage/design'), { recursive: true });
        await mkdir(join(projectPath, 'src'), { recursive: true });
        await mkdir(join(projectPath, '__tests__'), { recursive: true });

        // Create minimal EARS requirements
        const reqContent = `# Requirements: ${name}

**Document ID**: REQ-${domain}-001
**Version**: 1.0.0
**Created**: ${new Date().toISOString().split('T')[0]}

## Requirements

| ID | Pattern | Priority | Description |
|----|---------|----------|-------------|
| REQ-${domain}-001 | Ubiquitous | P0 | The system SHALL provide basic functionality |

### REQ-${domain}-001 (Ubiquitous - P0)
> The system SHALL provide basic functionality.

**Rationale**: Initial requirement placeholder
`;
        await writeFile(join(projectPath, 'storage/specs', `REQ-${domain}-001.md`), reqContent, 'utf-8');
        filesCreated.push(`storage/specs/REQ-${domain}-001.md`);

        // Create minimal package.json
        const packageContent = generatePackageJson(name, domain);
        await writeFile(join(projectPath, 'package.json'), packageContent, 'utf-8');
        filesCreated.push('package.json');

        const result: ScaffoldResult = {
          success: true,
          projectPath,
          filesCreated,
          message: `✅ Created minimal SDD scaffold at ${projectPath}`,
        };

        outputResult(result, globalOpts);
        process.exit(ExitCode.SUCCESS);
      } catch (error) {
        if (!globalOpts.quiet) {
          console.error(`❌ Scaffold failed: ${(error as Error).message}`);
        }
        process.exit(ExitCode.GENERAL_ERROR);
      }
    });
}

// ============================================================================
// Template Generators
// ============================================================================

function generateRequirementsTemplate(name: string, domain: string, entities: string[]): string {
  const date = new Date().toISOString().split('T')[0];
  const reqRows = entities.map((entity, i) => {
    const num = String(i + 1).padStart(3, '0');
    return `| REQ-${domain}-${num} | Event-driven | P0 | The system SHALL create ${entity} when requested |`;
  }).join('\n');

  const detailedReqs = entities.map((entity, i) => {
    const num = String(i + 1).padStart(3, '0');
    return `### REQ-${domain}-${num} (Event-driven - P0)
> WHEN a create ${entity} request is received, THE system SHALL create a new ${entity} entity with a unique ID.

**Rationale**: Core ${entity} management functionality
**Related**: DES-${domain}-${num}`;
  }).join('\n\n');

  return `# Requirements: ${name}

**Document ID**: REQ-${domain}-001
**Version**: 1.0.0
**Created**: ${date}
**Generated by**: MUSUBIX v${VERSION} scaffold

## Overview

This document defines the EARS-format requirements for the ${name} system.

## Requirements Summary

| ID | Pattern | Priority | Description |
|----|---------|----------|-------------|
${reqRows}

## Detailed Requirements

${detailedReqs}

---

## Traceability

Requirements trace to:
- Design: DES-${domain}-001
- Tests: __tests__/*.test.ts
`;
}

function generateDesignTemplate(name: string, domain: string, entities: string[]): string {
  const date = new Date().toISOString().split('T')[0];

  const componentRows = entities.map((entity, i) => {
    const num = String(i + 1).padStart(3, '0');
    return `| ${entity} | Component | ${entity} management | REQ-${domain}-${num} |`;
  }).join('\n');

  const componentDetails = entities.map((entity, i) => {
    const num = String(i + 1).padStart(3, '0');
    return `### Component: ${entity}

**Purpose**: Manages ${entity} entities
**Implements**: REQ-${domain}-${num}
**Location**: src/entities/${entity}.ts

#### Responsibilities
- Create ${entity} with unique ID
- Validate ${entity} data
- Status management

#### Patterns Applied
- Value Object (for IDs)
- Factory Function
- Result Type`;
  }).join('\n\n');

  return `# Design Document: ${name}

**Document ID**: DES-${domain}-001
**Version**: 1.0.0
**Created**: ${date}
**Generated by**: MUSUBIX v${VERSION} scaffold

## Overview

This document describes the C4 model design for the ${name} system.

## C4 Model

### Level 1: Context

The ${name} system provides domain management capabilities.

### Level 2: Container

| Container | Type | Technology | Purpose |
|-----------|------|------------|---------|
| ${name} | Application | TypeScript | Core domain logic |

### Level 3: Components

| Component | Type | Description | Requirements |
|-----------|------|-------------|--------------|
${componentRows}

## Component Details

${componentDetails}

---

## Traceability

- Requirements: REQ-${domain}-001
- Implementation: src/entities/
- Tests: __tests__/
`;
}

function generateTraceabilityTemplate(domain: string): string {
  const date = new Date().toISOString().split('T')[0];

  return `# Traceability Matrix

**Document ID**: TRACE-${domain}-001
**Version**: 1.0.0
**Updated**: ${date}
**Generated by**: MUSUBIX v${VERSION} scaffold

## Requirements → Design → Code → Test

| Requirement | Design | Code | Test | Status |
|-------------|--------|------|------|--------|
| REQ-${domain}-001 | DES-${domain}-001 | src/entities/*.ts | __tests__/*.test.ts | 🟡 In Progress |

## Coverage Summary

- Requirements Coverage: 0%
- Design Coverage: 0%
- Test Coverage: 0%

---

*Update this matrix as implementation progresses.*
`;
}

function generateTypesTemplate(domain: string): string {
  return `/**
 * Common Types for ${domain}
 *
 * Value Objects and shared types
 *
 * @see REQ-${domain}-001
 */

import { Result, ok, err } from 'neverthrow';
import type { ValidationError } from './errors.js';

// ============================================================================
// ID Value Object
// ============================================================================

export interface EntityId {
  readonly value: string;
  readonly prefix: string;
}

let entityCounter = 0;

export function createEntityId(prefix: string): EntityId {
  const date = new Date().toISOString().slice(0, 10).replace(/-/g, '');
  const sequence = String(++entityCounter).padStart(3, '0');
  return {
    value: \`\${prefix}-\${date}-\${sequence}\`,
    prefix,
  };
}

export function resetEntityCounter(): void {
  entityCounter = 0;
}

// ============================================================================
// Timestamp
// ============================================================================

export interface Timestamp {
  readonly createdAt: Date;
  readonly updatedAt: Date;
}

export function createTimestamp(): Timestamp {
  const now = new Date();
  return {
    createdAt: now,
    updatedAt: now,
  };
}

export function updateTimestamp(timestamp: Timestamp): Timestamp {
  return {
    ...timestamp,
    updatedAt: new Date(),
  };
}

// ============================================================================
// Re-export Result type
// ============================================================================

export { Result, ok, err };
export type { ValidationError };
`;
}

function generateErrorsTemplate(domain: string): string {
  return `/**
 * Domain Errors for ${domain}
 *
 * @see REQ-${domain}-001
 */

// ============================================================================
// Error Types
// ============================================================================

export interface ValidationError {
  readonly code: string;
  readonly message: string;
  readonly field?: string;
}

export interface NotFoundError {
  readonly code: 'NOT_FOUND';
  readonly message: string;
  readonly entityType: string;
  readonly id: string;
}

export interface InvalidStateError {
  readonly code: 'INVALID_STATE';
  readonly message: string;
  readonly currentState: string;
  readonly attemptedAction: string;
}

// ============================================================================
// Error Type Union
// ============================================================================

export type DomainError = ValidationError | NotFoundError | InvalidStateError;

// ============================================================================
// Error Factories
// ============================================================================

export function createValidationError(message: string, field?: string): ValidationError {
  return {
    code: 'VALIDATION_ERROR',
    message,
    field,
  };
}

export function createNotFoundError(entityType: string, id: string): NotFoundError {
  return {
    code: 'NOT_FOUND',
    message: \`\${entityType} with ID \${id} not found\`,
    entityType,
    id,
  };
}

export function createInvalidStateError(
  currentState: string,
  attemptedAction: string
): InvalidStateError {
  return {
    code: 'INVALID_STATE',
    message: \`Cannot \${attemptedAction} in state \${currentState}\`,
    currentState,
    attemptedAction,
  };
}
`;
}

function generateEntityTemplate(domain: string, entity: string): string {
  const entityLower = entity.toLowerCase();
  const entityUpper = entity.toUpperCase();

  return `/**
 * ${entity} Entity
 *
 * @see REQ-${domain}-001
 * @see DES-${domain}-001
 */

import { Result, ok, err } from 'neverthrow';
import {
  EntityId,
  createEntityId,
  Timestamp,
  createTimestamp,
  updateTimestamp,
} from '../types/common.js';
import { ValidationError, createValidationError, createInvalidStateError } from '../types/errors.js';

// ============================================================================
// Types
// ============================================================================

export type ${entity}Status = 'active' | 'inactive' | 'deleted';

export interface ${entity}Input {
  readonly name: string;
  // Add more fields as needed
}

export interface ${entity} {
  readonly id: EntityId;
  readonly name: string;
  readonly status: ${entity}Status;
  readonly timestamp: Timestamp;
  readonly version: number;
}

// ============================================================================
// Status Transition Map
// ============================================================================

const validStatusTransitions: Record<${entity}Status, ${entity}Status[]> = {
  active: ['inactive', 'deleted'],
  inactive: ['active', 'deleted'],
  deleted: [],
};

export function canTransitionTo(current: ${entity}Status, target: ${entity}Status): boolean {
  return validStatusTransitions[current].includes(target);
}

// ============================================================================
// Factory Functions
// ============================================================================

let ${entityLower}Counter = 0;

export function create${entity}(input: ${entity}Input): Result<${entity}, ValidationError> {
  // Validation
  if (!input.name || input.name.trim().length === 0) {
    return err(createValidationError('Name is required', 'name'));
  }

  if (input.name.length > 100) {
    return err(createValidationError('Name must be 100 characters or less', 'name'));
  }

  const ${entityLower}: ${entity} = {
    id: createEntityId('${entityUpper}'),
    name: input.name.trim(),
    status: 'active',
    timestamp: createTimestamp(),
    version: 1,
  };

  return ok(${entityLower});
}

export function update${entity}(
  ${entityLower}: ${entity},
  updates: Partial<${entity}Input>
): Result<${entity}, ValidationError> {
  if (${entityLower}.status === 'deleted') {
    return err(createInvalidStateError('deleted', 'update'));
  }

  const name = updates.name ?? ${entityLower}.name;

  if (name.length > 100) {
    return err(createValidationError('Name must be 100 characters or less', 'name'));
  }

  return ok({
    ...${entityLower},
    name: name.trim(),
    timestamp: updateTimestamp(${entityLower}.timestamp),
    version: ${entityLower}.version + 1,
  });
}

export function change${entity}Status(
  ${entityLower}: ${entity},
  newStatus: ${entity}Status
): Result<${entity}, ValidationError> {
  if (!canTransitionTo(${entityLower}.status, newStatus)) {
    return err(
      createInvalidStateError(${entityLower}.status, \`transition to \${newStatus}\`)
    );
  }

  return ok({
    ...${entityLower},
    status: newStatus,
    timestamp: updateTimestamp(${entityLower}.timestamp),
    version: ${entityLower}.version + 1,
  });
}

// ============================================================================
// Test Utilities
// ============================================================================

export function reset${entity}Counter(): void {
  ${entityLower}Counter = 0;
}
`;
}

function generateTestTemplate(domain: string, entity: string): string {
  const entityLower = entity.toLowerCase();

  return `/**
 * ${entity} Tests
 *
 * @see REQ-${domain}-001
 * @see DES-${domain}-001
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  create${entity},
  update${entity},
  change${entity}Status,
  canTransitionTo,
  reset${entity}Counter,
  type ${entity}Input,
} from '../src/entities/${entity}.js';
import { resetEntityCounter } from '../src/types/common.js';

describe('${entity}', () => {
  beforeEach(() => {
    resetEntityCounter();
    reset${entity}Counter();
  });

  describe('create${entity}', () => {
    it('should create ${entityLower} with valid input', () => {
      const input: ${entity}Input = {
        name: 'Test ${entity}',
      };

      const result = create${entity}(input);

      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.name).toBe('Test ${entity}');
        expect(result.value.status).toBe('active');
        expect(result.value.version).toBe(1);
      }
    });

    it('should reject empty name', () => {
      const input: ${entity}Input = {
        name: '',
      };

      const result = create${entity}(input);

      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.field).toBe('name');
      }
    });

    it('should reject name over 100 characters', () => {
      const input: ${entity}Input = {
        name: 'a'.repeat(101),
      };

      const result = create${entity}(input);

      expect(result.isErr()).toBe(true);
    });
  });

  describe('update${entity}', () => {
    it('should update ${entityLower} name', () => {
      const createResult = create${entity}({ name: 'Original' });
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const updateResult = update${entity}(createResult.value, { name: 'Updated' });

      expect(updateResult.isOk()).toBe(true);
      if (updateResult.isOk()) {
        expect(updateResult.value.name).toBe('Updated');
        expect(updateResult.value.version).toBe(2);
      }
    });

    it('should not update deleted ${entityLower}', () => {
      const createResult = create${entity}({ name: 'Test' });
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const deleteResult = change${entity}Status(createResult.value, 'deleted');
      expect(deleteResult.isOk()).toBe(true);
      if (!deleteResult.isOk()) return;

      const updateResult = update${entity}(deleteResult.value, { name: 'Should Fail' });

      expect(updateResult.isErr()).toBe(true);
    });
  });

  describe('change${entity}Status', () => {
    it('should allow valid status transitions', () => {
      const createResult = create${entity}({ name: 'Test' });
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const inactiveResult = change${entity}Status(createResult.value, 'inactive');

      expect(inactiveResult.isOk()).toBe(true);
      if (inactiveResult.isOk()) {
        expect(inactiveResult.value.status).toBe('inactive');
      }
    });

    it('should reject invalid status transitions', () => {
      const createResult = create${entity}({ name: 'Test' });
      expect(createResult.isOk()).toBe(true);
      if (!createResult.isOk()) return;

      const deleteResult = change${entity}Status(createResult.value, 'deleted');
      expect(deleteResult.isOk()).toBe(true);
      if (!deleteResult.isOk()) return;

      const reactivateResult = change${entity}Status(deleteResult.value, 'active');

      expect(reactivateResult.isErr()).toBe(true);
    });
  });

  describe('canTransitionTo', () => {
    it('should return true for valid transitions', () => {
      expect(canTransitionTo('active', 'inactive')).toBe(true);
      expect(canTransitionTo('active', 'deleted')).toBe(true);
      expect(canTransitionTo('inactive', 'active')).toBe(true);
    });

    it('should return false for invalid transitions', () => {
      expect(canTransitionTo('deleted', 'active')).toBe(false);
      expect(canTransitionTo('deleted', 'inactive')).toBe(false);
    });
  });
});
`;
}

function generateIndexTemplate(entities: string[]): string {
  const imports = entities.map(e => `export * from './entities/${e}.js';`).join('\n');

  return `/**
 * Public API
 */

export * from './types/common.js';
export * from './types/errors.js';
${imports}
`;
}

function generatePackageJson(name: string, domain: string): string {
  return JSON.stringify(
    {
      name: name.toLowerCase().replace(/\s+/g, '-'),
      version: '1.0.0',
      description: `${domain} domain implementation - SDD compliant`,
      type: 'module',
      main: 'dist/index.js',
      types: 'dist/index.d.ts',
      scripts: {
        build: 'tsc',
        test: 'vitest run',
        'test:watch': 'vitest watch',
        'test:coverage': 'vitest run --coverage',
        lint: 'eslint src __tests__',
        typecheck: 'tsc --noEmit',
      },
      dependencies: {
        neverthrow: '^8.1.1',
      },
      devDependencies: {
        typescript: '^5.7.2',
        vitest: '^3.0.4',
        '@vitest/coverage-v8': '^3.0.4',
        '@types/node': '^22.10.2',
      },
      keywords: ['sdd', 'domain-driven-design', 'musubix'],
      license: 'MIT',
    },
    null,
    2
  );
}

function generateTsConfig(): string {
  return JSON.stringify(
    {
      compilerOptions: {
        target: 'ES2022',
        module: 'NodeNext',
        moduleResolution: 'NodeNext',
        declaration: true,
        outDir: './dist',
        rootDir: './src',
        strict: true,
        esModuleInterop: true,
        skipLibCheck: true,
        forceConsistentCasingInFileNames: true,
        resolveJsonModule: true,
      },
      include: ['src/**/*'],
      exclude: ['node_modules', 'dist', '__tests__'],
    },
    null,
    2
  );
}

function generateVitestConfig(): string {
  return `import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    globals: true,
    environment: 'node',
    include: ['__tests__/**/*.test.ts'],
    coverage: {
      provider: 'v8',
      reporter: ['text', 'json', 'html'],
      include: ['src/**/*.ts'],
      exclude: ['src/**/*.d.ts'],
    },
  },
});
`;
}

function generateKnowledgeConfig(domain: string): string {
  return JSON.stringify(
    {
      version: '1.0.0',
      metadata: {
        name: domain,
        created: new Date().toISOString(),
      },
      entities: [],
      relations: [],
    },
    null,
    2
  );
}

/**
 * Convert PascalCase to kebab-case
 */
function toKebabCase(str: string): string {
  return str
    .replace(/([a-z])([A-Z])/g, '$1-$2')
    .replace(/([A-Z])([A-Z][a-z])/g, '$1-$2')
    .toLowerCase();
}

/**
 * Generate Value Object template (BP-CODE-004 pattern)
 */
function generateValueObjectTemplate(domain: string, voName: string): string {
  const kebabName = toKebabCase(voName);
  return `/**
 * ${voName} Value Object
 *
 * @pattern BP-CODE-004 Function-based Value Objects
 * @requirement REQ-${domain}-VO-${voName}
 */

import { Result, ok, err } from '../types/common.js';
import { ValidationError } from '../types/errors.js';

/**
 * ${voName} interface
 */
export interface ${voName} {
  readonly value: string;
}

/**
 * ${voName} input
 */
export interface ${voName}Input {
  value: string;
}

/**
 * Create ${voName} with validation
 */
export function create${voName}(input: ${voName}Input): Result<${voName}, ValidationError> {
  const { value } = input;

  // Add validation rules here
  if (!value || value.trim().length === 0) {
    return err(new ValidationError('${voName} value cannot be empty'));
  }

  return ok({
    value: value.trim(),
  });
}

/**
 * Check if two ${voName} values are equal
 */
export function equals${voName}(a: ${voName}, b: ${voName}): boolean {
  return a.value === b.value;
}
`;
}

/**
 * Generate Value Object test template
 */
function generateValueObjectTestTemplate(domain: string, voName: string): string {
  return `/**
 * ${voName} Value Object Tests
 *
 * @pattern BP-TEST-004 Result Type Test Pattern
 * @requirement REQ-${domain}-VO-${voName}
 */

import { describe, it, expect } from 'vitest';
import { create${voName}, equals${voName} } from '../src/value-objects/${toKebabCase(voName)}.js';

describe('${voName}', () => {
  describe('create${voName}', () => {
    it('should create valid ${voName}', () => {
      const result = create${voName}({ value: 'test' });
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.value).toBe('test');
      }
    });

    it('should reject empty value', () => {
      const result = create${voName}({ value: '' });
      expect(result.isErr()).toBe(true);
      if (result.isErr()) {
        expect(result.error.message).toContain('empty');
      }
    });

    it('should trim whitespace', () => {
      const result = create${voName}({ value: '  test  ' });
      expect(result.isOk()).toBe(true);
      if (result.isOk()) {
        expect(result.value.value).toBe('test');
      }
    });
  });

  describe('equals${voName}', () => {
    it('should return true for equal values', () => {
      const result1 = create${voName}({ value: 'test' });
      const result2 = create${voName}({ value: 'test' });
      if (result1.isOk() && result2.isOk()) {
        expect(equals${voName}(result1.value, result2.value)).toBe(true);
      }
    });

    it('should return false for different values', () => {
      const result1 = create${voName}({ value: 'test1' });
      const result2 = create${voName}({ value: 'test2' });
      if (result1.isOk() && result2.isOk()) {
        expect(equals${voName}(result1.value, result2.value)).toBe(false);
      }
    });
  });
});
`;
}

/**
 * Generate Status machine template (BP-DESIGN-001 pattern)
 */
function generateStatusTemplate(domain: string, statusName: string): string {
  return `/**
 * ${statusName} Status Transitions
 *
 * @pattern BP-DESIGN-001 Status Transition Map
 * @requirement REQ-${domain}-STATUS-${statusName}
 * @generated by MUSUBIX StatusTransitionGenerator
 */

/**
 * ${statusName}Status - Valid status values
 */
export type ${statusName}Status = 'draft' | 'active' | 'completed' | 'cancelled';

/**
 * All valid ${statusName}Status values
 */
export const ${statusName.toLowerCase()}StatusValues: readonly ${statusName}Status[] = ['draft', 'active', 'completed', 'cancelled'] as const;

/**
 * Valid status transitions map
 *
 * @pattern BP-DESIGN-001 Status Transition Map
 */
export const valid${statusName}Transitions: Record<${statusName}Status, ${statusName}Status[]> = {
  'draft': ['active', 'cancelled'],
  'active': ['completed', 'cancelled'],
  'completed': [],
  'cancelled': [],
};

/**
 * Check if a status transition is valid
 */
export function canTransition${statusName}Status(from: ${statusName}Status, to: ${statusName}Status): boolean {
  return valid${statusName}Transitions[from].includes(to);
}

/**
 * Get the initial status for ${statusName}
 */
export function getInitial${statusName}Status(): ${statusName}Status {
  return 'draft';
}

/**
 * Check if a status is terminal (no further transitions)
 */
export function isTerminal${statusName}Status(status: ${statusName}Status): boolean {
  const terminalStatuses: ${statusName}Status[] = ['completed', 'cancelled'];
  return terminalStatuses.includes(status);
}

/**
 * Get all valid next statuses from the current status
 */
export function getNext${statusName}Statuses(current: ${statusName}Status): ${statusName}Status[] {
  return valid${statusName}Transitions[current];
}

/**
 * Assert that a status transition is valid
 * @throws Error if the transition is not valid
 */
export function assertValid${statusName}Transition(from: ${statusName}Status, to: ${statusName}Status): void {
  if (!canTransition${statusName}Status(from, to)) {
    throw new Error(\`Invalid ${statusName} status transition: \${from} -> \${to}\`);
  }
}
`;
}

/**
 * Generate Status test template (BP-TEST-005 pattern)
 */
function generateStatusTestTemplate(domain: string, statusName: string): string {
  const kebabName = toKebabCase(statusName);
  return `/**
 * ${statusName} Status Transition Tests
 *
 * @pattern BP-TEST-005 Status Transition Testing
 * @requirement REQ-${domain}-STATUS-${statusName}
 */

import { describe, it, expect } from 'vitest';
import {
  ${statusName}Status,
  canTransition${statusName}Status,
  valid${statusName}Transitions,
  getNext${statusName}Statuses,
  getInitial${statusName}Status,
  isTerminal${statusName}Status,
} from '../src/statuses/${kebabName}-status.js';

describe('${statusName}Status Transitions', () => {
  describe('valid transitions', () => {
    const validCases: Array<{ from: ${statusName}Status; to: ${statusName}Status }> = [
      { from: 'draft', to: 'active' },
      { from: 'draft', to: 'cancelled' },
      { from: 'active', to: 'completed' },
      { from: 'active', to: 'cancelled' },
    ];

    it.each(validCases)('should allow transition from $from to $to', ({ from, to }) => {
      expect(canTransition${statusName}Status(from, to)).toBe(true);
    });
  });

  describe('invalid transitions', () => {
    const invalidCases: Array<{ from: ${statusName}Status; to: ${statusName}Status }> = [
      { from: 'draft', to: 'completed' },
      { from: 'completed', to: 'draft' },
      { from: 'cancelled', to: 'active' },
    ];

    it.each(invalidCases)('should reject transition from $from to $to', ({ from, to }) => {
      expect(canTransition${statusName}Status(from, to)).toBe(false);
    });
  });

  describe('edge cases', () => {
    it('should reject self-transition', () => {
      expect(canTransition${statusName}Status('draft', 'draft')).toBe(false);
    });

    it('should have no transitions from terminal status', () => {
      const nextStatuses = getNext${statusName}Statuses('completed');
      expect(nextStatuses).toHaveLength(0);
    });

    it('should return correct initial status', () => {
      expect(getInitial${statusName}Status()).toBe('draft');
    });

    it('should identify terminal statuses', () => {
      expect(isTerminal${statusName}Status('completed')).toBe(true);
      expect(isTerminal${statusName}Status('cancelled')).toBe(true);
      expect(isTerminal${statusName}Status('draft')).toBe(false);
    });

    it('should have transitions defined for all statuses', () => {
      const statuses: ${statusName}Status[] = ['draft', 'active', 'completed', 'cancelled'];
      for (const status of statuses) {
        expect(valid${statusName}Transitions[status]).toBeDefined();
      }
    });
  });
});
`;
}
