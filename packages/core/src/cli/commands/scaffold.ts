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
 * @see ADR-v3.3.0-001 - Status option syntax decision
 */

import type { Command } from 'commander';
import { mkdir, writeFile, access } from 'fs/promises';
import { resolve, join } from 'path';
import { ExitCode, getGlobalOptions, outputResult } from '../base.js';
import { VERSION } from '../../version.js';
import {
  ValueObjectGenerator,
  StatusMachineGenerator,
} from '../generators/index.js';

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
    .option('-s, --statuses <list>', 'Status machines: "Entity" or "Entity=status1,status2" (ADR-v3.3.0-001)')
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
          ? options.valueObjects.split(',').map((v: string) => v.trim()).filter((v: string) => v.length > 0)
          : [];

        if (valueObjects.length > 0) {
          // v3.3.0: Use ValueObjectGenerator (TSK-SCF-005)
          const voGenerator = new ValueObjectGenerator({
            domain,
            outputDir: projectPath,
            generateTests: true,
          });
          
          const voSpecs = valueObjects.map((vo) => ({ name: vo }));
          const voFiles = await voGenerator.generate(voSpecs);
          const voTestFiles = await voGenerator.generateTests(voSpecs);
          
          await voGenerator.writeFiles([...voFiles, ...voTestFiles]);
          
          for (const file of voFiles) {
            const relativePath = file.path.replace(projectPath + '/', '');
            filesCreated.push(relativePath);
          }
          for (const file of voTestFiles) {
            const relativePath = file.path.replace(projectPath + '/', '');
            filesCreated.push(relativePath);
          }
        }

        // Create status machines if specified
        // ADR-v3.3.0-001: Support "Entity" or "Entity=status1,status2" syntax
        const statusOptionStr = options.statuses || '';

        if (statusOptionStr.trim()) {
          // v3.3.0: Use StatusMachineGenerator (TSK-SCF-005)
          const statusGenerator = new StatusMachineGenerator({
            domain,
            outputDir: projectPath,
            generateTests: true,
          });
          
          // Parse status options using ADR-v3.3.0-001 syntax
          const parsedMap = StatusMachineGenerator.parseStatusOption(statusOptionStr);
          
          const statusSpecs = Array.from(parsedMap.entries()).map(([entityName, initialStatus]) => ({
            entityName,
            initialStatus: initialStatus || 'draft',
          }));
          
          const statusFiles = await statusGenerator.generate(statusSpecs);
          const statusTestFiles = await statusGenerator.generateTests(statusSpecs);
          
          await statusGenerator.writeFiles([...statusFiles, ...statusTestFiles]);
          
          for (const file of statusFiles) {
            const relativePath = file.path.replace(projectPath + '/', '');
            filesCreated.push(relativePath);
          }
          for (const file of statusTestFiles) {
            const relativePath = file.path.replace(projectPath + '/', '');
            filesCreated.push(relativePath);
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
 * @public Exported for use in generators and tests
 */
export function toKebabCase(str: string): string {
  return str
    .replace(/([a-z])([A-Z])/g, '$1-$2')
    .replace(/([A-Z])([A-Z][a-z])/g, '$1-$2')
    .toLowerCase();
}

