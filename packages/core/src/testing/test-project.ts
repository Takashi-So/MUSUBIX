/**
 * Test Project Factory
 *
 * @fileoverview Creates and manages test project directories
 * @module @musubix/core/testing/test-project
 * @requirement REQ-E2E-001
 */

import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';
import type { ITestProject, TestProjectOptions, ProjectTemplate } from './types.js';

/**
 * Test project implementation
 */
class TestProject implements ITestProject {
  readonly path: string;
  readonly name: string;
  private readonly cleanup: boolean;
  private created = false;

  constructor(options: TestProjectOptions = {}) {
    this.name = options.name || `musubix-test-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
    this.cleanup = options.cleanup ?? true;
    const baseDir = options.baseDir || path.join(os.tmpdir(), 'musubix-e2e');
    this.path = path.join(baseDir, this.name);
  }

  /**
   * Create the test project directory
   */
  async create(): Promise<void> {
    if (this.created) return;

    // Ensure base directory exists
    const baseDir = path.dirname(this.path);
    if (!fs.existsSync(baseDir)) {
      fs.mkdirSync(baseDir, { recursive: true });
    }

    // Create project directory
    if (!fs.existsSync(this.path)) {
      fs.mkdirSync(this.path, { recursive: true });
    }

    this.created = true;
  }

  /**
   * Destroy the test project directory
   */
  async destroy(): Promise<void> {
    if (!this.created || !this.cleanup) return;

    if (fs.existsSync(this.path)) {
      fs.rmSync(this.path, { recursive: true, force: true });
    }
    this.created = false;
  }

  /**
   * Add a file to the project
   */
  async addFile(relativePath: string, content: string): Promise<void> {
    if (!this.created) {
      await this.create();
    }

    const filePath = path.join(this.path, relativePath);
    const dir = path.dirname(filePath);

    if (!fs.existsSync(dir)) {
      fs.mkdirSync(dir, { recursive: true });
    }

    fs.writeFileSync(filePath, content, 'utf-8');
  }

  /**
   * Get file content from the project
   */
  async getFile(relativePath: string): Promise<string> {
    const filePath = path.join(this.path, relativePath);
    return fs.readFileSync(filePath, 'utf-8');
  }

  /**
   * Check if a file exists in the project
   */
  fileExists(relativePath: string): boolean {
    const filePath = path.join(this.path, relativePath);
    return fs.existsSync(filePath);
  }
}

/**
 * Template content generators
 */
const templateGenerators: Record<ProjectTemplate, (project: ITestProject) => Promise<void>> = {
  minimal: async (project) => {
    await project.addFile('package.json', JSON.stringify({
      name: project.name,
      version: '1.0.0',
      type: 'module',
    }, null, 2));
  },

  full: async (project) => {
    await project.addFile('package.json', JSON.stringify({
      name: project.name,
      version: '1.0.0',
      type: 'module',
      scripts: {
        test: 'vitest run',
        build: 'tsc',
      },
    }, null, 2));

    await project.addFile('tsconfig.json', JSON.stringify({
      compilerOptions: {
        target: 'ES2022',
        module: 'NodeNext',
        strict: true,
        outDir: 'dist',
      },
      include: ['src/**/*'],
    }, null, 2));

    await project.addFile('src/index.ts', '// Entry point\nexport const VERSION = "1.0.0";\n');
  },

  sdd: async (project) => {
    // Package.json
    await project.addFile('package.json', JSON.stringify({
      name: project.name,
      version: '1.0.0',
      type: 'module',
    }, null, 2));

    // Sample requirements
    await project.addFile('requirements.md', `# Requirements

## REQ-001: User Authentication

THE system SHALL provide user authentication functionality.

### EARS Pattern: Ubiquitous

THE authentication system SHALL validate user credentials before granting access.

## REQ-002: Session Management

WHEN a user logs in successfully, THE system SHALL create a session with a unique token.

### EARS Pattern: Event-driven
`);

    // Sample design
    await project.addFile('design.md', `# Design

## DES-001: Authentication Module

### C4 Context

\`\`\`
[User] -> [Authentication System] -> [User Database]
\`\`\`

### Components

- AuthController
- AuthService
- UserRepository

### Traceability

- REQ-001 -> DES-001
`);

    // Sample code
    await project.addFile('src/auth/auth-service.ts', `/**
 * Authentication Service
 * @requirement REQ-001
 * @design DES-001
 */
export class AuthService {
  async authenticate(username: string, password: string): Promise<boolean> {
    // TODO: Implement authentication
    return username.length > 0 && password.length > 0;
  }
}
`);

    // Storage directories
    await project.addFile('storage/specs/.gitkeep', '');
    await project.addFile('storage/design/.gitkeep', '');
    await project.addFile('storage/traceability/.gitkeep', '');
  },
};

/**
 * Create a new test project
 *
 * @param options - Project options
 * @returns Test project instance
 *
 * @example
 * ```typescript
 * const project = createTestProject({ template: 'sdd' });
 * await project.create();
 * await project.addFile('test.txt', 'Hello');
 * // ... run tests
 * await project.destroy();
 * ```
 */
export function createTestProject(options: TestProjectOptions = {}): ITestProject {
  return new TestProject(options);
}

/**
 * Create and initialize a test project with template
 *
 * @param options - Project options
 * @returns Initialized test project
 */
export async function createTestProjectWithTemplate(
  options: TestProjectOptions = {}
): Promise<ITestProject> {
  const project = createTestProject(options);
  await project.create();

  const template = options.template || 'minimal';
  const generator = templateGenerators[template];
  if (generator) {
    await generator(project);
  }

  return project;
}

/**
 * Use test project in a test block (auto cleanup)
 *
 * @param options - Project options
 * @param fn - Test function
 *
 * @example
 * ```typescript
 * await withTestProject({ template: 'sdd' }, async (project) => {
 *   // project is created and initialized
 *   expect(project.fileExists('requirements.md')).toBe(true);
 *   // auto cleanup after function returns
 * });
 * ```
 */
export async function withTestProject<T>(
  options: TestProjectOptions,
  fn: (project: ITestProject) => Promise<T>
): Promise<T> {
  const project = await createTestProjectWithTemplate(options);
  try {
    return await fn(project);
  } finally {
    await project.destroy();
  }
}
