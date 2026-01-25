/**
 * Codemap Implementation
 *
 * REQ-CM-001: Repository Structure Analysis
 * REQ-CM-002: Module Analysis
 * REQ-CM-003: Codemap Generation
 * REQ-CM-004: Codemap Diff Threshold & Report
 *
 * @packageDocumentation
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import { createHash } from 'crypto';
import {
  type CodemapConfig,
  type CodemapDiff,
  type CodemapDocument,
  type CodemapGenerationResult,
  type CodemapManager,
  type DatabaseModelInfo,
  type DirectoryInfo,
  type EntryPoint,
  type ExportInfo,
  type FrameworkInfo,
  type ImportInfo,
  type ModuleAnalysis,
  type ModuleType,
  type RepositoryStructure,
  type RouteInfo,
  type WorkerInfo,
  DEFAULT_CODEMAP_CONFIG,
} from './types.js';

/**
 * Create hash from content
 */
function hashContent(content: string): string {
  return createHash('md5').update(content).digest('hex').slice(0, 8);
}

/**
 * Calculate Levenshtein distance for diff percentage
 */
function calculateDiffPercent(oldContent: string, newContent: string): number {
  if (oldContent === newContent) return 0;
  if (!oldContent) return 100;
  if (!newContent) return 100;

  const oldLines = oldContent.split('\n');
  const newLines = newContent.split('\n');

  const totalLines = Math.max(oldLines.length, newLines.length);
  let changedLines = 0;

  for (let i = 0; i < totalLines; i++) {
    if (oldLines[i] !== newLines[i]) {
      changedLines++;
    }
  }

  return Math.round((changedLines / totalLines) * 100);
}

/**
 * Detect framework from package.json
 */
function detectFrameworks(packageJson: Record<string, unknown>): FrameworkInfo[] {
  const frameworks: FrameworkInfo[] = [];
  const deps = {
    ...(packageJson.dependencies as Record<string, string> || {}),
    ...(packageJson.devDependencies as Record<string, string> || {}),
  };

  // React
  if (deps['react']) {
    frameworks.push({
      name: 'React',
      version: deps['react'],
      patterns: ['src/components', 'src/pages'],
    });
  }

  // Next.js
  if (deps['next']) {
    frameworks.push({
      name: 'Next.js',
      version: deps['next'],
      patterns: ['pages', 'app', 'src/app'],
    });
  }

  // Express
  if (deps['express']) {
    frameworks.push({
      name: 'Express',
      version: deps['express'],
      patterns: ['src/routes', 'src/controllers'],
    });
  }

  // NestJS
  if (deps['@nestjs/core']) {
    frameworks.push({
      name: 'NestJS',
      version: deps['@nestjs/core'],
      patterns: ['src/modules', 'src/controllers'],
    });
  }

  // Vite
  if (deps['vite']) {
    frameworks.push({
      name: 'Vite',
      version: deps['vite'],
      patterns: ['src'],
    });
  }

  return frameworks;
}

/**
 * Detect module type from path and content
 */
function detectModuleType(modulePath: string): ModuleType {
  const normalizedPath = modulePath.toLowerCase();

  if (normalizedPath.includes('frontend') || normalizedPath.includes('client')) {
    return 'frontend';
  }
  if (normalizedPath.includes('backend') || normalizedPath.includes('server') || normalizedPath.includes('api')) {
    return 'backend';
  }
  if (normalizedPath.includes('database') || normalizedPath.includes('db') || normalizedPath.includes('models')) {
    return 'database';
  }
  if (normalizedPath.includes('integration') || normalizedPath.includes('external')) {
    return 'integration';
  }
  if (normalizedPath.includes('worker') || normalizedPath.includes('jobs') || normalizedPath.includes('cron')) {
    return 'worker';
  }
  if (normalizedPath.includes('shared') || normalizedPath.includes('common') || normalizedPath.includes('utils')) {
    return 'shared';
  }

  return 'unknown';
}

/**
 * Parse exports from TypeScript/JavaScript content
 */
function parseExports(content: string, file: string): ExportInfo[] {
  const exports: ExportInfo[] = [];

  // export function
  const funcRegex = /export\s+(?:async\s+)?function\s+(\w+)/g;
  let match;
  while ((match = funcRegex.exec(content))) {
    exports.push({
      name: match[1],
      type: 'function',
      file,
    });
  }

  // export class
  const classRegex = /export\s+class\s+(\w+)/g;
  while ((match = classRegex.exec(content))) {
    exports.push({
      name: match[1],
      type: 'class',
      file,
    });
  }

  // export interface
  const interfaceRegex = /export\s+interface\s+(\w+)/g;
  while ((match = interfaceRegex.exec(content))) {
    exports.push({
      name: match[1],
      type: 'interface',
      file,
    });
  }

  // export type
  const typeRegex = /export\s+type\s+(\w+)/g;
  while ((match = typeRegex.exec(content))) {
    exports.push({
      name: match[1],
      type: 'type',
      file,
    });
  }

  // export const
  const constRegex = /export\s+const\s+(\w+)/g;
  while ((match = constRegex.exec(content))) {
    exports.push({
      name: match[1],
      type: 'const',
      file,
    });
  }

  // export default
  if (/export\s+default/.test(content)) {
    exports.push({
      name: 'default',
      type: 'default',
      file,
    });
  }

  return exports;
}

/**
 * Parse imports from TypeScript/JavaScript content
 */
function parseImports(content: string, file: string): ImportInfo[] {
  const imports: ImportInfo[] = [];

  const importRegex = /import\s+(?:{([^}]+)}|(\w+))\s+from\s+['"]([^'"]+)['"]/g;
  let match;

  while ((match = importRegex.exec(content))) {
    const namedImports = match[1];
    const defaultImport = match[2];
    const moduleName = match[3];

    const importedNames: string[] = [];
    if (namedImports) {
      importedNames.push(
        ...namedImports.split(',').map((s) => s.trim().split(' as ')[0])
      );
    }
    if (defaultImport) {
      importedNames.push(defaultImport);
    }

    imports.push({
      module: moduleName,
      isExternal: !moduleName.startsWith('.') && !moduleName.startsWith('/'),
      importedNames,
      file,
    });
  }

  return imports;
}

/**
 * Create codemap manager
 *
 * @param config - Configuration options
 * @returns CodemapManager instance
 */
export function createCodemapManager(
  config: Partial<CodemapConfig> = {}
): CodemapManager {
  const fullConfig: CodemapConfig = {
    ...DEFAULT_CODEMAP_CONFIG,
    ...config,
  };

  return {
    async analyzeRepository(): Promise<RepositoryStructure> {
      const root = fullConfig.projectRoot;
      const packageJsonPath = path.join(root, 'package.json');

      let packageJson: Record<string, unknown> = {};
      let workspaces: string[] = [];
      let monorepo = false;

      try {
        const content = await fs.readFile(packageJsonPath, 'utf-8');
        packageJson = JSON.parse(content);

        // Check for workspaces
        if (packageJson.workspaces) {
          workspaces = Array.isArray(packageJson.workspaces)
            ? packageJson.workspaces
            : (packageJson.workspaces as { packages?: string[] }).packages || [];
          monorepo = workspaces.length > 0;
        }
      } catch {
        // No package.json
      }

      const frameworks = detectFrameworks(packageJson);

      // Scan directories
      const directories: DirectoryInfo[] = [];
      const entryPoints: EntryPoint[] = [];

      try {
        const entries = await fs.readdir(root, { withFileTypes: true });

        for (const entry of entries) {
          if (entry.isDirectory() && !entry.name.startsWith('.')) {
            const dirPath = path.join(root, entry.name);
            let fileCount = 0;
            const languages = new Set<string>();

            try {
              const files = await fs.readdir(dirPath, { recursive: true });
              for (const file of files) {
                if (typeof file === 'string') {
                  fileCount++;
                  const ext = path.extname(file);
                  if (ext) languages.add(ext);
                }
              }
            } catch {
              // Skip unreadable directories
            }

            directories.push({
              path: entry.name,
              purpose: detectModuleType(entry.name),
              fileCount,
              languages: Array.from(languages),
            });
          }
        }

        // Detect entry points
        const possibleEntryPoints = [
          'src/index.ts',
          'src/main.ts',
          'src/app.ts',
          'index.ts',
          'main.ts',
          'server.ts',
          'bin/cli.js',
        ];

        for (const ep of possibleEntryPoints) {
          try {
            await fs.access(path.join(root, ep));
            entryPoints.push({
              path: ep,
              type: ep.includes('cli') ? 'cli' : ep.includes('server') ? 'server' : 'main',
            });
          } catch {
            // Entry point doesn't exist
          }
        }
      } catch {
        // Root directory issues
      }

      return {
        name: (packageJson.name as string) || path.basename(root),
        root,
        workspaces,
        directories,
        entryPoints,
        frameworks,
        monorepo,
      };
    },

    async analyzeModule(modulePath: string): Promise<ModuleAnalysis> {
      const fullPath = path.resolve(fullConfig.projectRoot, modulePath);
      const type = detectModuleType(modulePath);

      const exports: ExportInfo[] = [];
      const imports: ImportInfo[] = [];
      const routes: RouteInfo[] = [];
      const databaseModels: DatabaseModelInfo[] = [];
      const workers: WorkerInfo[] = [];

      try {
        const stat = await fs.stat(fullPath);

        if (stat.isFile()) {
          const content = await fs.readFile(fullPath, 'utf-8');
          exports.push(...parseExports(content, modulePath));
          imports.push(...parseImports(content, modulePath));
        } else if (stat.isDirectory()) {
          const files = await fs.readdir(fullPath, { recursive: true });

          for (const file of files) {
            if (typeof file === 'string' && (file.endsWith('.ts') || file.endsWith('.js'))) {
              const filePath = path.join(fullPath, file);
              try {
                const content = await fs.readFile(filePath, 'utf-8');
                const relPath = path.join(modulePath, file);
                exports.push(...parseExports(content, relPath));
                imports.push(...parseImports(content, relPath));

                // Detect routes (Express-style)
                const routeRegex = /\.(get|post|put|delete|patch)\s*\(\s*['"]([^'"]+)['"]/gi;
                let routeMatch;
                while ((routeMatch = routeRegex.exec(content))) {
                  routes.push({
                    path: routeMatch[2],
                    method: routeMatch[1].toUpperCase() as RouteInfo['method'],
                    handler: file,
                    file: relPath,
                  });
                }

                // Detect database models
                if (content.includes('@Entity') || content.includes('Schema(')) {
                  const modelMatch = content.match(/(?:@Entity|Schema)\s*\(\s*['"]?(\w+)['"]?\s*\)/);
                  if (modelMatch) {
                    databaseModels.push({
                      name: modelMatch[1],
                      type: content.includes('@Entity') ? 'entity' : 'collection',
                      file: relPath,
                    });
                  }
                }

                // Detect workers
                if (content.includes('@Cron') || content.includes('schedule(')) {
                  workers.push({
                    name: path.basename(file, path.extname(file)),
                    type: 'cron',
                    file: relPath,
                  });
                }
              } catch {
                // Skip unreadable files
              }
            }
          }
        }
      } catch {
        // Module not found
      }

      // Get dependencies from package.json if it exists
      let dependencies: string[] = [];
      let devDependencies: string[] = [];

      try {
        const pkgPath = path.join(fullPath, 'package.json');
        const pkgContent = await fs.readFile(pkgPath, 'utf-8');
        const pkg = JSON.parse(pkgContent);
        dependencies = Object.keys(pkg.dependencies || {});
        devDependencies = Object.keys(pkg.devDependencies || {});
      } catch {
        // No package.json in module
      }

      return {
        path: modulePath,
        type,
        exports,
        imports,
        routes,
        databaseModels,
        workers,
        dependencies,
        devDependencies,
      };
    },

    async generateCodemap(): Promise<CodemapGenerationResult> {
      const repo = await this.analyzeRepository();
      const documents: CodemapDocument[] = [];
      const diffs: CodemapDiff[] = [];
      const generatedAt = new Date();

      // Generate INDEX.md
      const indexContent = generateIndexDocument(repo);
      documents.push({
        name: 'INDEX.md',
        path: path.join(fullConfig.outputDir, 'INDEX.md'),
        content: indexContent,
        generatedAt,
      });

      // Check for existing documents and calculate diffs
      for (const doc of documents) {
        try {
          const existingContent = await fs.readFile(doc.path, 'utf-8');
          const diff = this.calculateDiff(doc.content, existingContent);
          diffs.push({ ...diff, documentName: doc.name });
        } catch {
          // No existing document
        }
      }

      const totalDiffPercent =
        diffs.length > 0
          ? Math.round(
              diffs.reduce((sum, d) => sum + d.diffPercent, 0) / diffs.length
            )
          : 0;

      return {
        documents,
        diffs,
        totalDiffPercent,
        generatedAt,
      };
    },

    calculateDiff(newContent: string, existingContent: string): CodemapDiff {
      const diffPercent = calculateDiffPercent(existingContent, newContent);
      const oldLines = existingContent.split('\n');
      const newLines = newContent.split('\n');

      let additions = 0;
      let deletions = 0;

      for (const line of newLines) {
        if (!oldLines.includes(line)) additions++;
      }
      for (const line of oldLines) {
        if (!newLines.includes(line)) deletions++;
      }

      return {
        documentName: '',
        previousHash: hashContent(existingContent),
        currentHash: hashContent(newContent),
        diffPercent,
        additions,
        deletions,
        requiresApproval: diffPercent > fullConfig.diffThresholdPercent,
      };
    },

    async saveCodemap(result: CodemapGenerationResult): Promise<string[]> {
      const savedPaths: string[] = [];

      await fs.mkdir(fullConfig.outputDir, { recursive: true });

      for (const doc of result.documents) {
        await fs.writeFile(doc.path, doc.content);
        savedPaths.push(doc.path);
      }

      // Write diff report
      const diffReportPath = path.join('.reports', 'codemap-diff.txt');
      await fs.mkdir(path.dirname(diffReportPath), { recursive: true });

      const diffReport = result.diffs
        .map((d) => `${d.documentName}: ${d.diffPercent}% changed (+${d.additions}/-${d.deletions})`)
        .join('\n');

      await fs.writeFile(diffReportPath, diffReport || 'No changes detected');
      savedPaths.push(diffReportPath);

      return savedPaths;
    },

    getConfig(): CodemapConfig {
      return fullConfig;
    },
  };
}

/**
 * Generate INDEX.md document
 */
function generateIndexDocument(repo: RepositoryStructure): string {
  const workspacesList =
    repo.workspaces.length > 0
      ? repo.workspaces.map((w) => `- ${w}`).join('\n')
      : '(単一パッケージ)';

  const frameworksList =
    repo.frameworks.length > 0
      ? repo.frameworks.map((f) => `- ${f.name} ${f.version || ''}`).join('\n')
      : '(なし)';

  const entryPointsList =
    repo.entryPoints.length > 0
      ? repo.entryPoints.map((e) => `- \`${e.path}\` (${e.type})`).join('\n')
      : '(なし)';

  const directoriesList = repo.directories
    .map(
      (d) =>
        `| ${d.path} | ${d.purpose} | ${d.fileCount} | ${d.languages.slice(0, 3).join(', ')} |`
    )
    .join('\n');

  return `# ${repo.name} - Code Map

Generated: ${new Date().toISOString()}

## Overview

| Property | Value |
|----------|-------|
| Root | \`${repo.root}\` |
| Monorepo | ${repo.monorepo ? 'Yes' : 'No'} |
| Workspaces | ${repo.workspaces.length} |

## Workspaces

${workspacesList}

## Frameworks & Libraries

${frameworksList}

## Entry Points

${entryPointsList}

## Directory Structure

| Directory | Purpose | Files | Languages |
|-----------|---------|-------|-----------|
${directoriesList}

## Navigation

- [Frontend](./frontend.md)
- [Backend](./backend.md)
- [Database](./database.md)
- [Integrations](./integrations.md)
- [Workers](./workers.md)
`;
}

/**
 * Format codemap generation result as markdown
 *
 * @param result - Generation result
 * @returns Markdown string
 */
export function formatCodemapResultMarkdown(
  result: CodemapGenerationResult
): string {
  const docList = result.documents
    .map((d) => `- ${d.name}`)
    .join('\n');

  const diffList =
    result.diffs.length > 0
      ? result.diffs
          .map(
            (d) =>
              `- ${d.documentName}: ${d.diffPercent}% ${d.requiresApproval ? '⚠️ 要承認' : '✅'}`
          )
          .join('\n')
      : '(変更なし)';

  return `Codemap Generation Report
=========================

生成日時: ${result.generatedAt.toISOString()}
総差分率: ${result.totalDiffPercent}%

生成ドキュメント:
${docList}

差分:
${diffList}`;
}
