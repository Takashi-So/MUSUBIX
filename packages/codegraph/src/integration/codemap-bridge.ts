/**
 * @fileoverview Codemap Bridge Implementation for Agent Skills Integration
 * @traceability REQ-CM-001, REQ-CM-002, REQ-CM-003, REQ-CM-004
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import { createHash } from 'crypto';
import type {
  CodemapBridge,
  CodemapBridgeConfig,
  PackageInfo,
  DirectoryNode,
  EntryPoint,
  FrameworkInfo,
  ModuleAnalysisResult,
  ModuleExport,
  ModuleImport,
  Codemap,
  CodemapDocument,
  CodemapDiff,
} from './codemap-types.js';
import {
  DEFAULT_CODEMAP_BRIDGE_CONFIG,
} from './codemap-types.js';
import type { Language } from '../types.js';
import { LANGUAGE_EXTENSIONS } from '../types.js';

/**
 * Create a Codemap Bridge for Agent Skills integration
 * @param config Bridge configuration
 * @returns CodemapBridge instance
 */
export function createCodemapBridge(
  config: Partial<CodemapBridgeConfig> = {}
): CodemapBridge {
  let currentConfig: CodemapBridgeConfig = {
    ...DEFAULT_CODEMAP_BRIDGE_CONFIG,
    ...config,
  };

  return {
    async analyzeStructure(rootPath: string) {
      const packages = await analyzePackages(rootPath);
      const structure = await buildDirectoryTree(rootPath, currentConfig.maxDepth, currentConfig);
      const entryPoints = await detectEntryPoints(rootPath, packages);
      const frameworks = await detectFrameworks(rootPath);

      return { packages, structure, entryPoints, frameworks };
    },

    async analyzeModule(modulePath: string): Promise<ModuleAnalysisResult> {
      const content = await fs.readFile(modulePath, 'utf-8');
      const lines = content.split('\n');
      const exports = extractExports(content, modulePath);
      const imports = extractImports(content);
      const entityCounts = countEntities(content);

      return {
        path: modulePath,
        name: path.basename(modulePath, path.extname(modulePath)),
        exports,
        imports,
        entityCounts,
        linesOfCode: lines.length,
        complexity: calculateComplexity(content),
      };
    },

    async generateCodemap(rootPath: string): Promise<Codemap> {
      const { packages, structure, entryPoints, frameworks } = await this.analyzeStructure(rootPath);
      
      // Read project info
      const packageJsonPath = path.join(rootPath, 'package.json');
      let projectName = path.basename(rootPath);
      let projectVersion: string | undefined;
      
      try {
        const packageJson = JSON.parse(await fs.readFile(packageJsonPath, 'utf-8'));
        projectName = packageJson.name || projectName;
        projectVersion = packageJson.version;
      } catch {
        // No package.json, use directory name
      }

      const documents = await generateDocuments(rootPath, packages, entryPoints, frameworks, structure);

      return {
        projectName,
        projectVersion,
        generatedAt: new Date().toISOString(),
        documents,
        packages,
        entryPoints,
        frameworks,
        structure,
      };
    },

    compareCodemaps(previous: Codemap, current: Codemap): CodemapDiff {
      const prevHash = hashCodemap(previous);
      const currHash = hashCodemap(current);

      const prevPackageNames = new Set(previous.packages.map(p => p.name));
      const currPackageNames = new Set(current.packages.map(p => p.name));

      const addedPackages = [...currPackageNames].filter(n => !prevPackageNames.has(n));
      const removedPackages = [...prevPackageNames].filter(n => !currPackageNames.has(n));
      const modifiedPackages = [...currPackageNames].filter(n => {
        if (!prevPackageNames.has(n)) return false;
        const prev = previous.packages.find(p => p.name === n);
        const curr = current.packages.find(p => p.name === n);
        return prev && curr && JSON.stringify(prev) !== JSON.stringify(curr);
      });

      const prevEntryPoints = new Set(previous.entryPoints.map(e => e.path));
      const currEntryPoints = new Set(current.entryPoints.map(e => e.path));

      const addedEntryPoints = [...currEntryPoints].filter(p => !prevEntryPoints.has(p));
      const removedEntryPoints = [...prevEntryPoints].filter(p => !currEntryPoints.has(p));

      const totalChanges = addedPackages.length + removedPackages.length + modifiedPackages.length +
        addedEntryPoints.length + removedEntryPoints.length;
      const totalItems = Math.max(
        previous.packages.length + previous.entryPoints.length,
        current.packages.length + current.entryPoints.length
      );
      const diffPercentage = totalItems > 0 ? (totalChanges / totalItems) * 100 : 0;

      const majorChanges: string[] = [];
      if (addedPackages.length > 0) majorChanges.push(`Added ${addedPackages.length} package(s)`);
      if (removedPackages.length > 0) majorChanges.push(`Removed ${removedPackages.length} package(s)`);
      if (modifiedPackages.length > 0) majorChanges.push(`Modified ${modifiedPackages.length} package(s)`);

      return {
        previousHash: prevHash,
        currentHash: currHash,
        diffPercentage: Math.round(diffPercentage * 10) / 10,
        addedPackages,
        removedPackages,
        modifiedPackages,
        addedEntryPoints,
        removedEntryPoints,
        majorChanges,
      };
    },

    async writeCodemap(codemap: Codemap, outputDir?: string): Promise<void> {
      const dir = outputDir || currentConfig.outputDir;
      await fs.mkdir(dir, { recursive: true });

      for (const doc of codemap.documents) {
        const fileName = `${doc.type === 'index' ? 'INDEX' : doc.type}.md`;
        const filePath = path.join(dir, fileName);
        await fs.writeFile(filePath, doc.content, 'utf-8');
      }

      // Also write metadata
      const metadataPath = path.join(dir, '.codemap-metadata.json');
      await fs.writeFile(metadataPath, JSON.stringify({
        projectName: codemap.projectName,
        projectVersion: codemap.projectVersion,
        generatedAt: codemap.generatedAt,
        packageCount: codemap.packages.length,
        entryPointCount: codemap.entryPoints.length,
        frameworkCount: codemap.frameworks.length,
      }, null, 2), 'utf-8');
    },

    formatAsMarkdown(codemap: Codemap): string {
      const lines: string[] = [];
      
      lines.push(`# Code Map: ${codemap.projectName}`);
      lines.push('');
      lines.push(`**Generated**: ${codemap.generatedAt}`);
      if (codemap.projectVersion) {
        lines.push(`**Version**: ${codemap.projectVersion}`);
      }
      lines.push('');

      // Package Structure
      lines.push('## Package Structure');
      lines.push('');
      lines.push('| Package | Description | Dependencies |');
      lines.push('|---------|-------------|--------------|');
      for (const pkg of codemap.packages) {
        const deps = pkg.dependencies.slice(0, 3).join(', ') + 
          (pkg.dependencies.length > 3 ? ', ...' : '');
        lines.push(`| ${pkg.name} | ${pkg.description || '-'} | ${deps || '-'} |`);
      }
      lines.push('');

      // Entry Points
      lines.push('## Entry Points');
      lines.push('');
      for (const entry of codemap.entryPoints) {
        lines.push(`- **${entry.type}**: \`${entry.path}\`${entry.description ? ` - ${entry.description}` : ''}`);
      }
      lines.push('');

      // Frameworks
      if (codemap.frameworks.length > 0) {
        lines.push('## Detected Frameworks');
        lines.push('');
        for (const fw of codemap.frameworks) {
          lines.push(`- **${fw.name}**${fw.version ? ` (${fw.version})` : ''} - ${fw.type}`);
        }
        lines.push('');
      }

      return lines.join('\n');
    },

    formatDiffReport(diff: CodemapDiff): string {
      const lines: string[] = [];

      lines.push('Codemap Diff Report');
      lines.push('===================');
      lines.push(`Date: ${new Date().toISOString()}`);
      lines.push(`Previous Hash: ${diff.previousHash.substring(0, 8)}`);
      lines.push(`Current Hash: ${diff.currentHash.substring(0, 8)}`);
      lines.push('');
      lines.push('Summary:');
      lines.push(`- Packages added: ${diff.addedPackages.length}`);
      lines.push(`- Packages removed: ${diff.removedPackages.length}`);
      lines.push(`- Packages modified: ${diff.modifiedPackages.length}`);
      lines.push(`- Entry points added: ${diff.addedEntryPoints.length}`);
      lines.push(`- Entry points removed: ${diff.removedEntryPoints.length}`);
      lines.push(`- Diff percentage: ${diff.diffPercentage}%`);
      lines.push('');

      if (diff.majorChanges.length > 0) {
        lines.push('Major Changes:');
        for (const change of diff.majorChanges) {
          lines.push(`- ${change}`);
        }
      }

      return lines.join('\n');
    },

    getConfig(): CodemapBridgeConfig {
      return { ...currentConfig };
    },

    updateConfig(config: Partial<CodemapBridgeConfig>): void {
      currentConfig = { ...currentConfig, ...config };
    },
  };
}

// ============================================================================
// Helper Functions
// ============================================================================

async function analyzePackages(rootPath: string): Promise<PackageInfo[]> {
  const packages: PackageInfo[] = [];

  // Check for monorepo
  const rootPackageJsonPath = path.join(rootPath, 'package.json');
  try {
    const rootPackageJson = JSON.parse(await fs.readFile(rootPackageJsonPath, 'utf-8'));
    
    // Check workspaces
    const workspaces = rootPackageJson.workspaces || [];
    const workspacePaths: string[] = [];

    for (const ws of workspaces) {
      // Handle glob patterns like "packages/*"
      if (ws.includes('*')) {
        const base = ws.replace('/*', '');
        const basePath = path.join(rootPath, base);
        try {
          const dirs = await fs.readdir(basePath, { withFileTypes: true });
          for (const dir of dirs) {
            if (dir.isDirectory()) {
              workspacePaths.push(path.join(base, dir.name));
            }
          }
        } catch {
          // Directory doesn't exist
        }
      } else {
        workspacePaths.push(ws);
      }
    }

    // Analyze each workspace package
    for (const wsPath of workspacePaths) {
      const pkgJsonPath = path.join(rootPath, wsPath, 'package.json');
      try {
        const pkgJson = JSON.parse(await fs.readFile(pkgJsonPath, 'utf-8'));
        packages.push({
          name: pkgJson.name || path.basename(wsPath),
          version: pkgJson.version,
          path: wsPath,
          description: pkgJson.description,
          main: pkgJson.main,
          exports: pkgJson.exports,
          dependencies: Object.keys(pkgJson.dependencies || {}),
          devDependencies: Object.keys(pkgJson.devDependencies || {}),
        });
      } catch {
        // No package.json
      }
    }

    // If no workspaces, add root as single package
    if (packages.length === 0) {
      packages.push({
        name: rootPackageJson.name || path.basename(rootPath),
        version: rootPackageJson.version,
        path: '.',
        description: rootPackageJson.description,
        main: rootPackageJson.main,
        exports: rootPackageJson.exports,
        dependencies: Object.keys(rootPackageJson.dependencies || {}),
        devDependencies: Object.keys(rootPackageJson.devDependencies || {}),
      });
    }
  } catch {
    // No package.json at root
  }

  return packages;
}

async function buildDirectoryTree(
  dirPath: string,
  maxDepth: number,
  config: CodemapBridgeConfig,
  currentDepth: number = 0
): Promise<DirectoryNode> {
  const name = path.basename(dirPath);
  const node: DirectoryNode = {
    name,
    path: dirPath,
    isDirectory: true,
    children: [],
  };

  if (currentDepth >= maxDepth) {
    return node;
  }

  try {
    const entries = await fs.readdir(dirPath, { withFileTypes: true });

    for (const entry of entries) {
      // Skip common excludes
      if (entry.name.startsWith('.') && entry.name !== '.github') continue;
      if (entry.name === 'node_modules' && !config.includeNodeModules) continue;
      if (entry.name === 'dist' || entry.name === 'build') continue;
      if (!config.includeTests && (entry.name === '__tests__' || entry.name === 'tests')) continue;

      const entryPath = path.join(dirPath, entry.name);

      if (entry.isDirectory()) {
        const child = await buildDirectoryTree(entryPath, maxDepth, config, currentDepth + 1);
        node.children?.push(child);
      } else {
        const ext = path.extname(entry.name);
        const language = LANGUAGE_EXTENSIONS[ext] as Language | undefined;
        node.children?.push({
          name: entry.name,
          path: entryPath,
          isDirectory: false,
          language,
        });
      }
    }
  } catch {
    // Directory read error
  }

  return node;
}

async function detectEntryPoints(rootPath: string, packages: PackageInfo[]): Promise<EntryPoint[]> {
  const entryPoints: EntryPoint[] = [];

  // Check bin directory
  const binPath = path.join(rootPath, 'bin');
  try {
    const binFiles = await fs.readdir(binPath);
    for (const file of binFiles) {
      entryPoints.push({
        type: 'cli',
        path: `bin/${file}`,
        description: 'CLI entry point',
      });
    }
  } catch {
    // No bin directory
  }

  // Check package main/exports
  for (const pkg of packages) {
    if (pkg.main) {
      entryPoints.push({
        type: 'library',
        path: path.join(pkg.path, pkg.main),
        description: `Main entry for ${pkg.name}`,
      });
    }
  }

  // Check common patterns
  const commonPatterns = [
    { pattern: 'src/index.ts', type: 'library' as const },
    { pattern: 'src/main.ts', type: 'library' as const },
    { pattern: 'src/server.ts', type: 'api' as const },
    { pattern: 'src/app.ts', type: 'api' as const },
    { pattern: 'src/worker.ts', type: 'worker' as const },
    { pattern: 'pages/api', type: 'api' as const },
    { pattern: 'app/api', type: 'api' as const },
  ];

  for (const { pattern, type } of commonPatterns) {
    const fullPath = path.join(rootPath, pattern);
    try {
      await fs.access(fullPath);
      // Avoid duplicates
      if (!entryPoints.some(e => e.path === pattern)) {
        entryPoints.push({ type, path: pattern });
      }
    } catch {
      // File doesn't exist
    }
  }

  return entryPoints;
}

async function detectFrameworks(rootPath: string): Promise<FrameworkInfo[]> {
  const frameworks: FrameworkInfo[] = [];
  const packageJsonPath = path.join(rootPath, 'package.json');

  try {
    const packageJson = JSON.parse(await fs.readFile(packageJsonPath, 'utf-8'));
    const allDeps = {
      ...packageJson.dependencies,
      ...packageJson.devDependencies,
    };

    const frameworkPatterns: Array<{
      dep: string;
      name: string;
      type: FrameworkInfo['type'];
      indicators: string[];
    }> = [
      { dep: 'next', name: 'Next.js', type: 'fullstack', indicators: ['next.config.js', 'next.config.mjs'] },
      { dep: 'react', name: 'React', type: 'frontend', indicators: ['src/App.tsx', 'src/App.jsx'] },
      { dep: 'vue', name: 'Vue.js', type: 'frontend', indicators: ['vue.config.js'] },
      { dep: 'express', name: 'Express', type: 'backend', indicators: ['src/app.ts', 'src/server.ts'] },
      { dep: 'fastify', name: 'Fastify', type: 'backend', indicators: ['src/server.ts'] },
      { dep: 'vitest', name: 'Vitest', type: 'test', indicators: ['vitest.config.ts'] },
      { dep: 'jest', name: 'Jest', type: 'test', indicators: ['jest.config.js'] },
      { dep: 'playwright', name: 'Playwright', type: 'test', indicators: ['playwright.config.ts'] },
      { dep: 'vite', name: 'Vite', type: 'build', indicators: ['vite.config.ts'] },
      { dep: 'webpack', name: 'Webpack', type: 'build', indicators: ['webpack.config.js'] },
    ];

    for (const { dep, name, type, indicators } of frameworkPatterns) {
      if (allDeps[dep]) {
        frameworks.push({
          name,
          version: allDeps[dep],
          type,
          indicators,
        });
      }
    }
  } catch {
    // No package.json
  }

  return frameworks;
}

function extractExports(content: string, filePath: string): ModuleExport[] {
  const exports: ModuleExport[] = [];
  const lines = content.split('\n');

  const exportPatterns = [
    { regex: /export\s+default\s+/, type: 'default' as const },
    { regex: /export\s+function\s+(\w+)/, type: 'function' as const },
    { regex: /export\s+class\s+(\w+)/, type: 'class' as const },
    { regex: /export\s+interface\s+(\w+)/, type: 'interface' as const },
    { regex: /export\s+type\s+(\w+)/, type: 'type' as const },
    { regex: /export\s+const\s+(\w+)/, type: 'const' as const },
    { regex: /export\s+enum\s+(\w+)/, type: 'enum' as const },
    { regex: /export\s+\{\s*([^}]+)\s*\}/, type: 'const' as const },
  ];

  lines.forEach((line, index) => {
    for (const { regex, type } of exportPatterns) {
      const match = line.match(regex);
      if (match) {
        if (type === 'default') {
          exports.push({
            name: 'default',
            type: 'default',
            isReExport: line.includes('from'),
            sourceFile: filePath,
            line: index + 1,
          });
        } else if (match[1]) {
          // Handle multiple exports in braces
          const names = match[1].split(',').map(n => n.trim().split(' ')[0]);
          for (const name of names) {
            if (name) {
              exports.push({
                name,
                type,
                isReExport: line.includes('from'),
                sourceFile: filePath,
                line: index + 1,
              });
            }
          }
        }
      }
    }
  });

  return exports;
}

function extractImports(content: string): ModuleImport[] {
  const imports: ModuleImport[] = [];
  const importRegex = /import\s+(?:type\s+)?(?:\{([^}]+)\}|(\w+))\s+from\s+['"]([^'"]+)['"]/g;
  
  let match;
  while ((match = importRegex.exec(content)) !== null) {
    const items = match[1] 
      ? match[1].split(',').map(i => i.trim().split(' ')[0]).filter(Boolean)
      : match[2] ? [match[2]] : [];
    const source = match[3];
    
    imports.push({
      source,
      isExternal: !source.startsWith('.') && !source.startsWith('/'),
      items,
      isTypeOnly: match[0].includes('import type'),
    });
  }

  return imports;
}

function countEntities(content: string): Record<string, number> {
  const counts: Record<string, number> = {};
  
  const patterns: Array<{ name: string; regex: RegExp }> = [
    { name: 'function', regex: /function\s+\w+/g },
    { name: 'class', regex: /class\s+\w+/g },
    { name: 'interface', regex: /interface\s+\w+/g },
    { name: 'type', regex: /type\s+\w+\s*=/g },
    { name: 'const', regex: /const\s+\w+/g },
    { name: 'let', regex: /let\s+\w+/g },
  ];

  for (const { name, regex } of patterns) {
    const matches = content.match(regex);
    if (matches) {
      counts[name] = matches.length;
    }
  }

  return counts;
}

function calculateComplexity(content: string): number {
  let complexity = 1; // Base complexity
  
  // Count control flow statements
  const controlPatterns = [
    /\bif\s*\(/g,
    /\belse\s+if\s*\(/g,
    /\bwhile\s*\(/g,
    /\bfor\s*\(/g,
    /\bswitch\s*\(/g,
    /\bcase\s+/g,
    /\bcatch\s*\(/g,
    /\?\s*[^:]+\s*:/g, // Ternary
    /&&/g,
    /\|\|/g,
  ];

  for (const pattern of controlPatterns) {
    const matches = content.match(pattern);
    if (matches) {
      complexity += matches.length;
    }
  }

  return complexity;
}

async function generateDocuments(
  _rootPath: string,
  packages: PackageInfo[],
  entryPoints: EntryPoint[],
  frameworks: FrameworkInfo[],
  _structure: DirectoryNode
): Promise<CodemapDocument[]> {
  const documents: CodemapDocument[] = [];
  const timestamp = new Date().toISOString();

  // INDEX.md
  let indexContent = '# Code Map\n\n';
  indexContent += `**Generated**: ${timestamp}\n\n`;
  indexContent += '## Packages\n\n';
  indexContent += '| Package | Version | Dependencies |\n';
  indexContent += '|---------|---------|-------------|\n';
  for (const pkg of packages) {
    indexContent += `| ${pkg.name} | ${pkg.version || '-'} | ${pkg.dependencies.length} |\n`;
  }
  indexContent += '\n## Entry Points\n\n';
  for (const ep of entryPoints) {
    indexContent += `- **${ep.type}**: \`${ep.path}\`\n`;
  }
  if (frameworks.length > 0) {
    indexContent += '\n## Frameworks\n\n';
    for (const fw of frameworks) {
      indexContent += `- ${fw.name} (${fw.type})\n`;
    }
  }

  documents.push({
    type: 'index',
    title: 'Code Map Index',
    content: indexContent,
    updatedAt: timestamp,
  });

  // packages.md
  let packagesContent = '# Packages\n\n';
  for (const pkg of packages) {
    packagesContent += `## ${pkg.name}\n\n`;
    packagesContent += `**Path**: \`${pkg.path}\`\n\n`;
    if (pkg.description) packagesContent += `${pkg.description}\n\n`;
    if (pkg.dependencies.length > 0) {
      packagesContent += '### Dependencies\n\n';
      for (const dep of pkg.dependencies.slice(0, 20)) {
        packagesContent += `- ${dep}\n`;
      }
      if (pkg.dependencies.length > 20) {
        packagesContent += `- ... and ${pkg.dependencies.length - 20} more\n`;
      }
      packagesContent += '\n';
    }
  }

  documents.push({
    type: 'packages',
    title: 'Package Details',
    content: packagesContent,
    packages: packages.map(p => p.name),
    updatedAt: timestamp,
  });

  return documents;
}

function hashCodemap(codemap: Codemap): string {
  const data = JSON.stringify({
    packages: codemap.packages.map(p => ({ name: p.name, deps: p.dependencies })),
    entryPoints: codemap.entryPoints.map(e => e.path),
  });
  return createHash('sha256').update(data).digest('hex');
}

/**
 * Format codemap structure as Mermaid diagram
 */
export function formatCodemapAsMermaid(codemap: Codemap): string {
  const lines: string[] = ['graph TD'];

  // Add packages
  for (const pkg of codemap.packages) {
    const safeId = pkg.name.replace(/[@/\-]/g, '_');
    lines.push(`    ${safeId}["${pkg.name}"]`);
  }

  // Add dependencies
  for (const pkg of codemap.packages) {
    const sourceId = pkg.name.replace(/[@/\-]/g, '_');
    for (const dep of pkg.dependencies) {
      // Only include internal dependencies
      const depPkg = codemap.packages.find(p => p.name === dep);
      if (depPkg) {
        const targetId = dep.replace(/[@/\-]/g, '_');
        lines.push(`    ${sourceId} --> ${targetId}`);
      }
    }
  }

  return lines.join('\n');
}
