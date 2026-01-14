/**
 * MUSUBIX Version
 * 
 * Dynamically reads version from package.json
 * 
 * @packageDocumentation
 * @module @musubix/core/version
 * 
 * @see REQ-BUGFIX-005-01〜05 - Version management improvements
 */

import { fileURLToPath } from 'url';
import { dirname, join } from 'path';
import { readFileSync, existsSync } from 'fs';

/**
 * Dependency versions for verbose output
 * @see REQ-BUGFIX-005-01
 */
export interface DependencyVersions {
  core: string;
  mcpServer: string;
  knowledge: string;
  policy: string;
  decisions: string;
}

/**
 * Version mismatch detection result
 * @see REQ-BUGFIX-005-02
 */
export interface VersionMismatchResult {
  hasMismatch: boolean;
  expected?: string;
  actual?: string;
  guidance?: string;
}

/**
 * Get version from package.json
 * Tries multiple locations to handle different installation scenarios
 */
function getVersion(): string {
  // Try to find package.json in various locations
  const possiblePaths = [
    // When running from source (development)
    join(dirname(fileURLToPath(import.meta.url)), '..', 'package.json'),
    join(dirname(fileURLToPath(import.meta.url)), '..', '..', 'package.json'),
    // When running from dist (production)
    join(dirname(fileURLToPath(import.meta.url)), '..', '..', 'package.json'),
    join(dirname(fileURLToPath(import.meta.url)), '..', '..', '..', 'package.json'),
  ];

  for (const pkgPath of possiblePaths) {
    try {
      if (existsSync(pkgPath)) {
        const pkg = JSON.parse(readFileSync(pkgPath, 'utf-8'));
        if (pkg.name === '@nahisaho/musubix-core' || pkg.name === 'musubix') {
          return pkg.version;
        }
      }
    } catch {
      // Continue to next path
    }
  }

  // Fallback version (should not happen in normal operation)
  return '1.1.8';
}

export const VERSION = getVersion();

/**
 * Try to get version of a package
 * @see REQ-BUGFIX-005-01
 */
function tryGetVersion(pkgName: string): string {
  try {
    // Try to resolve package.json relative to project root
    const possiblePaths = [
      join(process.cwd(), 'node_modules', pkgName, 'package.json'),
      join(dirname(fileURLToPath(import.meta.url)), '..', '..', '..', pkgName.replace('@', '').replace('/', '-'), 'package.json'),
    ];
    
    for (const pkgPath of possiblePaths) {
      if (existsSync(pkgPath)) {
        const pkg = JSON.parse(readFileSync(pkgPath, 'utf-8'));
        return pkg.version;
      }
    }
    return 'not installed';
  } catch {
    return 'not installed';
  }
}

/**
 * Collect versions of all MUSUBIX dependencies
 * @see REQ-BUGFIX-005-01
 */
export function collectDependencyVersions(): DependencyVersions {
  return {
    core: VERSION,
    mcpServer: tryGetVersion('@nahisaho/musubix-mcp-server'),
    knowledge: tryGetVersion('@musubix/knowledge'),
    policy: tryGetVersion('@musubix/policy'),
    decisions: tryGetVersion('@musubix/decisions'),
  };
}

/**
 * Check for version mismatch between installed and expected
 * @see REQ-BUGFIX-005-02
 */
export function checkVersionMismatch(): VersionMismatchResult {
  try {
    // Check project's package.json for expected version
    const projectPkgPath = join(process.cwd(), 'package.json');
    if (!existsSync(projectPkgPath)) {
      return { hasMismatch: false };
    }
    
    const projectPkg = JSON.parse(readFileSync(projectPkgPath, 'utf-8'));
    const deps = {
      ...projectPkg.dependencies,
      ...projectPkg.devDependencies,
    };
    
    // Check musubix or @nahisaho/musubix-core
    const expectedVersion = deps['musubix'] || deps['@nahisaho/musubix-core'];
    if (!expectedVersion) {
      return { hasMismatch: false };
    }
    
    // Remove version prefix (^, ~, etc.)
    const cleanExpected = expectedVersion.replace(/^[\^~>=<]+/, '');
    
    // Compare with actual version
    if (cleanExpected !== VERSION && !cleanExpected.includes('*')) {
      return {
        hasMismatch: true,
        expected: cleanExpected,
        actual: VERSION,
        guidance: 'Run: npx --yes musubix@latest',
      };
    }
    
    return { hasMismatch: false };
  } catch {
    return { hasMismatch: false };
  }
}

/**
 * Format verbose version output
 * @see REQ-BUGFIX-005-03
 */
export function formatVerboseVersion(): string {
  const deps = collectDependencyVersions();
  const mismatch = checkVersionMismatch();
  
  const lines = [
    `musubix v${VERSION}`,
    '',
    'Dependencies:',
    `  @nahisaho/musubix-core: ${deps.core}`,
    `  @nahisaho/musubix-mcp-server: ${deps.mcpServer}`,
    `  @musubix/knowledge: ${deps.knowledge}`,
    `  @musubix/policy: ${deps.policy}`,
    `  @musubix/decisions: ${deps.decisions}`,
  ];
  
  if (mismatch.hasMismatch) {
    lines.push('');
    lines.push(`⚠️  Version mismatch: config expects ${mismatch.expected}, but ${mismatch.actual} is installed`);
    lines.push(`   ${mismatch.guidance}`);
  }
  
  return lines.join('\n');
}
