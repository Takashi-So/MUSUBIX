/**
 * @fileoverview Package JSON Parser for dependency extraction
 * @module @nahisaho/musubix-security/cve/dependency-parser
 *
 * Parses package.json and package-lock.json to extract dependency
 * information for vulnerability scanning.
 *
 * @requirement REQ-CVE-002 - Dependency extraction from package files
 * @design DES-EPIC2-005 - Dependency Parser component
 */

import * as fs from 'node:fs';
import * as path from 'node:path';

/**
 * Dependency types in package.json
 */
export type DependencyType =
  | 'dependencies'
  | 'devDependencies'
  | 'peerDependencies'
  | 'optionalDependencies';

/**
 * Parsed dependency information
 */
export interface ParsedDependency {
  /** Package name */
  name: string;
  /** Version specifier from package.json (may be a range) */
  versionSpecifier: string;
  /** Resolved exact version (from lock file if available) */
  resolvedVersion?: string;
  /** Type of dependency */
  type: DependencyType;
  /** Whether this is a direct or transitive dependency */
  isDirect: boolean;
  /** Dependencies of this package */
  dependencies?: string[];
  /** Integrity hash (from lock file) */
  integrity?: string;
  /** Package URL for download */
  resolved?: string;
}

/**
 * Package.json structure (partial)
 */
export interface PackageJson {
  name?: string;
  version?: string;
  dependencies?: Record<string, string>;
  devDependencies?: Record<string, string>;
  peerDependencies?: Record<string, string>;
  optionalDependencies?: Record<string, string>;
}

/**
 * Package-lock.json structure (v2/v3)
 */
export interface PackageLockJson {
  name?: string;
  version?: string;
  lockfileVersion?: number;
  packages?: Record<string, PackageLockEntry>;
  dependencies?: Record<string, LegacyLockEntry>;
}

/**
 * Package-lock.json packages entry (v2/v3)
 */
export interface PackageLockEntry {
  version?: string;
  resolved?: string;
  integrity?: string;
  dev?: boolean;
  optional?: boolean;
  peer?: boolean;
  dependencies?: Record<string, string>;
  devDependencies?: Record<string, string>;
  peerDependencies?: Record<string, string>;
  optionalDependencies?: Record<string, string>;
}

/**
 * Legacy package-lock.json dependencies entry (v1)
 */
export interface LegacyLockEntry {
  version: string;
  resolved?: string;
  integrity?: string;
  dev?: boolean;
  optional?: boolean;
  requires?: Record<string, string>;
  dependencies?: Record<string, LegacyLockEntry>;
}

/**
 * Parser options
 */
export interface DependencyParserOptions {
  /** Include dev dependencies (default: true) */
  includeDevDependencies?: boolean;
  /** Include peer dependencies (default: false) */
  includePeerDependencies?: boolean;
  /** Include optional dependencies (default: true) */
  includeOptionalDependencies?: boolean;
  /** Maximum depth for transitive dependencies (default: unlimited) */
  maxDepth?: number;
}

/**
 * Parse result
 */
export interface ParseResult {
  /** Project name */
  projectName?: string;
  /** Project version */
  projectVersion?: string;
  /** All parsed dependencies */
  dependencies: ParsedDependency[];
  /** Direct dependencies count */
  directCount: number;
  /** Transitive dependencies count */
  transitiveCount: number;
  /** Parsing warnings */
  warnings: string[];
}

/**
 * Dependency Parser for npm projects
 *
 * @example
 * ```typescript
 * const parser = new DependencyParser();
 *
 * // Parse from directory
 * const result = await parser.parseDirectory('./my-project');
 *
 * // Parse from package.json content
 * const deps = parser.parsePackageJson(packageJsonContent);
 *
 * // Get all dependencies as flat list
 * console.log(result.dependencies);
 * ```
 */
export class DependencyParser {
  private readonly options: Required<DependencyParserOptions>;

  constructor(options: DependencyParserOptions = {}) {
    this.options = {
      includeDevDependencies: options.includeDevDependencies ?? true,
      includePeerDependencies: options.includePeerDependencies ?? false,
      includeOptionalDependencies: options.includeOptionalDependencies ?? true,
      maxDepth: options.maxDepth ?? Infinity,
    };
  }

  /**
   * Parse dependencies from a project directory
   * @param dirPath - Path to project directory
   * @returns Parsed dependencies
   */
  async parseDirectory(dirPath: string): Promise<ParseResult> {
    const warnings: string[] = [];
    
    // Read package.json
    const packageJsonPath = path.join(dirPath, 'package.json');
    if (!fs.existsSync(packageJsonPath)) {
      throw new Error(`package.json not found at ${packageJsonPath}`);
    }

    const packageJsonContent = await fs.promises.readFile(packageJsonPath, 'utf-8');
    const packageJson: PackageJson = JSON.parse(packageJsonContent);

    // Try to read package-lock.json
    let packageLock: PackageLockJson | null = null;
    const packageLockPath = path.join(dirPath, 'package-lock.json');
    
    if (fs.existsSync(packageLockPath)) {
      try {
        const lockContent = await fs.promises.readFile(packageLockPath, 'utf-8');
        packageLock = JSON.parse(lockContent);
      } catch (error) {
        warnings.push(`Failed to parse package-lock.json: ${error}`);
      }
    } else {
      warnings.push('package-lock.json not found, using version specifiers only');
    }

    return this.parsePackageJsonWithLock(packageJson, packageLock, warnings);
  }

  /**
   * Parse package.json content directly
   * @param content - package.json content as string
   * @returns Direct dependencies (no transitive without lock file)
   */
  parsePackageJson(content: string): ParsedDependency[] {
    const packageJson: PackageJson = JSON.parse(content);
    const dependencies: ParsedDependency[] = [];

    this.extractDependencies(
      packageJson.dependencies,
      'dependencies',
      true,
      dependencies
    );

    if (this.options.includeDevDependencies) {
      this.extractDependencies(
        packageJson.devDependencies,
        'devDependencies',
        true,
        dependencies
      );
    }

    if (this.options.includePeerDependencies) {
      this.extractDependencies(
        packageJson.peerDependencies,
        'peerDependencies',
        true,
        dependencies
      );
    }

    if (this.options.includeOptionalDependencies) {
      this.extractDependencies(
        packageJson.optionalDependencies,
        'optionalDependencies',
        true,
        dependencies
      );
    }

    return dependencies;
  }

  /**
   * Parse package-lock.json content directly
   * @param content - package-lock.json content as string
   * @returns All dependencies including transitive
   */
  parsePackageLock(content: string): ParsedDependency[] {
    const lockFile: PackageLockJson = JSON.parse(content);
    return this.extractFromLockFile(lockFile);
  }

  /**
   * Parse with both package.json and lock file
   */
  private parsePackageJsonWithLock(
    packageJson: PackageJson,
    packageLock: PackageLockJson | null,
    warnings: string[]
  ): ParseResult {
    const dependencies: ParsedDependency[] = [];
    const directNames = new Set<string>();

    // Extract direct dependencies from package.json
    const directDeps = this.parsePackageJson(JSON.stringify(packageJson));
    for (const dep of directDeps) {
      directNames.add(dep.name);
    }

    if (packageLock) {
      // Use lock file for all dependencies
      const allDeps = this.extractFromLockFile(packageLock);
      
      // Mark direct dependencies
      for (const dep of allDeps) {
        dep.isDirect = directNames.has(dep.name);
        
        // Find matching direct dep to get the type
        if (dep.isDirect) {
          const direct = directDeps.find(d => d.name === dep.name);
          if (direct) {
            dep.type = direct.type;
            dep.versionSpecifier = direct.versionSpecifier;
          }
        }
        
        dependencies.push(dep);
      }
    } else {
      // Without lock file, we only have direct dependencies
      dependencies.push(...directDeps);
    }

    const directCount = dependencies.filter(d => d.isDirect).length;
    const transitiveCount = dependencies.length - directCount;

    return {
      projectName: packageJson.name,
      projectVersion: packageJson.version,
      dependencies,
      directCount,
      transitiveCount,
      warnings,
    };
  }

  /**
   * Extract dependencies from lock file
   */
  private extractFromLockFile(lockFile: PackageLockJson): ParsedDependency[] {
    const dependencies: ParsedDependency[] = [];
    const seen = new Set<string>();

    // Handle v2/v3 format (packages)
    if (lockFile.packages) {
      for (const [key, entry] of Object.entries(lockFile.packages)) {
        // Skip root package
        if (key === '') continue;

        // Extract package name from path (node_modules/pkg or node_modules/@scope/pkg)
        const name = this.extractPackageNameFromPath(key);
        if (!name || seen.has(name)) continue;

        const type = this.determineDependencyType(entry);
        if (!this.shouldIncludeType(type)) continue;

        seen.add(name);
        dependencies.push({
          name,
          versionSpecifier: entry.version ?? '*',
          resolvedVersion: entry.version,
          type,
          isDirect: false, // Will be updated later
          integrity: entry.integrity,
          resolved: entry.resolved,
          dependencies: entry.dependencies ? Object.keys(entry.dependencies) : undefined,
        });
      }
    }

    // Handle v1 format (dependencies)
    if (lockFile.dependencies && dependencies.length === 0) {
      this.extractFromLegacyLock(lockFile.dependencies, dependencies, seen, 0);
    }

    return dependencies;
  }

  /**
   * Extract from v1 lock format (recursive)
   */
  private extractFromLegacyLock(
    deps: Record<string, LegacyLockEntry>,
    result: ParsedDependency[],
    seen: Set<string>,
    depth: number
  ): void {
    if (depth > this.options.maxDepth) return;

    for (const [name, entry] of Object.entries(deps)) {
      if (seen.has(name)) continue;

      const type: DependencyType = entry.dev
        ? 'devDependencies'
        : entry.optional
        ? 'optionalDependencies'
        : 'dependencies';

      if (!this.shouldIncludeType(type)) continue;

      seen.add(name);
      result.push({
        name,
        versionSpecifier: entry.version,
        resolvedVersion: entry.version,
        type,
        isDirect: depth === 0,
        integrity: entry.integrity,
        resolved: entry.resolved,
        dependencies: entry.requires ? Object.keys(entry.requires) : undefined,
      });

      // Recurse into nested dependencies
      if (entry.dependencies) {
        this.extractFromLegacyLock(entry.dependencies, result, seen, depth + 1);
      }
    }
  }

  /**
   * Extract dependencies from package.json section
   */
  private extractDependencies(
    deps: Record<string, string> | undefined,
    type: DependencyType,
    isDirect: boolean,
    result: ParsedDependency[]
  ): void {
    if (!deps) return;

    for (const [name, version] of Object.entries(deps)) {
      result.push({
        name,
        versionSpecifier: version,
        type,
        isDirect,
      });
    }
  }

  /**
   * Determine dependency type from lock entry
   */
  private determineDependencyType(entry: PackageLockEntry): DependencyType {
    if (entry.dev) return 'devDependencies';
    if (entry.optional) return 'optionalDependencies';
    if (entry.peer) return 'peerDependencies';
    return 'dependencies';
  }

  /**
   * Check if dependency type should be included
   */
  private shouldIncludeType(type: DependencyType): boolean {
    switch (type) {
      case 'dependencies':
        return true;
      case 'devDependencies':
        return this.options.includeDevDependencies;
      case 'peerDependencies':
        return this.options.includePeerDependencies;
      case 'optionalDependencies':
        return this.options.includeOptionalDependencies;
      default:
        return true;
    }
  }

  /**
   * Extract package name from node_modules path
   */
  private extractPackageNameFromPath(modulePath: string): string | null {
    // Handle paths like:
    // node_modules/lodash
    // node_modules/@scope/package
    // node_modules/a/node_modules/b
    const match = modulePath.match(/node_modules\/(@[^/]+\/[^/]+|[^/]+)$/);
    return match ? match[1] : null;
  }
}

/**
 * Resolve version specifier to concrete version
 * Handles npm version ranges
 */
export function resolveVersionSpecifier(specifier: string): {
  type: 'exact' | 'range' | 'tag' | 'url' | 'git';
  version?: string;
  minVersion?: string;
  maxVersion?: string;
} {
  // Exact version
  if (/^\d+\.\d+\.\d+/.test(specifier)) {
    return { type: 'exact', version: specifier };
  }

  // URL or git
  if (specifier.startsWith('http') || specifier.startsWith('git') || specifier.includes('github:')) {
    if (specifier.startsWith('git') || specifier.includes('github:')) {
      return { type: 'git' };
    }
    return { type: 'url' };
  }

  // Tag (latest, next, etc.)
  if (/^[a-z]+$/i.test(specifier)) {
    return { type: 'tag' };
  }

  // Range patterns
  const rangeMatch = specifier.match(
    /^(?:>=?|<=?|~|\^)?(\d+(?:\.\d+(?:\.\d+)?)?)/
  );
  if (rangeMatch) {
    return {
      type: 'range',
      minVersion: rangeMatch[1],
    };
  }

  return { type: 'range' };
}

/**
 * Filter dependencies for security scanning
 * Removes dev dependencies if not needed, etc.
 */
export function filterDependenciesForScanning(
  dependencies: ParsedDependency[],
  options: {
    includeDevDependencies?: boolean;
    includeTransitive?: boolean;
    directOnly?: boolean;
  } = {}
): ParsedDependency[] {
  // Set defaults - by default include everything
  const includeDevDeps = options.includeDevDependencies ?? true;
  const includeTransitive = options.includeTransitive ?? true;
  const directOnly = options.directOnly ?? false;

  return dependencies.filter((dep) => {
    // directOnly takes precedence
    if (directOnly && !dep.isDirect) {
      return false;
    }

    // If not including transitive and this is transitive
    if (!includeTransitive && !dep.isDirect) {
      return false;
    }

    // If not including dev deps and this is a dev dep
    if (!includeDevDeps && dep.type === 'devDependencies') {
      return false;
    }

    return true;
  });
}

/**
 * Get unique packages (deduplicate by name)
 */
export function getUniquePackages(
  dependencies: ParsedDependency[]
): ParsedDependency[] {
  const seen = new Map<string, ParsedDependency>();

  for (const dep of dependencies) {
    const existing = seen.get(dep.name);
    if (!existing || dep.isDirect) {
      seen.set(dep.name, dep);
    }
  }

  return Array.from(seen.values());
}
