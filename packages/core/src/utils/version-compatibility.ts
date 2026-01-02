/**
 * Version Compatibility Checker
 * 
 * Checks and manages version compatibility
 * 
 * @packageDocumentation
 * @module utils/version-compatibility
 * 
 * @see REQ-ERR-003 - Version Compatibility
 * @see Article IX - Continuous Adaptation
 */

/**
 * Version info
 */
export interface VersionInfo {
  /** Major version */
  major: number;
  /** Minor version */
  minor: number;
  /** Patch version */
  patch: number;
  /** Prerelease tag */
  prerelease?: string;
  /** Build metadata */
  build?: string;
  /** Raw version string */
  raw: string;
}

/**
 * Compatibility level
 */
export type CompatibilityLevel = 'compatible' | 'minor-incompatible' | 'major-incompatible' | 'unknown';

/**
 * Compatibility result
 */
export interface CompatibilityResult {
  /** Current version */
  current: VersionInfo;
  /** Required version */
  required: VersionInfo;
  /** Compatibility level */
  level: CompatibilityLevel;
  /** Is compatible */
  compatible: boolean;
  /** Message */
  message: string;
  /** Breaking changes */
  breakingChanges?: string[];
  /** Migration steps */
  migrationSteps?: string[];
}

/**
 * Dependency info
 */
export interface DependencyInfo {
  /** Package name */
  name: string;
  /** Current version */
  currentVersion: string;
  /** Required version range */
  requiredVersion: string;
  /** Latest version */
  latestVersion?: string;
  /** Is satisfied */
  satisfied: boolean;
  /** Is outdated */
  outdated: boolean;
}

/**
 * Compatibility report
 */
export interface CompatibilityReport {
  /** Timestamp */
  timestamp: Date;
  /** System version */
  systemVersion: VersionInfo;
  /** Dependencies checked */
  dependencies: DependencyInfo[];
  /** Overall compatible */
  compatible: boolean;
  /** Warnings */
  warnings: string[];
  /** Errors */
  errors: string[];
  /** Recommendations */
  recommendations: string[];
}

/**
 * Version constraint
 */
export interface VersionConstraint {
  /** Operator */
  operator: '>=' | '>' | '<=' | '<' | '=' | '^' | '~';
  /** Version */
  version: VersionInfo;
}

/**
 * Migration guide
 */
export interface MigrationGuide {
  /** From version */
  fromVersion: string;
  /** To version */
  toVersion: string;
  /** Steps */
  steps: Array<{
    description: string;
    action: string;
    automated: boolean;
  }>;
  /** Breaking changes */
  breakingChanges: string[];
  /** Deprecations */
  deprecations: string[];
  /** New features */
  newFeatures: string[];
}

/**
 * Compatibility config
 */
export interface VersionCompatibilityConfig {
  /** Strict mode */
  strictMode: boolean;
  /** Allow prerelease */
  allowPrerelease: boolean;
  /** Check dependencies */
  checkDependencies: boolean;
  /** Auto-migrate */
  autoMigrate: boolean;
}

/**
 * Default configuration
 */
export const DEFAULT_COMPATIBILITY_CONFIG: VersionCompatibilityConfig = {
  strictMode: false,
  allowPrerelease: false,
  checkDependencies: true,
  autoMigrate: false,
};

/**
 * Version pattern
 */
const VERSION_PATTERN = /^v?(\d+)\.(\d+)\.(\d+)(?:-([a-zA-Z0-9.-]+))?(?:\+([a-zA-Z0-9.-]+))?$/;

/**
 * Version Compatibility Checker
 */
export class VersionCompatibility {
  private config: VersionCompatibilityConfig;
  private migrationGuides: Map<string, MigrationGuide> = new Map();

  constructor(config?: Partial<VersionCompatibilityConfig>) {
    this.config = { ...DEFAULT_COMPATIBILITY_CONFIG, ...config };
  }

  /**
   * Parse version string
   */
  parseVersion(version: string): VersionInfo | null {
    const match = version.trim().match(VERSION_PATTERN);
    if (!match) {
      return null;
    }

    return {
      major: parseInt(match[1], 10),
      minor: parseInt(match[2], 10),
      patch: parseInt(match[3], 10),
      prerelease: match[4],
      build: match[5],
      raw: version,
    };
  }

  /**
   * Format version to string
   */
  formatVersion(info: VersionInfo): string {
    let version = `${info.major}.${info.minor}.${info.patch}`;
    if (info.prerelease) {
      version += `-${info.prerelease}`;
    }
    if (info.build) {
      version += `+${info.build}`;
    }
    return version;
  }

  /**
   * Compare two versions
   * Returns: -1 if a < b, 0 if a == b, 1 if a > b
   */
  compareVersions(a: VersionInfo | string, b: VersionInfo | string): number {
    const versionA = typeof a === 'string' ? this.parseVersion(a) : a;
    const versionB = typeof b === 'string' ? this.parseVersion(b) : b;

    if (!versionA || !versionB) {
      throw new Error('Invalid version format');
    }

    // Compare major
    if (versionA.major !== versionB.major) {
      return versionA.major > versionB.major ? 1 : -1;
    }

    // Compare minor
    if (versionA.minor !== versionB.minor) {
      return versionA.minor > versionB.minor ? 1 : -1;
    }

    // Compare patch
    if (versionA.patch !== versionB.patch) {
      return versionA.patch > versionB.patch ? 1 : -1;
    }

    // Compare prerelease
    if (versionA.prerelease && versionB.prerelease) {
      return versionA.prerelease.localeCompare(versionB.prerelease);
    }
    if (versionA.prerelease) {
      return -1;  // Prerelease is less than release
    }
    if (versionB.prerelease) {
      return 1;
    }

    return 0;
  }

  /**
   * Check version compatibility
   */
  checkCompatibility(current: string, required: string): CompatibilityResult {
    const currentVersion = this.parseVersion(current);
    const requiredVersion = this.parseVersion(required);

    if (!currentVersion || !requiredVersion) {
      return {
        current: currentVersion ?? { major: 0, minor: 0, patch: 0, raw: current },
        required: requiredVersion ?? { major: 0, minor: 0, patch: 0, raw: required },
        level: 'unknown',
        compatible: false,
        message: 'Unable to parse version',
      };
    }

    // Check prerelease
    if (!this.config.allowPrerelease && currentVersion.prerelease) {
      return {
        current: currentVersion,
        required: requiredVersion,
        level: 'unknown',
        compatible: false,
        message: 'Prerelease versions are not allowed',
      };
    }

    // Major version mismatch
    if (currentVersion.major !== requiredVersion.major) {
      const breaking = this.getBreakingChanges(requiredVersion, currentVersion);
      const migration = this.getMigrationSteps(requiredVersion, currentVersion);

      return {
        current: currentVersion,
        required: requiredVersion,
        level: 'major-incompatible',
        compatible: false,
        message: `Major version mismatch: ${current} vs ${required}`,
        breakingChanges: breaking,
        migrationSteps: migration,
      };
    }

    // Minor version mismatch (current < required)
    if (currentVersion.minor < requiredVersion.minor) {
      if (this.config.strictMode) {
        return {
          current: currentVersion,
          required: requiredVersion,
          level: 'minor-incompatible',
          compatible: false,
          message: `Minor version mismatch (strict mode): ${current} vs ${required}`,
        };
      }

      return {
        current: currentVersion,
        required: requiredVersion,
        level: 'minor-incompatible',
        compatible: true,
        message: `Minor version older than required: ${current} vs ${required}`,
      };
    }

    // Patch version mismatch (current < required)
    if (currentVersion.minor === requiredVersion.minor && 
        currentVersion.patch < requiredVersion.patch) {
      if (this.config.strictMode) {
        return {
          current: currentVersion,
          required: requiredVersion,
          level: 'compatible',
          compatible: false,
          message: `Patch version mismatch (strict mode): ${current} vs ${required}`,
        };
      }
    }

    return {
      current: currentVersion,
      required: requiredVersion,
      level: 'compatible',
      compatible: true,
      message: `Version ${current} is compatible with ${required}`,
    };
  }

  /**
   * Check version range (semver style)
   */
  satisfiesRange(version: string, range: string): boolean {
    const v = this.parseVersion(version);
    if (!v) return false;

    const constraints = this.parseRange(range);
    
    for (const constraint of constraints) {
      if (!this.satisfiesConstraint(v, constraint)) {
        return false;
      }
    }

    return true;
  }

  /**
   * Parse version range
   */
  parseRange(range: string): VersionConstraint[] {
    const constraints: VersionConstraint[] = [];
    
    // Handle ^ (caret) - compatible with version
    if (range.startsWith('^')) {
      const v = this.parseVersion(range.slice(1));
      if (v) {
        constraints.push({ operator: '>=', version: v });
        constraints.push({ 
          operator: '<', 
          version: { ...v, major: v.major + 1, minor: 0, patch: 0, raw: '' } 
        });
      }
      return constraints;
    }

    // Handle ~ (tilde) - approximately equivalent
    if (range.startsWith('~')) {
      const v = this.parseVersion(range.slice(1));
      if (v) {
        constraints.push({ operator: '>=', version: v });
        constraints.push({ 
          operator: '<', 
          version: { ...v, minor: v.minor + 1, patch: 0, raw: '' } 
        });
      }
      return constraints;
    }

    // Handle >= > <= < =
    const parts = range.split(/\s+/);
    for (const part of parts) {
      let operator: VersionConstraint['operator'] = '=';
      let versionStr = part;

      if (part.startsWith('>=')) {
        operator = '>=';
        versionStr = part.slice(2);
      } else if (part.startsWith('<=')) {
        operator = '<=';
        versionStr = part.slice(2);
      } else if (part.startsWith('>')) {
        operator = '>';
        versionStr = part.slice(1);
      } else if (part.startsWith('<')) {
        operator = '<';
        versionStr = part.slice(1);
      } else if (part.startsWith('=')) {
        versionStr = part.slice(1);
      }

      const v = this.parseVersion(versionStr);
      if (v) {
        constraints.push({ operator, version: v });
      }
    }

    return constraints;
  }

  /**
   * Check if version satisfies constraint
   */
  private satisfiesConstraint(version: VersionInfo, constraint: VersionConstraint): boolean {
    const cmp = this.compareVersions(version, constraint.version);

    switch (constraint.operator) {
      case '>=': return cmp >= 0;
      case '>': return cmp > 0;
      case '<=': return cmp <= 0;
      case '<': return cmp < 0;
      case '=': return cmp === 0;
      case '^': // Already expanded in parseRange
      case '~':
        return false;
      default:
        return false;
    }
  }

  /**
   * Check dependency compatibility
   */
  checkDependency(
    name: string,
    currentVersion: string,
    requiredVersion: string,
    latestVersion?: string
  ): DependencyInfo {
    const satisfied = this.satisfiesRange(currentVersion, requiredVersion);
    const outdated = latestVersion ? 
      this.compareVersions(currentVersion, latestVersion) < 0 : false;

    return {
      name,
      currentVersion,
      requiredVersion,
      latestVersion,
      satisfied,
      outdated,
    };
  }

  /**
   * Generate compatibility report
   */
  generateReport(
    systemVersion: string,
    dependencies: Array<{ name: string; current: string; required: string; latest?: string }>
  ): CompatibilityReport {
    const sysVersion = this.parseVersion(systemVersion);
    const depResults: DependencyInfo[] = [];
    const warnings: string[] = [];
    const errors: string[] = [];
    const recommendations: string[] = [];

    // Check each dependency
    for (const dep of dependencies) {
      const result = this.checkDependency(dep.name, dep.current, dep.required, dep.latest);
      depResults.push(result);

      if (!result.satisfied) {
        errors.push(`${dep.name}: ${dep.current} does not satisfy ${dep.required}`);
      } else if (result.outdated) {
        warnings.push(`${dep.name}: ${dep.current} is outdated (latest: ${dep.latest})`);
        recommendations.push(`Update ${dep.name} to ${dep.latest}`);
      }
    }

    const compatible = errors.length === 0;

    if (!compatible) {
      recommendations.push('Run dependency update to resolve incompatibilities');
    }

    return {
      timestamp: new Date(),
      systemVersion: sysVersion ?? { major: 0, minor: 0, patch: 0, raw: systemVersion },
      dependencies: depResults,
      compatible,
      warnings,
      errors,
      recommendations,
    };
  }

  /**
   * Register migration guide
   */
  registerMigration(guide: MigrationGuide): void {
    const key = `${guide.fromVersion}->${guide.toVersion}`;
    this.migrationGuides.set(key, guide);
  }

  /**
   * Get migration guide
   */
  getMigrationGuide(from: string, to: string): MigrationGuide | null {
    const key = `${from}->${to}`;
    return this.migrationGuides.get(key) ?? null;
  }

  /**
   * Get breaking changes between versions
   */
  private getBreakingChanges(from: VersionInfo, to: VersionInfo): string[] {
    const key = `${this.formatVersion(from)}->${this.formatVersion(to)}`;
    const guide = this.migrationGuides.get(key);
    return guide?.breakingChanges ?? [];
  }

  /**
   * Get migration steps between versions
   */
  private getMigrationSteps(from: VersionInfo, to: VersionInfo): string[] {
    const key = `${this.formatVersion(from)}->${this.formatVersion(to)}`;
    const guide = this.migrationGuides.get(key);
    return guide?.steps.map((s) => s.description) ?? [];
  }

  /**
   * Get next version
   */
  getNextVersion(current: string, bump: 'major' | 'minor' | 'patch'): string {
    const v = this.parseVersion(current);
    if (!v) {
      throw new Error(`Invalid version: ${current}`);
    }

    switch (bump) {
      case 'major':
        return `${v.major + 1}.0.0`;
      case 'minor':
        return `${v.major}.${v.minor + 1}.0`;
      case 'patch':
        return `${v.major}.${v.minor}.${v.patch + 1}`;
    }
  }

  /**
   * Determine version bump type
   */
  determineBumpType(from: string, to: string): 'major' | 'minor' | 'patch' | null {
    const vFrom = this.parseVersion(from);
    const vTo = this.parseVersion(to);

    if (!vFrom || !vTo) return null;

    if (vTo.major > vFrom.major) return 'major';
    if (vTo.minor > vFrom.minor) return 'minor';
    if (vTo.patch > vFrom.patch) return 'patch';

    return null;
  }

  /**
   * Format report as string
   */
  formatReport(report: CompatibilityReport): string {
    const lines: string[] = [];

    lines.push('# Version Compatibility Report');
    lines.push('');
    lines.push(`**Generated:** ${report.timestamp.toISOString()}`);
    lines.push(`**System Version:** ${this.formatVersion(report.systemVersion)}`);
    lines.push(`**Overall Status:** ${report.compatible ? '✅ Compatible' : '❌ Incompatible'}`);
    lines.push('');

    // Dependencies
    lines.push('## Dependencies');
    lines.push('');
    lines.push('| Package | Current | Required | Status |');
    lines.push('|---------|---------|----------|--------|');

    for (const dep of report.dependencies) {
      const status = dep.satisfied
        ? (dep.outdated ? '⚠️ Outdated' : '✅ OK')
        : '❌ Incompatible';
      lines.push(`| ${dep.name} | ${dep.currentVersion} | ${dep.requiredVersion} | ${status} |`);
    }
    lines.push('');

    // Errors
    if (report.errors.length > 0) {
      lines.push('## Errors');
      lines.push('');
      for (const error of report.errors) {
        lines.push(`- ❌ ${error}`);
      }
      lines.push('');
    }

    // Warnings
    if (report.warnings.length > 0) {
      lines.push('## Warnings');
      lines.push('');
      for (const warning of report.warnings) {
        lines.push(`- ⚠️ ${warning}`);
      }
      lines.push('');
    }

    // Recommendations
    if (report.recommendations.length > 0) {
      lines.push('## Recommendations');
      lines.push('');
      for (const rec of report.recommendations) {
        lines.push(`- 💡 ${rec}`);
      }
      lines.push('');
    }

    return lines.join('\n');
  }
}

/**
 * Create version compatibility checker instance
 */
export function createVersionCompatibility(
  config?: Partial<VersionCompatibilityConfig>
): VersionCompatibility {
  return new VersionCompatibility(config);
}
