/**
 * @fileoverview Dependency auditor - check for vulnerable dependencies
 * @module @nahisaho/musubix-security/analysis/dependency-auditor
 * @trace REQ-SEC-DEP-001, REQ-SEC-DEP-002, REQ-SEC-DEP-003
 */

import { exec } from 'node:child_process';
import { readFile, access, constants } from 'node:fs/promises';
import { join } from 'node:path';
import { promisify } from 'node:util';
import type {
  AuditResult,
  AuditOptions,
  VulnerableDependency,
  DependencyVulnerability,
  UpgradeSuggestion,
  SBOM,
  SBOMEntry,
  SBOMOptions,
  DependencyType,
  Severity,
} from '../types/index.js';

const execAsync = promisify(exec);

/**
 * Detect package manager from project
 */
async function detectPackageManager(
  projectPath: string
): Promise<'npm' | 'yarn' | 'pnpm'> {
  // Check for lock files
  const checks = [
    { file: 'pnpm-lock.yaml', manager: 'pnpm' as const },
    { file: 'yarn.lock', manager: 'yarn' as const },
    { file: 'package-lock.json', manager: 'npm' as const },
  ];

  for (const { file, manager } of checks) {
    try {
      await access(join(projectPath, file), constants.R_OK);
      return manager;
    } catch {
      // File doesn't exist, continue checking
    }
  }

  return 'npm'; // Default to npm
}

/**
 * Convert npm severity to our severity
 */
function convertSeverity(npmSeverity: string): Severity {
  switch (npmSeverity.toLowerCase()) {
    case 'critical':
      return 'critical';
    case 'high':
      return 'high';
    case 'moderate':
    case 'medium':
      return 'medium';
    case 'low':
      return 'low';
    default:
      return 'medium';
  }
}

/**
 * Parse npm audit JSON output
 */
interface NpmAuditOutput {
  vulnerabilities?: Record<string, {
    name: string;
    severity: string;
    isDirect: boolean;
    via: (string | {
      source: number;
      name: string;
      dependency: string;
      title: string;
      url: string;
      severity: string;
      cwe: string[];
      cvss: { score: number; vectorString: string };
      range: string;
    })[];
    effects: string[];
    range: string;
    nodes: string[];
    fixAvailable: boolean | { name: string; version: string; isSemVerMajor: boolean };
  }>;
  metadata?: {
    vulnerabilities: {
      critical: number;
      high: number;
      moderate: number;
      low: number;
      total: number;
    };
    dependencies: {
      prod: number;
      dev: number;
      optional: number;
      peer: number;
      total: number;
    };
  };
}

/**
 * Parse npm audit output to our format
 */
function parseNpmAuditOutput(output: NpmAuditOutput): {
  vulnerabilities: VulnerableDependency[];
  metadata: {
    total: number;
    direct: number;
    transitive: number;
    critical: number;
    high: number;
    moderate: number;
    low: number;
  };
} {
  const vulnerabilities: VulnerableDependency[] = [];
  const metadata = {
    total: output.metadata?.dependencies?.total ?? 0,
    direct: output.metadata?.dependencies?.prod ?? 0,
    transitive: 0,
    critical: output.metadata?.vulnerabilities?.critical ?? 0,
    high: output.metadata?.vulnerabilities?.high ?? 0,
    moderate: output.metadata?.vulnerabilities?.moderate ?? 0,
    low: output.metadata?.vulnerabilities?.low ?? 0,
  };

  if (!output.vulnerabilities) {
    return { vulnerabilities, metadata };
  }

  for (const [name, vuln] of Object.entries(output.vulnerabilities)) {
    const depVulns: DependencyVulnerability[] = [];

    for (const via of vuln.via) {
      if (typeof via === 'object') {
        depVulns.push({
          id: String(via.source),
          cve: undefined, // npm audit doesn't always provide CVE
          cwes: via.cwe || [],
          severity: convertSeverity(via.severity),
          title: via.title,
          description: via.title,
          affectedVersions: via.range,
          source: 'npm-audit',
          url: via.url,
        });
      }
    }

    // Determine dependency type
    let type: DependencyType = 'production';
    // Note: npm audit doesn't directly tell us the type, we'd need to cross-reference with package.json

    // Check fix availability
    let fixAvailable = false;
    let patchedVersion: string | undefined;
    if (typeof vuln.fixAvailable === 'object') {
      fixAvailable = true;
      patchedVersion = vuln.fixAvailable.version;
    } else if (vuln.fixAvailable === true) {
      fixAvailable = true;
    }

    // Update patched version in vulnerabilities
    if (patchedVersion && depVulns.length > 0) {
      depVulns[0].patchedVersion = patchedVersion;
    }

    vulnerabilities.push({
      name,
      installedVersion: vuln.range,
      type,
      isDirect: vuln.isDirect,
      dependencyPath: vuln.effects,
      vulnerabilities: depVulns,
      highestSeverity: convertSeverity(vuln.severity),
      fixAvailable,
    });
  }

  metadata.transitive = metadata.total - metadata.direct;

  return { vulnerabilities, metadata };
}

/**
 * Dependency auditor
 */
export class DependencyAuditor {
  private options: AuditOptions;

  constructor(options: AuditOptions = {}) {
    this.options = options;
  }

  /**
   * Generate upgrade suggestions
   */
  private generateUpgradeSuggestions(
    vulnerabilities: VulnerableDependency[]
  ): UpgradeSuggestion[] {
    const suggestions: UpgradeSuggestion[] = [];

    for (const vuln of vulnerabilities) {
      if (!vuln.fixAvailable) continue;

      const fixedVulns = vuln.vulnerabilities
        .filter((v) => v.patchedVersion)
        .map((v) => v.id);

      if (fixedVulns.length === 0) continue;

      const patchedVersion = vuln.vulnerabilities[0]?.patchedVersion;
      if (!patchedVersion) continue;

      // Determine upgrade type
      const currentParts = vuln.installedVersion.replace(/[\^~>=<]/g, '').split('.');
      const targetParts = patchedVersion.split('.');
      
      let upgradeType: 'patch' | 'minor' | 'major' = 'patch';
      if (currentParts[0] !== targetParts[0]) {
        upgradeType = 'major';
      } else if (currentParts[1] !== targetParts[1]) {
        upgradeType = 'minor';
      }

      suggestions.push({
        packageName: vuln.name,
        currentVersion: vuln.installedVersion,
        suggestedVersion: patchedVersion,
        upgradeType,
        breaking: upgradeType === 'major',
        fixesVulnerabilities: fixedVulns,
        confidence: upgradeType === 'major' ? 0.6 : upgradeType === 'minor' ? 0.8 : 0.95,
      });
    }

    return suggestions;
  }

  /**
   * Audit dependencies in a project
   */
  async audit(projectPath: string): Promise<AuditResult> {
    const startTime = Date.now();

    // Detect package manager
    const packageManager = await detectPackageManager(projectPath);

    // Read lock file path
    const lockFiles: Record<string, string> = {
      npm: 'package-lock.json',
      yarn: 'yarn.lock',
      pnpm: 'pnpm-lock.yaml',
    };
    const lockFilePath = join(projectPath, lockFiles[packageManager]);

    // Run audit
    let auditOutput: NpmAuditOutput;
    try {
      // For now, we only support npm audit
      // TODO: Add yarn and pnpm support
      auditOutput = await runNpmAudit(projectPath);
    } catch (error) {
      console.warn(`Warning: Failed to run audit: ${error}`);
      auditOutput = { vulnerabilities: {}, metadata: undefined };
    }

    const { vulnerabilities, metadata } = parseNpmAuditOutput(auditOutput);

    // Apply filters
    let filteredVulns = vulnerabilities;

    // Filter by severity
    if (this.options.minSeverity) {
      const severityOrder: Severity[] = ['low', 'medium', 'high', 'critical'];
      const minIndex = severityOrder.indexOf(this.options.minSeverity);
      filteredVulns = filteredVulns.filter((v) => {
        const vulnIndex = severityOrder.indexOf(v.highestSeverity);
        return vulnIndex >= minIndex;
      });
    }

    // Filter ignored vulnerabilities
    if (this.options.ignoreVulnerabilities) {
      filteredVulns = filteredVulns.filter((v) => {
        return !v.vulnerabilities.some((vuln) =>
          this.options.ignoreVulnerabilities!.includes(vuln.id)
        );
      });
    }

    // Filter ignored packages
    if (this.options.ignorePackages) {
      filteredVulns = filteredVulns.filter(
        (v) => !this.options.ignorePackages!.includes(v.name)
      );
    }

    // Generate upgrade suggestions
    const upgradeSuggestions = this.options.suggestUpgrades
      ? this.generateUpgradeSuggestions(filteredVulns)
      : [];

    const duration = Date.now() - startTime;

    return {
      vulnerableDependencies: filteredVulns,
      upgradeSuggestions,
      totalDependencies: metadata.total,
      directDependencies: metadata.direct,
      transitiveDependencies: metadata.transitive,
      duration,
      timestamp: new Date(),
      packageManager,
      lockFilePath,
      summary: {
        critical: filteredVulns.filter((v) => v.highestSeverity === 'critical').length,
        high: filteredVulns.filter((v) => v.highestSeverity === 'high').length,
        medium: filteredVulns.filter((v) => v.highestSeverity === 'medium').length,
        low: filteredVulns.filter((v) => v.highestSeverity === 'low').length,
        total: filteredVulns.length,
        fixable: filteredVulns.filter((v) => v.fixAvailable).length,
        breaking: upgradeSuggestions.filter((s) => s.breaking).length,
      },
    };
  }

  /**
   * Generate SBOM for a project
   */
  async generateSBOM(projectPath: string, options?: SBOMOptions): Promise<SBOM> {
    const format = options?.format ?? 'cyclonedx';

    // Read package.json
    const packageJsonPath = join(projectPath, 'package.json');
    const packageJson = JSON.parse(await readFile(packageJsonPath, 'utf-8'));

    // Get audit results for vulnerability info
    const auditResult = options?.includeVulnerabilities
      ? await this.audit(projectPath)
      : null;

    const components: SBOMEntry[] = [];

    // Add direct dependencies
    const addDeps = (deps: Record<string, string> | undefined, type: DependencyType) => {
      if (!deps) return;
      for (const [name, version] of Object.entries(deps)) {
        const cleanVersion = version.replace(/[\^~>=<]/g, '');
        const vuln = auditResult?.vulnerableDependencies.find((v) => v.name === name);

        components.push({
          name,
          version: cleanVersion,
          type,
          isDirect: true,
          purl: `pkg:npm/${name}@${cleanVersion}`,
          vulnerabilityCount: vuln?.vulnerabilities.length ?? 0,
          highestSeverity: vuln?.highestSeverity,
        });
      }
    };

    addDeps(packageJson.dependencies, 'production');
    if (options?.includeDevDependencies) {
      addDeps(packageJson.devDependencies, 'development');
    }

    // Get unique licenses
    const licenses = new Set<string>();
    for (const comp of components) {
      if (comp.license) licenses.add(comp.license);
    }

    return {
      formatVersion: '1.4',
      spec: format,
      projectName: packageJson.name || 'unknown',
      projectVersion: packageJson.version || '0.0.0',
      generatedAt: new Date(),
      generator: {
        name: '@nahisaho/musubix-security',
        version: '1.8.0',
      },
      components,
      summary: {
        totalComponents: components.length,
        directDependencies: components.filter((c) => c.isDirect).length,
        transitiveDependencies: components.filter((c) => !c.isDirect).length,
        uniqueLicenses: Array.from(licenses),
        vulnerableComponents: components.filter((c) => c.vulnerabilityCount > 0).length,
      },
    };
  }
}

/**
 * Helper function to run npm audit
 */
async function runNpmAudit(projectPath: string): Promise<NpmAuditOutput> {
  try {
    const { stdout } = await execAsync('npm audit --json', {
      cwd: projectPath,
      maxBuffer: 10 * 1024 * 1024,
    });
    return JSON.parse(stdout);
  } catch (error: any) {
    if (error.stdout) {
      try {
        return JSON.parse(error.stdout);
      } catch {
        throw new Error(`Failed to parse npm audit output`);
      }
    }
    throw error;
  }
}

/**
 * Create a dependency auditor
 */
export function createDependencyAuditor(options?: AuditOptions): DependencyAuditor {
  return new DependencyAuditor(options);
}
