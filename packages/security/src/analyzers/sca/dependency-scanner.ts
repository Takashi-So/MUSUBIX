/**
 * @fileoverview Dependency Scanner - SCA and SBOM generation
 * @module @nahisaho/musubix-security/analyzers/sca/dependency-scanner
 * @trace DES-SEC3-SCA-001, REQ-SEC3-SCA-001
 */

import { execSync } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import type { Vulnerability, Severity } from '../../types/vulnerability.js';

/**
 * Dependency information
 */
export interface DependencyInfo {
  name: string;
  version: string;
  type: 'production' | 'development' | 'peer' | 'optional';
  license: string;
  repository?: string;
  description?: string;
  dependencies?: string[];
  devDependencies?: string[];
}

/**
 * Dependency vulnerability
 */
export interface DependencyVulnerability {
  id: string;
  package: string;
  severity: Severity;
  vulnerableVersions: string;
  patchedVersions?: string;
  title: string;
  description: string;
  cve?: string;
  cwe?: string[];
  references: string[];
  recommendation: string;
}

/**
 * License risk information
 */
export interface LicenseRisk {
  package: string;
  version: string;
  license: string;
  riskLevel: 'low' | 'medium' | 'high' | 'critical';
  reason: string;
  recommendation?: string;
}

/**
 * SBOM entry (CycloneDX format)
 */
export interface SBOMComponent {
  type: 'library' | 'application' | 'framework' | 'file' | 'container';
  name: string;
  version: string;
  purl?: string;
  licenses?: Array<{ id: string; name: string }>;
  hashes?: Array<{ alg: string; content: string }>;
  externalReferences?: Array<{ type: string; url: string }>;
}

/**
 * SBOM document
 */
export interface SBOMDocument {
  bomFormat: 'CycloneDX';
  specVersion: string;
  serialNumber: string;
  version: number;
  metadata: {
    timestamp: string;
    tools: Array<{ vendor: string; name: string; version: string }>;
    component?: {
      type: string;
      name: string;
      version: string;
    };
  };
  components: SBOMComponent[];
  dependencies?: Array<{
    ref: string;
    dependsOn: string[];
  }>;
}

/**
 * Dependency scan result
 */
export interface DependencyScanResult {
  timestamp: Date;
  projectPath: string;
  packageManager: 'npm' | 'yarn' | 'pnpm' | 'unknown';
  totalDependencies: number;
  directDependencies: number;
  devDependencies: number;
  vulnerabilities: DependencyVulnerability[];
  licenseRisks: LicenseRisk[];
  outdatedPackages: OutdatedPackage[];
  sbom: SBOMDocument;
  summary: DependencySummary;
}

/**
 * Outdated package info
 */
export interface OutdatedPackage {
  name: string;
  currentVersion: string;
  latestVersion: string;
  type: 'major' | 'minor' | 'patch';
  breaking: boolean;
}

/**
 * Dependency scan summary
 */
export interface DependencySummary {
  vulnerabilityCount: {
    critical: number;
    high: number;
    medium: number;
    low: number;
  };
  licenseRiskCount: {
    high: number;
    medium: number;
    low: number;
  };
  outdatedCount: number;
  healthScore: number;
}

/**
 * Dependency scanner options
 */
export interface DependencyScannerOptions {
  checkVulnerabilities?: boolean;
  checkLicenses?: boolean;
  checkOutdated?: boolean;
  generateSBOM?: boolean;
  includeDev?: boolean;
  depth?: number;
  ignoredPackages?: string[];
  allowedLicenses?: string[];
  blockedLicenses?: string[];
}

/**
 * License categories for risk assessment
 */
const LICENSE_CATEGORIES: Record<string, { risk: LicenseRisk['riskLevel']; reason: string }> = {
  // Permissive - Low risk
  'MIT': { risk: 'low', reason: 'Permissive license, minimal restrictions' },
  'ISC': { risk: 'low', reason: 'Permissive license, minimal restrictions' },
  'BSD-2-Clause': { risk: 'low', reason: 'Permissive license, minimal restrictions' },
  'BSD-3-Clause': { risk: 'low', reason: 'Permissive license, minimal restrictions' },
  'Apache-2.0': { risk: 'low', reason: 'Permissive license with patent grant' },
  'Unlicense': { risk: 'low', reason: 'Public domain dedication' },
  'CC0-1.0': { risk: 'low', reason: 'Public domain dedication' },
  '0BSD': { risk: 'low', reason: 'Public domain equivalent' },
  
  // Weak copyleft - Medium risk
  'LGPL-2.1': { risk: 'medium', reason: 'Weak copyleft, dynamic linking permitted' },
  'LGPL-3.0': { risk: 'medium', reason: 'Weak copyleft, dynamic linking permitted' },
  'MPL-2.0': { risk: 'medium', reason: 'File-level copyleft' },
  'EPL-1.0': { risk: 'medium', reason: 'Weak copyleft license' },
  'EPL-2.0': { risk: 'medium', reason: 'Weak copyleft license' },
  
  // Strong copyleft - High risk
  'GPL-2.0': { risk: 'high', reason: 'Strong copyleft, requires derivative works to be GPL' },
  'GPL-3.0': { risk: 'high', reason: 'Strong copyleft with anti-tivoization' },
  'AGPL-3.0': { risk: 'critical', reason: 'Network copyleft, affects SaaS usage' },
  
  // Unknown/Custom - High risk
  'UNKNOWN': { risk: 'high', reason: 'Unknown license, legal review required' },
  'UNLICENSED': { risk: 'high', reason: 'No license specified, all rights reserved' },
  'SEE LICENSE IN': { risk: 'medium', reason: 'Custom license, review required' },
};

/**
 * Dependency Scanner
 * @trace DES-SEC3-SCA-001
 */
export class DependencyScanner {
  private options: Required<DependencyScannerOptions>;

  constructor(options: DependencyScannerOptions = {}) {
    this.options = {
      checkVulnerabilities: options.checkVulnerabilities ?? true,
      checkLicenses: options.checkLicenses ?? true,
      checkOutdated: options.checkOutdated ?? true,
      generateSBOM: options.generateSBOM ?? true,
      includeDev: options.includeDev ?? true,
      depth: options.depth ?? Infinity,
      ignoredPackages: options.ignoredPackages ?? [],
      allowedLicenses: options.allowedLicenses ?? [],
      blockedLicenses: options.blockedLicenses ?? ['AGPL-3.0', 'GPL-3.0'],
    };
  }

  /**
   * Scan project dependencies
   * @trace REQ-SEC3-SCA-001
   */
  async scan(projectPath: string): Promise<DependencyScanResult> {
    const packageManager = this.detectPackageManager(projectPath);
    const dependencies = this.parseDependencies(projectPath);
    
    const vulnerabilities: DependencyVulnerability[] = [];
    const licenseRisks: LicenseRisk[] = [];
    const outdatedPackages: OutdatedPackage[] = [];

    // Check vulnerabilities
    if (this.options.checkVulnerabilities) {
      const vulns = await this.checkVulnerabilities(projectPath, packageManager);
      vulnerabilities.push(...vulns);
    }

    // Check licenses
    if (this.options.checkLicenses) {
      const risks = this.checkLicenses(dependencies);
      licenseRisks.push(...risks);
    }

    // Check outdated packages
    if (this.options.checkOutdated) {
      const outdated = await this.checkOutdated(projectPath, packageManager);
      outdatedPackages.push(...outdated);
    }

    // Generate SBOM
    const sbom = this.options.generateSBOM 
      ? this.generateSBOMPrivate(projectPath, dependencies)
      : this.createEmptySBOM(projectPath);

    const directDeps = dependencies.filter(d => d.type === 'production').length;
    const devDeps = dependencies.filter(d => d.type === 'development').length;

    return {
      timestamp: new Date(),
      projectPath,
      packageManager,
      totalDependencies: dependencies.length,
      directDependencies: directDeps,
      devDependencies: devDeps,
      vulnerabilities,
      licenseRisks,
      outdatedPackages,
      sbom,
      summary: this.generateSummary(vulnerabilities, licenseRisks, outdatedPackages),
    };
  }

  /**
   * Alias for scan() - for API compatibility
   */
  async scanDependencies(projectPath: string): Promise<{
    packageManager: DependencyScanResult['packageManager'];
    dependencies: Array<{ name: string; version: string; isDev: boolean }>;
    vulnerabilities: Array<{ name: string; severity: string; advisory: string }>;
    outdatedPackages: Array<{ name: string; current: string; latest: string; updateType: string }>;
    licenseRisks: Array<{ package: string; license: string; risk: string }>;
    summary: {
      totalDependencies: number;
      vulnerableCount: number;
      outdatedCount: number;
      healthScore: number;
    };
  }> {
    const result = await this.scan(projectPath);
    
    // Parse dependencies to include isDev
    const deps = this.parseDependenciesPublic(projectPath);
    
    return {
      packageManager: result.packageManager,
      dependencies: deps.map(d => ({
        name: d.name,
        version: d.version,
        isDev: d.type === 'development',
      })),
      vulnerabilities: result.vulnerabilities.map(v => ({
        name: v.package,
        severity: v.severity,
        advisory: v.id,
      })),
      outdatedPackages: result.outdatedPackages.map(o => ({
        name: o.name,
        current: o.currentVersion,
        latest: o.latestVersion,
        updateType: o.type,
      })),
      licenseRisks: result.licenseRisks.map(r => ({
        package: r.package,
        license: r.license,
        risk: r.riskLevel,
      })),
      summary: {
        totalDependencies: result.totalDependencies,
        vulnerableCount: result.summary.vulnerabilityCount.critical + 
          result.summary.vulnerabilityCount.high + 
          result.summary.vulnerabilityCount.medium + 
          result.summary.vulnerabilityCount.low,
        outdatedCount: result.outdatedPackages.length,
        healthScore: result.summary.healthScore,
      },
    };
  }

  /**
   * Public accessor for parsing dependencies
   */
  private parseDependenciesPublic(projectPath: string): DependencyInfo[] {
    return this.parseDependencies(projectPath);
  }

  /**
   * Generate SBOM from scan result (public)
   */
  generateSBOM(scanResult: DependencyScanResult | string, deps?: DependencyInfo[]): SBOMDocument {
    if (typeof scanResult === 'string') {
      // Old signature: generateSBOM(projectPath, dependencies)
      return this.generateSBOMInternal(scanResult, deps ?? []);
    }
    // New signature: generateSBOM(scanResult)
    return scanResult.sbom;
  }

  /**
   * Internal SBOM generation
   */
  private generateSBOMInternal(projectPath: string, dependencies: DependencyInfo[]): SBOMDocument {
    const packageJsonPath = join(projectPath, 'package.json');
    let projectName = 'unknown';
    let projectVersion = '0.0.0';

    try {
      if (existsSync(packageJsonPath)) {
        const pkg = JSON.parse(readFileSync(packageJsonPath, 'utf-8'));
        projectName = pkg.name ?? 'unknown';
        projectVersion = pkg.version ?? '0.0.0';
      }
    } catch {
      // Ignore
    }

    return {
      bomFormat: 'CycloneDX',
      specVersion: '1.4',
      serialNumber: `urn:uuid:${this.generateUUID()}`,
      version: 1,
      metadata: {
        timestamp: new Date().toISOString(),
        tools: [{
          vendor: 'MUSUBIX',
          name: 'musubix-security',
          version: '1.8.0',
        }],
        component: {
          type: 'application',
          name: projectName,
          version: projectVersion,
        },
      },
      components: dependencies.map(dep => ({
        type: 'library' as const,
        name: dep.name,
        version: dep.version,
        purl: `pkg:npm/${dep.name}@${dep.version}`,
        licenses: dep.license ? [{ id: dep.license, name: dep.license }] : undefined,
      })),
      dependencies: [],
    };
  }

  /**
   * Detect package manager
   */
  private detectPackageManager(projectPath: string): DependencyScanResult['packageManager'] {
    if (existsSync(join(projectPath, 'pnpm-lock.yaml'))) return 'pnpm';
    if (existsSync(join(projectPath, 'yarn.lock'))) return 'yarn';
    if (existsSync(join(projectPath, 'package-lock.json'))) return 'npm';
    if (existsSync(join(projectPath, 'package.json'))) return 'npm';
    return 'unknown';
  }

  /**
   * Parse dependencies from package.json
   */
  private parseDependencies(projectPath: string): DependencyInfo[] {
    const packageJsonPath = join(projectPath, 'package.json');
    if (!existsSync(packageJsonPath)) {
      return [];
    }

    const packageJson = JSON.parse(readFileSync(packageJsonPath, 'utf-8'));
    const dependencies: DependencyInfo[] = [];

    // Production dependencies
    if (packageJson.dependencies) {
      for (const [name, version] of Object.entries(packageJson.dependencies)) {
        if (this.options.ignoredPackages.includes(name)) continue;
        dependencies.push({
          name,
          version: String(version),
          type: 'production',
          license: this.getLicense(projectPath, name),
        });
      }
    }

    // Dev dependencies
    if (this.options.includeDev && packageJson.devDependencies) {
      for (const [name, version] of Object.entries(packageJson.devDependencies)) {
        if (this.options.ignoredPackages.includes(name)) continue;
        dependencies.push({
          name,
          version: String(version),
          type: 'development',
          license: this.getLicense(projectPath, name),
        });
      }
    }

    // Peer dependencies
    if (packageJson.peerDependencies) {
      for (const [name, version] of Object.entries(packageJson.peerDependencies)) {
        if (this.options.ignoredPackages.includes(name)) continue;
        dependencies.push({
          name,
          version: String(version),
          type: 'peer',
          license: this.getLicense(projectPath, name),
        });
      }
    }

    return dependencies;
  }

  /**
   * Get license for a package
   */
  private getLicense(projectPath: string, packageName: string): string {
    const modulePath = join(projectPath, 'node_modules', packageName, 'package.json');
    try {
      if (existsSync(modulePath)) {
        const pkg = JSON.parse(readFileSync(modulePath, 'utf-8'));
        if (typeof pkg.license === 'string') return pkg.license;
        if (pkg.license?.type) return pkg.license.type;
        if (Array.isArray(pkg.licenses)) return pkg.licenses[0]?.type ?? 'UNKNOWN';
      }
    } catch {
      // Ignore errors
    }
    return 'UNKNOWN';
  }

  /**
   * Check for vulnerabilities using npm audit
   */
  private async checkVulnerabilities(
    projectPath: string,
    _packageManager: DependencyScanResult['packageManager']
  ): Promise<DependencyVulnerability[]> {
    const vulnerabilities: DependencyVulnerability[] = [];

    try {
      const result = execSync('npm audit --json 2>/dev/null', {
        cwd: projectPath,
        encoding: 'utf-8',
        maxBuffer: 10 * 1024 * 1024,
      });

      const auditData = JSON.parse(result);
      
      if (auditData.vulnerabilities) {
        for (const [pkgName, vulnData] of Object.entries(auditData.vulnerabilities as Record<string, any>)) {
          if (this.options.ignoredPackages.includes(pkgName)) continue;

          const severity = this.mapNpmSeverity(vulnData.severity);
          
          for (const via of vulnData.via ?? []) {
            if (typeof via === 'string') continue;
            
            vulnerabilities.push({
              id: via.source?.toString() ?? `NPM-${pkgName}`,
              package: pkgName,
              severity,
              vulnerableVersions: vulnData.range ?? '*',
              patchedVersions: vulnData.fixAvailable?.version,
              title: via.title ?? `Vulnerability in ${pkgName}`,
              description: via.title ?? 'No description available',
              cve: via.cve,
              cwe: via.cwe ? [via.cwe] : undefined,
              references: via.url ? [via.url] : [],
              recommendation: vulnData.fixAvailable 
                ? `Upgrade to ${vulnData.fixAvailable.name}@${vulnData.fixAvailable.version}`
                : 'No fix available, consider using an alternative package',
            });
          }
        }
      }
    } catch (error) {
      // npm audit may exit with non-zero if vulnerabilities found
      // Try to parse the output anyway
      const errorOutput = (error as any)?.stdout;
      if (errorOutput) {
        try {
          const auditData = JSON.parse(errorOutput);
          // Same parsing logic as above
          if (auditData.vulnerabilities) {
            for (const [pkgName, vulnData] of Object.entries(auditData.vulnerabilities as Record<string, any>)) {
              const severity = this.mapNpmSeverity(vulnData.severity);
              vulnerabilities.push({
                id: `NPM-${pkgName}-${Date.now()}`,
                package: pkgName,
                severity,
                vulnerableVersions: vulnData.range ?? '*',
                patchedVersions: vulnData.fixAvailable?.version,
                title: `Vulnerability in ${pkgName}`,
                description: 'Detected by npm audit',
                references: [],
                recommendation: vulnData.fixAvailable 
                  ? `Upgrade to ${vulnData.fixAvailable.name}@${vulnData.fixAvailable.version}`
                  : 'Review and update the package',
              });
            }
          }
        } catch {
          // Ignore parse errors
        }
      }
    }

    return vulnerabilities;
  }

  /**
   * Map npm severity to our severity type
   */
  private mapNpmSeverity(npmSeverity: string): Severity {
    const map: Record<string, Severity> = {
      'critical': 'critical',
      'high': 'high',
      'moderate': 'medium',
      'low': 'low',
      'info': 'info',
    };
    return map[npmSeverity] ?? 'medium';
  }

  /**
   * Check license risks
   */
  private checkLicenses(dependencies: DependencyInfo[]): LicenseRisk[] {
    const risks: LicenseRisk[] = [];

    for (const dep of dependencies) {
      const normalizedLicense = this.normalizeLicense(dep.license);
      
      // Check blocked licenses
      if (this.options.blockedLicenses.includes(normalizedLicense)) {
        risks.push({
          package: dep.name,
          version: dep.version,
          license: dep.license,
          riskLevel: 'critical',
          reason: `Blocked license: ${dep.license}`,
          recommendation: 'Find an alternative package with a compatible license',
        });
        continue;
      }

      // Check allowed licenses
      if (this.options.allowedLicenses.length > 0 && 
          !this.options.allowedLicenses.includes(normalizedLicense)) {
        risks.push({
          package: dep.name,
          version: dep.version,
          license: dep.license,
          riskLevel: 'medium',
          reason: 'License not in allowed list',
          recommendation: 'Review license compatibility',
        });
        continue;
      }

      // Check license category
      const category = LICENSE_CATEGORIES[normalizedLicense] ?? LICENSE_CATEGORIES['UNKNOWN'];
      if (category.risk !== 'low') {
        risks.push({
          package: dep.name,
          version: dep.version,
          license: dep.license,
          riskLevel: category.risk,
          reason: category.reason,
          recommendation: category.risk === 'high' || category.risk === 'critical'
            ? 'Consider using an alternative package'
            : 'Review license terms before commercial use',
        });
      }
    }

    return risks;
  }

  /**
   * Normalize license identifier
   */
  private normalizeLicense(license: string): string {
    const normalized = license.trim().toUpperCase();
    
    // Handle common variations
    const mappings: Record<string, string> = {
      'MIT LICENSE': 'MIT',
      '(MIT)': 'MIT',
      'APACHE 2.0': 'Apache-2.0',
      'APACHE LICENSE 2.0': 'Apache-2.0',
      'BSD': 'BSD-3-Clause',
      'ISC LICENSE': 'ISC',
    };

    return mappings[normalized] ?? license;
  }

  /**
   * Check for outdated packages
   */
  private async checkOutdated(
    projectPath: string,
    _packageManager: DependencyScanResult['packageManager']
  ): Promise<OutdatedPackage[]> {
    const outdated: OutdatedPackage[] = [];

    try {
      const result = execSync('npm outdated --json 2>/dev/null', {
        cwd: projectPath,
        encoding: 'utf-8',
        maxBuffer: 10 * 1024 * 1024,
      });

      const data = JSON.parse(result || '{}');
      
      for (const [name, info] of Object.entries(data as Record<string, any>)) {
        if (this.options.ignoredPackages.includes(name)) continue;

        const current = info.current ?? info.wanted;
        const latest = info.latest;
        
        if (!current || !latest) continue;

        const updateType = this.determineUpdateType(current, latest);
        
        outdated.push({
          name,
          currentVersion: current,
          latestVersion: latest,
          type: updateType,
          breaking: updateType === 'major',
        });
      }
    } catch {
      // npm outdated exits with non-zero when outdated packages found
      // This is expected behavior
    }

    return outdated;
  }

  /**
   * Determine update type
   */
  private determineUpdateType(current: string, latest: string): OutdatedPackage['type'] {
    const currentParts = current.replace(/[^0-9.]/g, '').split('.');
    const latestParts = latest.replace(/[^0-9.]/g, '').split('.');

    const currentMajor = parseInt(currentParts[0] ?? '0', 10);
    const latestMajor = parseInt(latestParts[0] ?? '0', 10);
    
    if (latestMajor > currentMajor) return 'major';
    
    const currentMinor = parseInt(currentParts[1] ?? '0', 10);
    const latestMinor = parseInt(latestParts[1] ?? '0', 10);
    
    if (latestMinor > currentMinor) return 'minor';
    
    return 'patch';
  }

  /**
   * Generate SBOM document
   */
  private generateSBOMPrivate(projectPath: string, dependencies: DependencyInfo[]): SBOMDocument {
    const packageJsonPath = join(projectPath, 'package.json');
    let projectName = 'unknown';
    let projectVersion = '0.0.0';

    if (existsSync(packageJsonPath)) {
      const pkg = JSON.parse(readFileSync(packageJsonPath, 'utf-8'));
      projectName = pkg.name ?? 'unknown';
      projectVersion = pkg.version ?? '0.0.0';
    }

    const components: SBOMComponent[] = dependencies.map(dep => ({
      type: 'library',
      name: dep.name,
      version: dep.version.replace(/[\^~>=<]/g, ''),
      purl: `pkg:npm/${dep.name}@${dep.version.replace(/[\^~>=<]/g, '')}`,
      licenses: dep.license !== 'UNKNOWN' ? [{ id: dep.license, name: dep.license }] : undefined,
    }));

    return {
      bomFormat: 'CycloneDX',
      specVersion: '1.4',
      serialNumber: `urn:uuid:${this.generateUUID()}`,
      version: 1,
      metadata: {
        timestamp: new Date().toISOString(),
        tools: [
          { vendor: 'nahisaho', name: 'musubix-security', version: '1.8.0' },
        ],
        component: {
          type: 'application',
          name: projectName,
          version: projectVersion,
        },
      },
      components,
      dependencies: this.buildDependencyGraph(projectPath, dependencies),
    };
  }

  /**
   * Build dependency graph for SBOM
   */
  private buildDependencyGraph(
    projectPath: string,
    dependencies: DependencyInfo[]
  ): SBOMDocument['dependencies'] {
    const graph: SBOMDocument['dependencies'] = [];

    for (const dep of dependencies) {
      const modulePath = join(projectPath, 'node_modules', dep.name, 'package.json');
      const dependsOn: string[] = [];

      try {
        if (existsSync(modulePath)) {
          const pkg = JSON.parse(readFileSync(modulePath, 'utf-8'));
          if (pkg.dependencies) {
            for (const subDep of Object.keys(pkg.dependencies)) {
              dependsOn.push(`pkg:npm/${subDep}`);
            }
          }
        }
      } catch {
        // Ignore errors
      }

      graph.push({
        ref: `pkg:npm/${dep.name}@${dep.version.replace(/[\^~>=<]/g, '')}`,
        dependsOn,
      });
    }

    return graph;
  }

  /**
   * Create empty SBOM
   */
  private createEmptySBOM(projectPath: string): SBOMDocument {
    return this.generateSBOM(projectPath, []);
  }

  /**
   * Generate UUID v4
   */
  private generateUUID(): string {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, (c) => {
      const r = Math.random() * 16 | 0;
      const v = c === 'x' ? r : (r & 0x3 | 0x8);
      return v.toString(16);
    });
  }

  /**
   * Generate scan summary
   */
  private generateSummary(
    vulnerabilities: DependencyVulnerability[],
    licenseRisks: LicenseRisk[],
    outdated: OutdatedPackage[]
  ): DependencySummary {
    const vulnCount = { critical: 0, high: 0, medium: 0, low: 0 };
    for (const v of vulnerabilities) {
      if (v.severity in vulnCount) {
        vulnCount[v.severity as keyof typeof vulnCount]++;
      }
    }

    const licenseCount = { high: 0, medium: 0, low: 0 };
    for (const r of licenseRisks) {
      if (r.riskLevel === 'critical') licenseCount.high++;
      else if (r.riskLevel in licenseCount) {
        licenseCount[r.riskLevel as keyof typeof licenseCount]++;
      }
    }

    // Calculate health score (0-100)
    let score = 100;
    score -= vulnCount.critical * 20;
    score -= vulnCount.high * 10;
    score -= vulnCount.medium * 5;
    score -= vulnCount.low * 1;
    score -= licenseCount.high * 15;
    score -= licenseCount.medium * 5;
    score -= outdated.filter(o => o.type === 'major').length * 3;
    score = Math.max(0, score);

    return {
      vulnerabilityCount: vulnCount,
      licenseRiskCount: licenseCount,
      outdatedCount: outdated.length,
      healthScore: score,
    };
  }

  /**
   * Convert scan result to vulnerabilities
   */
  toVulnerabilities(result: DependencyScanResult): Vulnerability[] {
    return result.vulnerabilities.map(v => ({
      id: v.id,
      type: 'dependency' as const,
      severity: v.severity,
      cwes: v.cwe ?? [],
      owasp: ['A06:2021'], // Vulnerable and Outdated Components
      location: {
        file: 'package.json',
        startLine: 1,
        endLine: 1,
        startColumn: 0,
        endColumn: 0,
      },
      description: `${v.package}: ${v.title}`,
      recommendation: v.recommendation,
      confidence: 0.95,
      ruleId: v.cve ?? v.id,
      codeSnippet: `"${v.package}": "${v.vulnerableVersions}"`,
      detectedAt: new Date(),
    }));
  }
}

/**
 * Create dependency scanner instance
 */
export function createDependencyScanner(options?: DependencyScannerOptions): DependencyScanner {
  return new DependencyScanner(options);
}
