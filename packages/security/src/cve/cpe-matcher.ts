/**
 * @fileoverview CPE (Common Platform Enumeration) Matching Engine
 * @module @nahisaho/musubix-security/cve/cpe-matcher
 *
 * Provides npm package name to CPE conversion and semver-based
 * vulnerability matching.
 *
 * @requirement REQ-CVE-003 - CPE matching for vulnerability lookup
 * @design DES-EPIC2-004 - CPE Matcher component
 */

/**
 * CPE 2.3 URI components
 * @see https://nvd.nist.gov/products/cpe
 */
export interface CPEComponents {
  /** CPE part: 'a' = application, 'o' = OS, 'h' = hardware */
  part: 'a' | 'o' | 'h';
  /** Vendor/publisher name */
  vendor: string;
  /** Product name */
  product: string;
  /** Version string */
  version: string;
  /** Update/patch level */
  update?: string;
  /** Edition */
  edition?: string;
  /** Language */
  language?: string;
  /** Software edition */
  swEdition?: string;
  /** Target software */
  targetSw?: string;
  /** Target hardware */
  targetHw?: string;
  /** Other attributes */
  other?: string;
}

/**
 * Version range for vulnerability matching
 */
export interface VersionRange {
  /** Starting version (inclusive unless startExcluding is set) */
  versionStart?: string;
  /** Ending version (inclusive unless endExcluding is set) */
  versionEnd?: string;
  /** Start version is exclusive */
  versionStartExcluding?: boolean;
  /** End version is exclusive */
  versionEndExcluding?: boolean;
}

/**
 * CPE match criteria from NVD
 */
export interface CPEMatch {
  /** CPE 2.3 URI */
  criteria: string;
  /** Whether this criteria makes the configuration vulnerable */
  vulnerable: boolean;
  /** Match criteria ID */
  matchCriteriaId: string;
  /** Version range */
  versionRange?: VersionRange;
}

/**
 * Vulnerability match result
 */
export interface VulnerabilityMatch {
  /** Package name */
  packageName: string;
  /** Package version */
  packageVersion: string;
  /** CVE ID */
  cveId: string;
  /** Generated CPE URI */
  cpe: string;
  /** Match criteria that matched */
  matchCriteria?: CPEMatch;
  /** Whether version is in vulnerable range */
  isVulnerable: boolean;
  /** Match confidence (0-1) */
  confidence: number;
}

/**
 * Known npm package to vendor mappings
 * Many npm packages use different names than their CPE vendor
 */
const VENDOR_MAPPINGS: Record<string, string> = {
  // Major frameworks
  'express': 'expressjs',
  'koa': 'koajs',
  'fastify': 'fastify',
  'next': 'vercel',
  'nuxt': 'nuxtjs',
  'gatsby': 'gatsbyjs',
  
  // Utilities
  'lodash': 'lodash',
  'underscore': 'underscorejs',
  'moment': 'momentjs',
  'dayjs': 'dayjs',
  
  // Security-related
  'jsonwebtoken': 'auth0',
  'passport': 'passportjs',
  'helmet': 'helmetjs',
  
  // Database clients
  'mongoose': 'mongoosejs',
  'sequelize': 'sequelizejs',
  'typeorm': 'typeorm',
  'prisma': 'prisma',
  'pg': 'postgresql',
  'mysql2': 'mysql',
  'sqlite3': 'sqlite',
  
  // Build tools
  'webpack': 'webpack',
  'vite': 'vitejs',
  'esbuild': 'esbuild',
  'rollup': 'rollupjs',
  
  // Testing
  'jest': 'jestjs',
  'mocha': 'mochajs',
  'vitest': 'vitest',
  
  // HTTP clients
  'axios': 'axios',
  'node-fetch': 'node-fetch',
  'got': 'sindresorhus',
  
  // Template engines
  'pug': 'pugjs',
  'ejs': 'ejs',
  'handlebars': 'handlebarsjs',
  
  // Validation
  'joi': 'hapijs',
  'yup': 'jquense',
  'zod': 'colinhacks',
  
  // Crypto
  'bcrypt': 'bcrypt',
  'argon2': 'argon2',
  'crypto-js': 'crypto-js',
};

/**
 * Packages that should be searched under 'node.js' vendor
 */
const NODEJS_VENDOR_PACKAGES = new Set([
  'node',
  'npm',
  'npx',
]);

/**
 * CPE Matcher for npm packages
 *
 * @example
 * ```typescript
 * const matcher = new CPEMatcher();
 *
 * // Generate CPE from package
 * const cpe = matcher.generateCPE('express', '4.18.2');
 * // => 'cpe:2.3:a:expressjs:express:4.18.2:*:*:*:*:node.js:*:*'
 *
 * // Check if version is vulnerable
 * const isVuln = matcher.isVersionVulnerable('4.18.2', {
 *   versionStart: '4.0.0',
 *   versionEnd: '4.19.0',
 *   versionEndExcluding: true
 * });
 * ```
 */
export class CPEMatcher {
  private vendorMappings: Map<string, string>;

  constructor(customMappings?: Record<string, string>) {
    this.vendorMappings = new Map([
      ...Object.entries(VENDOR_MAPPINGS),
      ...Object.entries(customMappings ?? {}),
    ]);
  }

  /**
   * Generate CPE 2.3 URI for an npm package
   * @param packageName - npm package name
   * @param version - Package version
   * @returns CPE 2.3 formatted URI
   */
  generateCPE(packageName: string, version: string): string {
    const components = this.packageToCPEComponents(packageName, version);
    return this.componentsToURI(components);
  }

  /**
   * Convert npm package info to CPE components
   */
  packageToCPEComponents(packageName: string, version: string): CPEComponents {
    const normalizedName = this.normalizeName(packageName);
    const vendor = this.resolveVendor(packageName);

    return {
      part: 'a',
      vendor,
      product: normalizedName,
      version: this.normalizeVersion(version),
      targetSw: 'node.js',
    };
  }

  /**
   * Convert CPE components to URI string
   */
  componentsToURI(components: CPEComponents): string {
    const parts = [
      'cpe:2.3',
      components.part,
      this.escapeComponent(components.vendor),
      this.escapeComponent(components.product),
      this.escapeComponent(components.version),
      this.escapeComponent(components.update ?? '*'),
      this.escapeComponent(components.edition ?? '*'),
      this.escapeComponent(components.language ?? '*'),
      this.escapeComponent(components.swEdition ?? '*'),
      this.escapeComponent(components.targetSw ?? '*'),
      this.escapeComponent(components.targetHw ?? '*'),
      this.escapeComponent(components.other ?? '*'),
    ];

    return parts.join(':');
  }

  /**
   * Parse CPE 2.3 URI to components
   */
  parseURI(cpeUri: string): CPEComponents | null {
    const match = cpeUri.match(
      /^cpe:2\.3:([aoh]):([^:]+):([^:]+):([^:]+):([^:]*):([^:]*):([^:]*):([^:]*):([^:]*):([^:]*):([^:]*)$/
    );

    if (!match) {
      return null;
    }

    return {
      part: match[1] as 'a' | 'o' | 'h',
      vendor: this.unescapeComponent(match[2]),
      product: this.unescapeComponent(match[3]),
      version: this.unescapeComponent(match[4]),
      update: match[5] && match[5] !== '*' ? this.unescapeComponent(match[5]) : undefined,
      edition: match[6] && match[6] !== '*' ? this.unescapeComponent(match[6]) : undefined,
      language: match[7] && match[7] !== '*' ? this.unescapeComponent(match[7]) : undefined,
      swEdition: match[8] && match[8] !== '*' ? this.unescapeComponent(match[8]) : undefined,
      targetSw: match[9] && match[9] !== '*' ? this.unescapeComponent(match[9]) : undefined,
      targetHw: match[10] && match[10] !== '*' ? this.unescapeComponent(match[10]) : undefined,
      other: match[11] && match[11] !== '*' ? this.unescapeComponent(match[11]) : undefined,
    };
  }

  /**
   * Check if a version falls within a vulnerable range
   * @param version - Version to check
   * @param range - Version range from CVE data
   * @returns True if version is within vulnerable range
   */
  isVersionVulnerable(version: string, range: VersionRange): boolean {
    const normalizedVersion = this.normalizeVersion(version);

    // Handle "all versions" case
    if (!range.versionStart && !range.versionEnd) {
      return true;
    }

    const vStart = range.versionStart ? this.normalizeVersion(range.versionStart) : null;
    const vEnd = range.versionEnd ? this.normalizeVersion(range.versionEnd) : null;

    // Check start bound
    if (vStart) {
      const comparison = this.compareVersions(normalizedVersion, vStart);
      if (range.versionStartExcluding) {
        if (comparison <= 0) return false;
      } else {
        if (comparison < 0) return false;
      }
    }

    // Check end bound
    if (vEnd) {
      const comparison = this.compareVersions(normalizedVersion, vEnd);
      if (range.versionEndExcluding) {
        if (comparison >= 0) return false;
      } else {
        if (comparison > 0) return false;
      }
    }

    return true;
  }

  /**
   * Match a package against CPE criteria
   */
  matchPackage(
    packageName: string,
    packageVersion: string,
    cpeMatch: CPEMatch
  ): VulnerabilityMatch | null {
    const parsed = this.parseURI(cpeMatch.criteria);
    if (!parsed) {
      return null;
    }

    const normalizedName = this.normalizeName(packageName);
    const expectedVendors = this.getPossibleVendors(packageName);

    // Check if product matches
    const productMatches =
      parsed.product === normalizedName ||
      parsed.product === '*' ||
      parsed.product.includes(normalizedName);

    // Check if vendor matches
    const vendorMatches =
      parsed.vendor === '*' ||
      expectedVendors.some(v => 
        parsed.vendor === v || 
        parsed.vendor.includes(v) ||
        v.includes(parsed.vendor)
      );

    if (!productMatches || !vendorMatches) {
      return null;
    }

    // Calculate confidence based on match quality
    let confidence = 0.5;
    if (parsed.vendor !== '*' && expectedVendors.includes(parsed.vendor)) {
      confidence += 0.25;
    }
    if (parsed.product === normalizedName) {
      confidence += 0.25;
    }

    // Check version range
    const versionRange: VersionRange | undefined = cpeMatch.versionRange;
    let isVulnerable = cpeMatch.vulnerable;

    if (versionRange) {
      isVulnerable = isVulnerable && this.isVersionVulnerable(packageVersion, versionRange);
    } else if (parsed.version !== '*') {
      // Exact version match
      isVulnerable = isVulnerable && this.compareVersions(
        this.normalizeVersion(packageVersion),
        this.normalizeVersion(parsed.version)
      ) === 0;
    }

    return {
      packageName,
      packageVersion,
      cveId: '', // To be filled by caller
      cpe: this.generateCPE(packageName, packageVersion),
      matchCriteria: cpeMatch,
      isVulnerable,
      confidence,
    };
  }

  /**
   * Add a custom vendor mapping
   */
  addVendorMapping(packageName: string, vendor: string): void {
    this.vendorMappings.set(packageName.toLowerCase(), vendor);
  }

  /**
   * Get the vendor for a package
   */
  getVendor(packageName: string): string {
    return this.resolveVendor(packageName);
  }

  /**
   * Normalize package name for CPE
   */
  private normalizeName(name: string): string {
    // Handle scoped packages (@org/package -> package)
    const unscoped = name.startsWith('@') ? name.split('/')[1] : name;
    
    // Convert to lowercase, replace special chars
    return unscoped
      .toLowerCase()
      .replace(/[^a-z0-9]/g, '_')
      .replace(/_+/g, '_')
      .replace(/^_|_$/g, '');
  }

  /**
   * Normalize version string
   */
  private normalizeVersion(version: string): string {
    // Remove leading 'v' and any pre-release/build metadata for comparison
    return version
      .replace(/^v/, '')
      .replace(/[+-].*$/, '') // Remove pre-release (-beta) and build (+build) metadata
      .trim();
  }

  /**
   * Resolve vendor for a package
   */
  private resolveVendor(packageName: string): string {
    const normalized = packageName.toLowerCase();
    
    // Check for scoped packages
    if (normalized.startsWith('@')) {
      const [scope] = normalized.slice(1).split('/');
      // Use scope as vendor (without @)
      return scope.replace(/[^a-z0-9]/g, '_');
    }

    // Check custom mappings
    if (this.vendorMappings.has(normalized)) {
      return this.vendorMappings.get(normalized)!;
    }

    // Check Node.js packages
    if (NODEJS_VENDOR_PACKAGES.has(normalized)) {
      return 'nodejs';
    }

    // Default: use package name as vendor
    return this.normalizeName(packageName);
  }

  /**
   * Get possible vendor names for a package
   */
  private getPossibleVendors(packageName: string): string[] {
    const vendors = new Set<string>();
    const normalized = packageName.toLowerCase();

    // Add resolved vendor
    vendors.add(this.resolveVendor(packageName));

    // Add normalized name
    vendors.add(this.normalizeName(packageName));

    // Add common variations
    if (normalized.endsWith('js')) {
      vendors.add(normalized.slice(0, -2));
    }
    if (!normalized.endsWith('js')) {
      vendors.add(`${normalized}js`);
    }

    return Array.from(vendors);
  }

  /**
   * Compare two semver versions
   * @returns -1 if a < b, 0 if a == b, 1 if a > b
   */
  compareVersions(a: string, b: string): number {
    const partsA = a.split('.').map(p => parseInt(p, 10) || 0);
    const partsB = b.split('.').map(p => parseInt(p, 10) || 0);

    const maxLen = Math.max(partsA.length, partsB.length);

    for (let i = 0; i < maxLen; i++) {
      const partA = partsA[i] ?? 0;
      const partB = partsB[i] ?? 0;

      if (partA < partB) return -1;
      if (partA > partB) return 1;
    }

    return 0;
  }

  /**
   * Escape special characters in CPE component
   */
  private escapeComponent(value: string): string {
    if (value === '*' || value === '-') {
      return value;
    }
    return value
      .replace(/\\/g, '\\\\')
      .replace(/\*/g, '\\*')
      .replace(/\?/g, '\\?');
  }

  /**
   * Unescape CPE component value
   */
  private unescapeComponent(value: string): string {
    if (value === '*' || value === '-') {
      return value;
    }
    return value
      .replace(/\\\\/g, '\\')
      .replace(/\\\*/g, '*')
      .replace(/\\\?/g, '?');
  }
}

/**
 * Create a CPE search query from package info
 * Generates wildcarded CPE for searching NVD
 */
export function createCPESearchQuery(
  packageName: string,
  vendor?: string
): string {
  const matcher = new CPEMatcher();
  const normalizedName = packageName
    .toLowerCase()
    .replace(/[^a-z0-9]/g, '_');
  
  const resolvedVendor = vendor ?? matcher.getVendor(packageName);
  
  return `cpe:2.3:a:${resolvedVendor}:${normalizedName}:*:*:*:*:*:*:*:*`;
}

/**
 * Extract package name from CPE URI
 */
export function extractPackageFromCPE(cpeUri: string): string | null {
  const matcher = new CPEMatcher();
  const parsed = matcher.parseURI(cpeUri);
  return parsed?.product ?? null;
}
