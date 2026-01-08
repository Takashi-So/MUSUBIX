/**
 * @fileoverview CVE and NVD type definitions
 * @module @nahisaho/musubix-security/types/cve
 * @trace REQ-SEC-CVE-001, REQ-SEC-CVE-002, REQ-SEC-CVE-003, REQ-SEC-CVE-004
 */

/**
 * CVSS v3.x score details
 * @trace DES-SEC-CVE-001
 */
export interface CVSSScore {
  /** CVSS version */
  version: '3.0' | '3.1';
  /** Base score (0.0 - 10.0) */
  baseScore: number;
  /** Severity based on base score */
  severity: CVSSSeverity;
  /** CVSS vector string (e.g., "CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H") */
  vectorString: string;
  /** Attack Vector */
  attackVector: 'NETWORK' | 'ADJACENT_NETWORK' | 'LOCAL' | 'PHYSICAL';
  /** Attack Complexity */
  attackComplexity: 'LOW' | 'HIGH';
  /** Privileges Required */
  privilegesRequired: 'NONE' | 'LOW' | 'HIGH';
  /** User Interaction */
  userInteraction: 'NONE' | 'REQUIRED';
  /** Scope */
  scope: 'UNCHANGED' | 'CHANGED';
  /** Confidentiality Impact */
  confidentialityImpact: 'NONE' | 'LOW' | 'HIGH';
  /** Integrity Impact */
  integrityImpact: 'NONE' | 'LOW' | 'HIGH';
  /** Availability Impact */
  availabilityImpact: 'NONE' | 'LOW' | 'HIGH';
}

/**
 * CVSS severity levels
 */
export type CVSSSeverity = 'NONE' | 'LOW' | 'MEDIUM' | 'HIGH' | 'CRITICAL';

/**
 * CVE reference link
 */
export interface CVEReference {
  /** Reference URL */
  url: string;
  /** Reference source (e.g., "MISC", "CONFIRM", "VENDOR_ADVISORY") */
  source: string;
  /** Reference tags */
  tags?: string[];
}

/**
 * CPE (Common Platform Enumeration) match criteria
 * @trace DES-SEC-CVE-001
 */
export interface CPEMatch {
  /** CPE 2.3 URI format */
  cpe: string;
  /** Vulnerable flag */
  vulnerable: boolean;
  /** Version start (including) */
  versionStartIncluding?: string;
  /** Version start (excluding) */
  versionStartExcluding?: string;
  /** Version end (including) */
  versionEndIncluding?: string;
  /** Version end (excluding) */
  versionEndExcluding?: string;
}

/**
 * CVE (Common Vulnerabilities and Exposures) entry
 * @trace REQ-SEC-CVE-001, DES-SEC-CVE-001
 */
export interface CVE {
  /** CVE identifier (e.g., "CVE-2021-44228") */
  id: string;
  /** Vulnerability description */
  description: string;
  /** Publication date */
  published: Date;
  /** Last modification date */
  lastModified: Date;
  /** CVSS v3.x score */
  cvss?: CVSSScore;
  /** Related CWE identifiers */
  cwes: string[];
  /** Reference links */
  references: CVEReference[];
  /** Affected products (CPE matches) */
  affectedProducts: CPEMatch[];
  /** Vulnerability status */
  status: CVEStatus;
}

/**
 * CVE status
 */
export type CVEStatus =
  | 'RECEIVED'
  | 'AWAITING_ANALYSIS'
  | 'UNDERGOING_ANALYSIS'
  | 'ANALYZED'
  | 'MODIFIED'
  | 'DEFERRED'
  | 'REJECTED';

/**
 * CVE finding for a specific package
 * @trace REQ-SEC-CVE-003
 */
export interface CVEFinding {
  /** CVE details */
  cve: CVE;
  /** Affected package name */
  package: string;
  /** Installed version */
  installedVersion: string;
  /** Affected version range description */
  affectedRange: string;
  /** Fixed version (if available) */
  fixedVersion?: string;
  /** Severity level */
  severity: CVSSSeverity;
  /** Recommended action */
  recommendation: string;
  /** Direct or transitive dependency */
  dependencyType: 'direct' | 'transitive';
  /** Dependency path (for transitive) */
  dependencyPath?: string[];
}

/**
 * CVE search query parameters
 * @trace DES-SEC-CVE-001
 */
export interface CVESearchQuery {
  /** Search by keyword */
  keyword?: string;
  /** Search by CPE */
  cpe?: string;
  /** Filter by CWE */
  cweId?: string;
  /** Filter by minimum CVSS score */
  minCvssScore?: number;
  /** Filter by maximum CVSS score */
  maxCvssScore?: number;
  /** Filter by publication date (start) */
  publishedAfter?: Date;
  /** Filter by publication date (end) */
  publishedBefore?: Date;
  /** Filter by modification date (start) */
  modifiedAfter?: Date;
  /** Filter by modification date (end) */
  modifiedBefore?: Date;
  /** Results per page (max 2000 for NVD API) */
  resultsPerPage?: number;
  /** Start index for pagination */
  startIndex?: number;
}

/**
 * CVE database sync result
 * @trace REQ-SEC-CVE-002
 */
export interface CVESyncResult {
  /** Whether sync was performed */
  synced: boolean;
  /** Number of CVEs updated */
  updated: number;
  /** Number of new CVEs added */
  added: number;
  /** Sync strategy used */
  strategy: 'full' | 'incremental' | 'on-demand';
  /** Sync duration in milliseconds */
  duration: number;
  /** Sync timestamp */
  timestamp: Date;
  /** Error message if sync failed */
  error?: string;
}

/**
 * CVE database options
 * @trace DES-SEC-CVE-001
 */
export interface CVEDatabaseOptions {
  /** NVD API key (optional, increases rate limit) */
  apiKey?: string;
  /** Cache directory path */
  cacheDir: string;
  /** Cache TTL in hours (default: 24) */
  cacheTTL: number;
  /** Maximum cache size in MB (default: 500) */
  maxCacheSize: number;
  /** Enable automatic sync */
  autoSync: boolean;
  /** Sync interval in hours */
  syncInterval: number;
}

/**
 * npm package to CPE mapping
 * @trace DES-SEC-CVE-003
 */
export interface NpmCPEMapping {
  /** npm package name */
  npmPackage: string;
  /** CPE vendor */
  cpeVendor: string;
  /** CPE product */
  cpeProduct: string;
  /** Last update timestamp */
  updatedAt: Date;
}

/**
 * NVD API response format
 * @internal
 */
export interface NVDAPIResponse {
  resultsPerPage: number;
  startIndex: number;
  totalResults: number;
  format: string;
  version: string;
  timestamp: string;
  vulnerabilities: NVDVulnerability[];
}

/**
 * NVD vulnerability entry
 * @internal
 */
export interface NVDVulnerability {
  cve: {
    id: string;
    sourceIdentifier: string;
    published: string;
    lastModified: string;
    vulnStatus: string;
    descriptions: Array<{ lang: string; value: string }>;
    metrics?: {
      cvssMetricV31?: Array<{
        source: string;
        type: string;
        cvssData: {
          version: string;
          vectorString: string;
          baseScore: number;
          baseSeverity: string;
          attackVector: string;
          attackComplexity: string;
          privilegesRequired: string;
          userInteraction: string;
          scope: string;
          confidentialityImpact: string;
          integrityImpact: string;
          availabilityImpact: string;
        };
      }>;
    };
    weaknesses?: Array<{
      source: string;
      type: string;
      description: Array<{ lang: string; value: string }>;
    }>;
    configurations?: Array<{
      nodes: Array<{
        operator: string;
        negate: boolean;
        cpeMatch: Array<{
          vulnerable: boolean;
          criteria: string;
          versionStartIncluding?: string;
          versionStartExcluding?: string;
          versionEndIncluding?: string;
          versionEndExcluding?: string;
        }>;
      }>;
    }>;
    references?: Array<{
      url: string;
      source: string;
      tags?: string[];
    }>;
  };
}
