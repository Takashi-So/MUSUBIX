/**
 * @fileoverview Threat Intelligence Integration
 * @module @nahisaho/musubix-security/intelligence/threat-intelligence
 * 
 * Provides threat intelligence feed integration, IOC matching,
 * and threat context enrichment for vulnerability findings.
 */

import type { Vulnerability, SourceLocation } from '../types/index.js';

// ============================================================================
// Types
// ============================================================================

/**
 * Indicator of Compromise (IOC) type
 */
export type IOCType = 
  | 'ip-address'
  | 'domain'
  | 'url'
  | 'file-hash'
  | 'email'
  | 'cve'
  | 'malware-signature'
  | 'attack-pattern'
  | 'registry-key'
  | 'mutex'
  | 'user-agent'
  | 'custom';

/**
 * Threat severity level
 */
export type ThreatSeverity = 'critical' | 'high' | 'medium' | 'low' | 'unknown';

/**
 * Threat confidence level
 */
export type ThreatConfidence = 'confirmed' | 'high' | 'medium' | 'low' | 'unknown';

/**
 * Indicator of Compromise
 */
export interface IOC {
  /** IOC ID */
  id: string;
  /** IOC type */
  type: IOCType;
  /** IOC value */
  value: string;
  /** Threat severity */
  severity: ThreatSeverity;
  /** Confidence level */
  confidence: ThreatConfidence;
  /** First seen timestamp */
  firstSeen: Date;
  /** Last seen timestamp */
  lastSeen: Date;
  /** Source feed */
  source: string;
  /** Tags */
  tags: string[];
  /** Related threat actors */
  threatActors: string[];
  /** Related campaigns */
  campaigns: string[];
  /** MITRE ATT&CK techniques */
  techniques: string[];
  /** Description */
  description?: string;
  /** Expiration date */
  expiresAt?: Date;
  /** Additional metadata */
  metadata: Record<string, unknown>;
}

/**
 * Threat feed configuration
 */
export interface ThreatFeed {
  /** Feed ID */
  id: string;
  /** Feed name */
  name: string;
  /** Feed URL or path */
  url: string;
  /** Feed format */
  format: 'stix' | 'taxii' | 'csv' | 'json' | 'openioc' | 'custom';
  /** API key if required */
  apiKey?: string;
  /** Update interval in minutes */
  updateInterval: number;
  /** Last updated */
  lastUpdated?: Date;
  /** Enabled status */
  enabled: boolean;
  /** Trust level (0-100) */
  trustLevel: number;
  /** IOC types to fetch */
  iocTypes?: IOCType[];
}

/**
 * Threat match result
 */
export interface ThreatMatch {
  /** Match ID */
  id: string;
  /** Matched IOC */
  ioc: IOC;
  /** Match context */
  context: {
    /** Where the match was found */
    location: SourceLocation;
    /** Code snippet */
    codeSnippet: string;
    /** Match type */
    matchType: 'exact' | 'partial' | 'pattern';
    /** Match confidence (0-1) */
    confidence: number;
  };
  /** Related vulnerability if any */
  vulnerabilityId?: string;
  /** Match timestamp */
  matchedAt: Date;
  /** Recommended actions */
  recommendations: string[];
}

/**
 * Threat context enrichment
 */
export interface ThreatContext {
  /** Vulnerability ID */
  vulnerabilityId: string;
  /** Related threats */
  threats: ThreatInfo[];
  /** Risk multiplier based on threat intelligence */
  riskMultiplier: number;
  /** Is actively exploited */
  activelyExploited: boolean;
  /** Known exploit kits */
  exploitKits: string[];
  /** Affected industries */
  targetedIndustries: string[];
  /** Geographic targeting */
  geographicTargets: string[];
  /** Time to patch recommendation */
  urgency: 'immediate' | 'high' | 'medium' | 'low';
}

/**
 * Threat information
 */
export interface ThreatInfo {
  /** Threat ID */
  id: string;
  /** Threat name */
  name: string;
  /** Threat type */
  type: 'apt' | 'cybercrime' | 'hacktivism' | 'insider' | 'unknown';
  /** Associated CVEs */
  cves: string[];
  /** MITRE ATT&CK mapping */
  mitreTechniques: string[];
  /** Confidence */
  confidence: ThreatConfidence;
}

/**
 * Threat Intelligence options
 */
export interface ThreatIntelligenceOptions {
  /** Enabled feeds */
  feeds?: ThreatFeed[];
  /** Cache TTL in minutes */
  cacheTTL?: number;
  /** Enable auto-update */
  autoUpdate?: boolean;
  /** Update interval in minutes */
  updateInterval?: number;
  /** Match threshold (0-1) */
  matchThreshold?: number;
  /** Enable CVE enrichment */
  enableCVEEnrichment?: boolean;
  /** Enable MITRE ATT&CK mapping */
  enableMitreMapping?: boolean;
}

// ============================================================================
// Built-in IOC Patterns
// ============================================================================

const BUILTIN_IOC_PATTERNS: IOC[] = [
  // Known malicious patterns in code
  {
    id: 'IOC-CRYPTO-MINER-001',
    type: 'malware-signature',
    value: 'coinhive.min.js',
    severity: 'high',
    confidence: 'confirmed',
    firstSeen: new Date('2017-09-01'),
    lastSeen: new Date(),
    source: 'builtin',
    tags: ['cryptominer', 'malware', 'javascript'],
    threatActors: [],
    campaigns: ['Cryptojacking'],
    techniques: ['T1496'],
    description: 'Coinhive cryptocurrency miner script',
    metadata: {},
  },
  {
    id: 'IOC-WEBSHELL-001',
    type: 'malware-signature',
    value: 'c99shell',
    severity: 'critical',
    confidence: 'confirmed',
    firstSeen: new Date('2010-01-01'),
    lastSeen: new Date(),
    source: 'builtin',
    tags: ['webshell', 'backdoor', 'php'],
    threatActors: [],
    campaigns: [],
    techniques: ['T1505.003'],
    description: 'C99 PHP webshell',
    metadata: {},
  },
  {
    id: 'IOC-WEBSHELL-002',
    type: 'malware-signature',
    value: 'r57shell',
    severity: 'critical',
    confidence: 'confirmed',
    firstSeen: new Date('2008-01-01'),
    lastSeen: new Date(),
    source: 'builtin',
    tags: ['webshell', 'backdoor', 'php'],
    threatActors: [],
    campaigns: [],
    techniques: ['T1505.003'],
    description: 'R57 PHP webshell',
    metadata: {},
  },
  {
    id: 'IOC-MALICIOUS-IP-PATTERN-001',
    type: 'attack-pattern',
    value: '0\\.0\\.0\\.0|127\\.0\\.0\\.1.*bind',
    severity: 'medium',
    confidence: 'medium',
    firstSeen: new Date('2020-01-01'),
    lastSeen: new Date(),
    source: 'builtin',
    tags: ['bind-shell', 'reverse-shell'],
    threatActors: [],
    campaigns: [],
    techniques: ['T1059'],
    description: 'Potential bind shell pattern',
    metadata: { isRegex: true },
  },
  {
    id: 'IOC-EXFIL-001',
    type: 'attack-pattern',
    value: 'base64.*\\|.*curl|wget.*base64',
    severity: 'high',
    confidence: 'medium',
    firstSeen: new Date('2019-01-01'),
    lastSeen: new Date(),
    source: 'builtin',
    tags: ['data-exfiltration', 'encoding'],
    threatActors: [],
    campaigns: [],
    techniques: ['T1041', 'T1132'],
    description: 'Base64 encoded data exfiltration pattern',
    metadata: { isRegex: true },
  },
];

// Known malicious domains (sample)
const MALICIOUS_DOMAINS = [
  'evil.com',
  'malware.net',
  'phishing-site.com',
  'cryptominer.xyz',
];

// Known vulnerable CVEs with active exploits
const ACTIVELY_EXPLOITED_CVES = new Set([
  'CVE-2021-44228', // Log4Shell
  'CVE-2021-26855', // ProxyLogon
  'CVE-2021-34527', // PrintNightmare
  'CVE-2021-27065', // Exchange
  'CVE-2020-1472',  // Zerologon
  'CVE-2019-19781', // Citrix ADC
  'CVE-2019-11510', // Pulse Secure
  'CVE-2018-13379', // FortiOS
  'CVE-2017-11882', // Equation Editor
  'CVE-2017-0144',  // EternalBlue
]);

// ============================================================================
// ThreatIntelligence Class
// ============================================================================

/**
 * Threat Intelligence service for IOC matching and threat enrichment
 */
export class ThreatIntelligence {
  private options: Required<ThreatIntelligenceOptions>;
  private feeds: Map<string, ThreatFeed> = new Map();
  private iocCache: Map<string, IOC> = new Map();
  private lastUpdate: Date = new Date(0);
  private updateTimer?: ReturnType<typeof setInterval>;

  constructor(options: ThreatIntelligenceOptions = {}) {
    this.options = {
      feeds: options.feeds ?? [],
      cacheTTL: options.cacheTTL ?? 60,
      autoUpdate: options.autoUpdate ?? false,
      updateInterval: options.updateInterval ?? 60,
      matchThreshold: options.matchThreshold ?? 0.7,
      enableCVEEnrichment: options.enableCVEEnrichment ?? true,
      enableMitreMapping: options.enableMitreMapping ?? true,
    };

    // Load built-in IOCs
    this.loadBuiltinIOCs();

    // Load configured feeds
    for (const feed of this.options.feeds) {
      this.feeds.set(feed.id, feed);
    }

    // Start auto-update if enabled
    if (this.options.autoUpdate) {
      this.startAutoUpdate();
    }
  }

  /**
   * Load built-in IOCs
   */
  private loadBuiltinIOCs(): void {
    for (const ioc of BUILTIN_IOC_PATTERNS) {
      this.iocCache.set(ioc.id, ioc);
    }

    // Add malicious domains
    for (const domain of MALICIOUS_DOMAINS) {
      const ioc: IOC = {
        id: `IOC-DOMAIN-${domain.replace(/\./g, '-').toUpperCase()}`,
        type: 'domain',
        value: domain,
        severity: 'high',
        confidence: 'high',
        firstSeen: new Date('2020-01-01'),
        lastSeen: new Date(),
        source: 'builtin',
        tags: ['malicious', 'domain'],
        threatActors: [],
        campaigns: [],
        techniques: [],
        metadata: {},
      };
      this.iocCache.set(ioc.id, ioc);
    }
  }

  /**
   * Start auto-update timer
   */
  private startAutoUpdate(): void {
    this.updateTimer = setInterval(
      () => this.updateFeeds(),
      this.options.updateInterval * 60 * 1000
    );
  }

  /**
   * Stop auto-update timer
   */
  stopAutoUpdate(): void {
    if (this.updateTimer) {
      clearInterval(this.updateTimer);
      this.updateTimer = undefined;
    }
  }

  /**
   * Add a threat feed
   */
  addFeed(feed: ThreatFeed): void {
    this.feeds.set(feed.id, feed);
  }

  /**
   * Remove a threat feed
   */
  removeFeed(feedId: string): boolean {
    return this.feeds.delete(feedId);
  }

  /**
   * Get all configured feeds
   */
  getFeeds(): ThreatFeed[] {
    return Array.from(this.feeds.values());
  }

  /**
   * Update all feeds
   */
  async updateFeeds(): Promise<{ updated: number; failed: number }> {
    let updated = 0;
    let failed = 0;

    for (const feed of this.feeds.values()) {
      if (!feed.enabled) continue;

      try {
        await this.updateFeed(feed);
        updated++;
      } catch {
        failed++;
      }
    }

    this.lastUpdate = new Date();
    return { updated, failed };
  }

  /**
   * Update a single feed
   */
  private async updateFeed(feed: ThreatFeed): Promise<void> {
    // In a real implementation, this would fetch from the feed URL
    // For now, we simulate the update
    feed.lastUpdated = new Date();
  }

  /**
   * Add an IOC
   */
  addIOC(ioc: IOC): void {
    this.iocCache.set(ioc.id, ioc);
  }

  /**
   * Get an IOC by ID
   */
  getIOC(id: string): IOC | undefined {
    return this.iocCache.get(id);
  }

  /**
   * Get all IOCs
   */
  getAllIOCs(): IOC[] {
    return Array.from(this.iocCache.values());
  }

  /**
   * Get IOCs by type
   */
  getIOCsByType(type: IOCType): IOC[] {
    return this.getAllIOCs().filter(ioc => ioc.type === type);
  }

  /**
   * Search IOCs
   */
  searchIOCs(query: string): IOC[] {
    const lowerQuery = query.toLowerCase();
    return this.getAllIOCs().filter(ioc =>
      ioc.value.toLowerCase().includes(lowerQuery) ||
      ioc.tags.some(tag => tag.toLowerCase().includes(lowerQuery)) ||
      ioc.description?.toLowerCase().includes(lowerQuery)
    );
  }

  /**
   * Match code against IOCs
   */
  matchCode(code: string, filePath: string): ThreatMatch[] {
    const matches: ThreatMatch[] = [];
    const lines = code.split('\n');

    for (const ioc of this.iocCache.values()) {
      // Skip expired IOCs
      if (ioc.expiresAt && ioc.expiresAt < new Date()) continue;

      const isRegex = ioc.metadata.isRegex === true;
      
      for (let lineNum = 0; lineNum < lines.length; lineNum++) {
        const line = lines[lineNum];
        let matched = false;
        let matchType: 'exact' | 'partial' | 'pattern' = 'exact';
        let confidence = 1.0;

        if (isRegex) {
          try {
            const regex = new RegExp(ioc.value, 'i');
            matched = regex.test(line);
            matchType = 'pattern';
            confidence = 0.8;
          } catch {
            // Invalid regex, skip
            continue;
          }
        } else if (ioc.type === 'domain') {
          // Domain matching
          matched = line.toLowerCase().includes(ioc.value.toLowerCase());
          matchType = 'partial';
          confidence = 0.9;
        } else {
          // Exact match
          matched = line.includes(ioc.value);
          matchType = 'exact';
          confidence = 1.0;
        }

        if (matched && confidence >= this.options.matchThreshold) {
          matches.push({
            id: `MATCH-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
            ioc,
            context: {
              location: {
                file: filePath,
                startLine: lineNum + 1,
                endLine: lineNum + 1,
                startColumn: 0,
                endColumn: line.length,
              },
              codeSnippet: line.trim(),
              matchType,
              confidence,
            },
            matchedAt: new Date(),
            recommendations: this.generateRecommendations(ioc),
          });
        }
      }
    }

    return matches;
  }

  /**
   * Generate recommendations for an IOC match
   */
  private generateRecommendations(ioc: IOC): string[] {
    const recommendations: string[] = [];

    switch (ioc.type) {
      case 'malware-signature':
        recommendations.push('Remove or quarantine the affected file immediately');
        recommendations.push('Scan the entire codebase for related signatures');
        recommendations.push('Review recent commits for the introduction point');
        break;
      case 'domain':
        recommendations.push('Block the domain at network level');
        recommendations.push('Remove all references to this domain');
        recommendations.push('Check for data exfiltration attempts');
        break;
      case 'attack-pattern':
        recommendations.push('Review the code for malicious intent');
        recommendations.push('Check if this is a false positive');
        recommendations.push('Implement input validation if user-controlled');
        break;
      case 'cve':
        recommendations.push('Update the affected dependency');
        recommendations.push('Apply available patches');
        recommendations.push('Implement compensating controls if patch unavailable');
        break;
      default:
        recommendations.push('Investigate the finding');
        recommendations.push('Consult security team');
    }

    if (ioc.severity === 'critical') {
      recommendations.unshift('CRITICAL: Immediate action required');
    }

    return recommendations;
  }

  /**
   * Enrich vulnerability with threat context
   */
  enrichVulnerability(vulnerability: Vulnerability): ThreatContext {
    const threats: ThreatInfo[] = [];
    let riskMultiplier = 1.0;
    let activelyExploited = false;
    const exploitKits: string[] = [];
    const targetedIndustries: string[] = [];
    const geographicTargets: string[] = [];

    // Check for CVE references
    if (this.options.enableCVEEnrichment) {
      for (const cwe of vulnerability.cwes) {
        // Check if any related CVE is actively exploited
        // In a real implementation, this would query a CVE database
        const relatedCVEs = this.getRelatedCVEs(cwe);
        for (const cve of relatedCVEs) {
          if (ACTIVELY_EXPLOITED_CVES.has(cve)) {
            activelyExploited = true;
            riskMultiplier = Math.max(riskMultiplier, 2.0);
            exploitKits.push('Public exploit available');
          }
        }
      }
    }

    // Map to MITRE ATT&CK
    if (this.options.enableMitreMapping) {
      const techniques = this.mapToMitre(vulnerability.type);
      if (techniques.length > 0) {
        threats.push({
          id: `THREAT-${vulnerability.id}`,
          name: `${vulnerability.type} attack vector`,
          type: 'unknown',
          cves: [],
          mitreTechniques: techniques,
          confidence: 'medium',
        });
      }
    }

    // Adjust risk based on severity
    if (vulnerability.severity === 'critical') {
      riskMultiplier *= 1.5;
    } else if (vulnerability.severity === 'high') {
      riskMultiplier *= 1.25;
    }

    // Check IOC matches in the vulnerability location
    const iocMatches = this.iocCache.size > 0;
    if (iocMatches && vulnerability.codeSnippet) {
      const matches = this.matchCode(vulnerability.codeSnippet, vulnerability.location.file);
      if (matches.length > 0) {
        riskMultiplier *= 1.5;
        for (const match of matches) {
          threats.push({
            id: match.id,
            name: match.ioc.description || match.ioc.value,
            type: 'unknown',
            cves: [],
            mitreTechniques: match.ioc.techniques,
            confidence: match.context.confidence >= 0.9 ? 'high' : 'medium',
          });
        }
      }
    }

    // Determine urgency
    let urgency: ThreatContext['urgency'];
    if (activelyExploited || vulnerability.severity === 'critical') {
      urgency = 'immediate';
    } else if (vulnerability.severity === 'high' || riskMultiplier > 1.5) {
      urgency = 'high';
    } else if (vulnerability.severity === 'medium') {
      urgency = 'medium';
    } else {
      urgency = 'low';
    }

    return {
      vulnerabilityId: vulnerability.id,
      threats,
      riskMultiplier,
      activelyExploited,
      exploitKits,
      targetedIndustries,
      geographicTargets,
      urgency,
    };
  }

  /**
   * Get related CVEs for a CWE
   */
  private getRelatedCVEs(cwe: string): string[] {
    // In a real implementation, this would query a CVE database
    // For now, return sample data based on common CWE-CVE mappings
    const cweCveMap: Record<string, string[]> = {
      'CWE-79': ['CVE-2021-41773', 'CVE-2020-11022'], // XSS
      'CWE-89': ['CVE-2021-27065', 'CVE-2019-2725'], // SQL Injection
      'CWE-94': ['CVE-2021-44228', 'CVE-2021-45046'], // Code Injection (Log4j)
      'CWE-22': ['CVE-2021-41773', 'CVE-2021-42013'], // Path Traversal
      'CWE-287': ['CVE-2021-26855', 'CVE-2020-1472'], // Auth Bypass
    };

    return cweCveMap[cwe] || [];
  }

  /**
   * Map vulnerability type to MITRE ATT&CK techniques
   */
  private mapToMitre(vulnerabilityType: string): string[] {
    const mitreMap: Record<string, string[]> = {
      'xss': ['T1059.007', 'T1185'], // JavaScript, Browser Session Hijacking
      'sql-injection': ['T1190', 'T1505'], // Exploit Public-Facing App, Server Software
      'command-injection': ['T1059', 'T1203'], // Command Execution
      'path-traversal': ['T1083', 'T1005'], // File Discovery, Data from Local System
      'ssrf': ['T1090', 'T1071'], // Proxy, Application Layer Protocol
      'xxe': ['T1005', 'T1083'], // Data from Local System
      'deserialization': ['T1059', 'T1055'], // Command Execution, Process Injection
      'hardcoded-secret': ['T1552.001', 'T1078'], // Credentials in Files, Valid Accounts
      'weak-crypto': ['T1600', 'T1040'], // Weaken Encryption, Network Sniffing
      'insecure-auth': ['T1078', 'T1110'], // Valid Accounts, Brute Force
    };

    return mitreMap[vulnerabilityType] || [];
  }

  /**
   * Check if a CVE is actively exploited
   */
  isActivelyExploited(cve: string): boolean {
    return ACTIVELY_EXPLOITED_CVES.has(cve);
  }

  /**
   * Get threat statistics
   */
  getStatistics(): {
    totalIOCs: number;
    byType: Record<IOCType, number>;
    bySeverity: Record<ThreatSeverity, number>;
    feedsActive: number;
    lastUpdate: Date;
  } {
    const byType: Record<IOCType, number> = {} as Record<IOCType, number>;
    const bySeverity: Record<ThreatSeverity, number> = {} as Record<ThreatSeverity, number>;

    for (const ioc of this.iocCache.values()) {
      byType[ioc.type] = (byType[ioc.type] || 0) + 1;
      bySeverity[ioc.severity] = (bySeverity[ioc.severity] || 0) + 1;
    }

    return {
      totalIOCs: this.iocCache.size,
      byType,
      bySeverity,
      feedsActive: Array.from(this.feeds.values()).filter(f => f.enabled).length,
      lastUpdate: this.lastUpdate,
    };
  }

  /**
   * Export IOCs
   */
  exportIOCs(format: 'json' | 'csv' | 'stix'): string {
    const iocs = this.getAllIOCs();

    switch (format) {
      case 'json':
        return JSON.stringify(iocs, null, 2);

      case 'csv': {
        const headers = ['id', 'type', 'value', 'severity', 'confidence', 'source', 'tags'];
        const rows = iocs.map(ioc => [
          ioc.id,
          ioc.type,
          ioc.value,
          ioc.severity,
          ioc.confidence,
          ioc.source,
          ioc.tags.join(';'),
        ]);
        return [headers.join(','), ...rows.map(r => r.join(','))].join('\n');
      }

      case 'stix': {
        // Simplified STIX 2.1 format
        const stixBundle = {
          type: 'bundle',
          id: `bundle--${Date.now()}`,
          objects: iocs.map(ioc => ({
            type: 'indicator',
            id: `indicator--${ioc.id}`,
            created: ioc.firstSeen.toISOString(),
            modified: ioc.lastSeen.toISOString(),
            name: ioc.description || ioc.value,
            pattern: `[${ioc.type}:value = '${ioc.value}']`,
            pattern_type: 'stix',
            valid_from: ioc.firstSeen.toISOString(),
            labels: ioc.tags,
          })),
        };
        return JSON.stringify(stixBundle, null, 2);
      }

      default:
        return JSON.stringify(iocs, null, 2);
    }
  }

  /**
   * Import IOCs
   */
  importIOCs(data: string, format: 'json' | 'csv'): number {
    let imported = 0;

    try {
      if (format === 'json') {
        const iocs = JSON.parse(data) as IOC[];
        for (const ioc of iocs) {
          if (ioc.id && ioc.type && ioc.value) {
            this.iocCache.set(ioc.id, {
              ...ioc,
              firstSeen: new Date(ioc.firstSeen),
              lastSeen: new Date(ioc.lastSeen),
              expiresAt: ioc.expiresAt ? new Date(ioc.expiresAt) : undefined,
            });
            imported++;
          }
        }
      } else if (format === 'csv') {
        const lines = data.split('\n');
        const headers = lines[0].split(',');

        for (let i = 1; i < lines.length; i++) {
          const values = lines[i].split(',');
          if (values.length >= headers.length) {
            const ioc: IOC = {
              id: values[0],
              type: values[1] as IOCType,
              value: values[2],
              severity: (values[3] || 'unknown') as ThreatSeverity,
              confidence: (values[4] || 'unknown') as ThreatConfidence,
              source: values[5] || 'import',
              tags: values[6]?.split(';') || [],
              firstSeen: new Date(),
              lastSeen: new Date(),
              threatActors: [],
              campaigns: [],
              techniques: [],
              metadata: {},
            };
            this.iocCache.set(ioc.id, ioc);
            imported++;
          }
        }
      }
    } catch {
      // Import failed
    }

    return imported;
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create a ThreatIntelligence instance
 */
export function createThreatIntelligence(
  options?: ThreatIntelligenceOptions
): ThreatIntelligence {
  return new ThreatIntelligence(options);
}

/**
 * Quick IOC check
 */
export function quickIOCCheck(
  code: string,
  filePath: string
): ThreatMatch[] {
  const ti = createThreatIntelligence();
  return ti.matchCode(code, filePath);
}

/**
 * Quick vulnerability enrichment
 */
export function enrichWithThreatIntel(
  vulnerability: Vulnerability
): ThreatContext {
  const ti = createThreatIntelligence();
  return ti.enrichVulnerability(vulnerability);
}

/**
 * Check if CVE is actively exploited
 */
export function isCVEActivelyExploited(cve: string): boolean {
  return ACTIVELY_EXPLOITED_CVES.has(cve);
}
