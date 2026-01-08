/**
 * @fileoverview NVD (National Vulnerability Database) API 2.0 Client
 * @module @nahisaho/musubix-security/cve/nvd-client
 * @trace REQ-CVE-001, DES-CVE-001
 */

import type {
  CVE,
  CVESearchQuery,
  CVSSScore,
  CVSSSeverity,
  CVEReference,
  CPEMatch,
  CVEStatus,
  NVDAPIResponse,
  NVDVulnerability,
} from '../types/cve.js';

/**
 * NVD API client options
 */
export interface NVDClientOptions {
  /** NVD API key (optional, increases rate limit from 5 to 50 req/30s) */
  apiKey?: string;
  /** Base URL for NVD API */
  baseUrl?: string;
  /** Request timeout in milliseconds (default: 30000) */
  timeout?: number;
  /** Maximum retry attempts (default: 3) */
  maxRetries?: number;
  /** Initial retry delay in milliseconds (default: 1000) */
  retryDelay?: number;
}

/**
 * CVE search result with pagination
 */
export interface CVESearchResult {
  /** Total number of results */
  totalResults: number;
  /** Results per page */
  resultsPerPage: number;
  /** Start index */
  startIndex: number;
  /** CVE entries */
  cves: CVE[];
  /** Response timestamp */
  timestamp: Date;
}

/**
 * NVD API error
 */
export class NVDAPIError extends Error {
  constructor(
    message: string,
    public readonly statusCode?: number,
    public readonly retryable: boolean = false
  ) {
    super(message);
    this.name = 'NVDAPIError';
  }
}

/**
 * NVD API 2.0 Client
 * @see https://nvd.nist.gov/developers/vulnerabilities
 * @trace REQ-CVE-001, DES-CVE-001
 */
export class NVDClient {
  private readonly baseUrl: string;
  private readonly apiKey?: string;
  private readonly timeout: number;
  private readonly maxRetries: number;
  private readonly retryDelay: number;

  constructor(options: NVDClientOptions = {}) {
    this.baseUrl = options.baseUrl ?? 'https://services.nvd.nist.gov/rest/json/cves/2.0';
    this.apiKey = options.apiKey ?? process.env.NVD_API_KEY;
    this.timeout = options.timeout ?? 30000;
    this.maxRetries = options.maxRetries ?? 3;
    this.retryDelay = options.retryDelay ?? 1000;
  }

  /**
   * Check if API key is configured
   */
  hasApiKey(): boolean {
    return !!this.apiKey;
  }

  /**
   * Get a single CVE by ID
   * @param cveId CVE identifier (e.g., "CVE-2021-44228")
   */
  async getCVE(cveId: string): Promise<CVE | null> {
    const normalizedId = this.normalizeCVEId(cveId);
    const url = new URL(this.baseUrl);
    url.searchParams.set('cveId', normalizedId);

    const response = await this.makeRequest(url.toString());
    
    if (response.totalResults === 0) {
      return null;
    }

    return this.transformVulnerability(response.vulnerabilities[0]);
  }

  /**
   * Search CVEs by keyword
   * @param keyword Search keyword
   * @param options Additional search options
   */
  async searchByKeyword(
    keyword: string,
    options?: CVESearchQuery
  ): Promise<CVESearchResult> {
    const url = new URL(this.baseUrl);
    url.searchParams.set('keywordSearch', keyword);
    this.applySearchOptions(url, options);

    return this.executeSearch(url);
  }

  /**
   * Search CVEs by CPE (Common Platform Enumeration)
   * @param cpe CPE 2.3 URI
   * @param options Additional search options
   */
  async searchByCPE(
    cpe: string,
    options?: CVESearchQuery
  ): Promise<CVESearchResult> {
    const url = new URL(this.baseUrl);
    url.searchParams.set('cpeName', cpe);
    this.applySearchOptions(url, options);

    return this.executeSearch(url);
  }

  /**
   * Search CVEs by CWE ID
   * @param cweId CWE identifier (e.g., "CWE-79")
   * @param options Additional search options
   */
  async searchByCWE(
    cweId: string,
    options?: CVESearchQuery
  ): Promise<CVESearchResult> {
    const url = new URL(this.baseUrl);
    // NVD API uses cweId parameter without "CWE-" prefix
    const numericCweId = cweId.replace(/^CWE-/i, '');
    url.searchParams.set('cweId', `CWE-${numericCweId}`);
    this.applySearchOptions(url, options);

    return this.executeSearch(url);
  }

  /**
   * Search CVEs by date range
   * @param startDate Start date
   * @param endDate End date
   * @param options Additional search options
   */
  async searchByDateRange(
    startDate: Date,
    endDate: Date,
    options?: CVESearchQuery
  ): Promise<CVESearchResult> {
    const url = new URL(this.baseUrl);
    url.searchParams.set('pubStartDate', this.formatDate(startDate));
    url.searchParams.set('pubEndDate', this.formatDate(endDate));
    this.applySearchOptions(url, options);

    return this.executeSearch(url);
  }

  /**
   * Search CVEs by CVSS score range
   * @param minScore Minimum CVSS score
   * @param maxScore Maximum CVSS score
   * @param options Additional search options
   */
  async searchByCVSSRange(
    minScore: number,
    maxScore: number,
    options?: CVESearchQuery
  ): Promise<CVESearchResult> {
    const url = new URL(this.baseUrl);
    url.searchParams.set('cvssV3Severity', this.getSeverityFromScore(minScore));
    this.applySearchOptions(url, options);

    // Filter results by exact score range
    const result = await this.executeSearch(url);
    result.cves = result.cves.filter(cve => {
      const score = cve.cvss?.baseScore ?? 0;
      return score >= minScore && score <= maxScore;
    });
    result.totalResults = result.cves.length;

    return result;
  }

  /**
   * Get recently modified CVEs
   * @param daysBack Number of days to look back (default: 7)
   * @param options Additional search options
   */
  async getRecentlyModified(
    daysBack: number = 7,
    options?: CVESearchQuery
  ): Promise<CVESearchResult> {
    const endDate = new Date();
    const startDate = new Date();
    startDate.setDate(startDate.getDate() - daysBack);

    const url = new URL(this.baseUrl);
    url.searchParams.set('lastModStartDate', this.formatDate(startDate));
    url.searchParams.set('lastModEndDate', this.formatDate(endDate));
    this.applySearchOptions(url, options);

    return this.executeSearch(url);
  }

  /**
   * Apply search options to URL
   */
  private applySearchOptions(url: URL, options?: CVESearchQuery): void {
    if (!options) return;

    if (options.minCvssScore !== undefined) {
      url.searchParams.set('cvssV3Severity', this.getSeverityFromScore(options.minCvssScore));
    }

    if (options.resultsPerPage !== undefined) {
      url.searchParams.set('resultsPerPage', String(Math.min(options.resultsPerPage, 2000)));
    }

    if (options.startIndex !== undefined) {
      url.searchParams.set('startIndex', String(options.startIndex));
    }

    if (options.publishedAfter) {
      url.searchParams.set('pubStartDate', this.formatDate(options.publishedAfter));
    }

    if (options.publishedBefore) {
      url.searchParams.set('pubEndDate', this.formatDate(options.publishedBefore));
    }

    if (options.modifiedAfter) {
      url.searchParams.set('lastModStartDate', this.formatDate(options.modifiedAfter));
    }

    if (options.modifiedBefore) {
      url.searchParams.set('lastModEndDate', this.formatDate(options.modifiedBefore));
    }
  }

  /**
   * Execute search and return results
   */
  private async executeSearch(url: URL): Promise<CVESearchResult> {
    const response = await this.makeRequest(url.toString());

    return {
      totalResults: response.totalResults,
      resultsPerPage: response.resultsPerPage,
      startIndex: response.startIndex,
      cves: response.vulnerabilities.map(v => this.transformVulnerability(v)),
      timestamp: new Date(response.timestamp),
    };
  }

  /**
   * Make HTTP request with retry logic
   */
  private async makeRequest(url: string): Promise<NVDAPIResponse> {
    const headers: Record<string, string> = {
      'Accept': 'application/json',
    };

    if (this.apiKey) {
      headers['apiKey'] = this.apiKey;
    }

    let lastError: Error | undefined;

    for (let attempt = 0; attempt <= this.maxRetries; attempt++) {
      try {
        const controller = new AbortController();
        const timeoutId = setTimeout(() => controller.abort(), this.timeout);

        const response = await fetch(url, {
          method: 'GET',
          headers,
          signal: controller.signal,
        });

        clearTimeout(timeoutId);

        if (!response.ok) {
          const retryable = response.status === 429 || response.status >= 500;
          throw new NVDAPIError(
            `NVD API error: ${response.status} ${response.statusText}`,
            response.status,
            retryable
          );
        }

        return await response.json() as NVDAPIResponse;
      } catch (error) {
        lastError = error instanceof Error ? error : new Error(String(error));

        // Check if error is retryable
        const isRetryable = 
          error instanceof NVDAPIError ? error.retryable :
          error instanceof Error && error.name === 'AbortError';

        if (!isRetryable || attempt === this.maxRetries) {
          throw lastError;
        }

        // Exponential backoff
        const delay = this.retryDelay * Math.pow(2, attempt);
        await this.sleep(delay);
      }
    }

    throw lastError ?? new Error('Unknown error');
  }

  /**
   * Transform NVD API response to CVE type
   */
  private transformVulnerability(vuln: NVDVulnerability): CVE {
    const cveData = vuln.cve;
    
    // Get English description
    const description = cveData.descriptions.find(d => d.lang === 'en')?.value ?? '';

    // Get CVSS v3.1 score
    let cvss: CVSSScore | undefined;
    const cvssMetric = cveData.metrics?.cvssMetricV31?.[0];
    if (cvssMetric) {
      const cvssData = cvssMetric.cvssData;
      cvss = {
        version: cvssData.version as '3.0' | '3.1',
        baseScore: cvssData.baseScore,
        severity: cvssData.baseSeverity as CVSSSeverity,
        vectorString: cvssData.vectorString,
        attackVector: cvssData.attackVector as CVSSScore['attackVector'],
        attackComplexity: cvssData.attackComplexity as CVSSScore['attackComplexity'],
        privilegesRequired: cvssData.privilegesRequired as CVSSScore['privilegesRequired'],
        userInteraction: cvssData.userInteraction as CVSSScore['userInteraction'],
        scope: cvssData.scope as CVSSScore['scope'],
        confidentialityImpact: cvssData.confidentialityImpact as CVSSScore['confidentialityImpact'],
        integrityImpact: cvssData.integrityImpact as CVSSScore['integrityImpact'],
        availabilityImpact: cvssData.availabilityImpact as CVSSScore['availabilityImpact'],
      };
    }

    // Get CWE IDs
    const cwes: string[] = [];
    if (cveData.weaknesses) {
      for (const weakness of cveData.weaknesses) {
        for (const desc of weakness.description) {
          if (desc.lang === 'en' && desc.value.startsWith('CWE-')) {
            cwes.push(desc.value);
          }
        }
      }
    }

    // Get references
    const references: CVEReference[] = (cveData.references ?? []).map(ref => ({
      url: ref.url,
      source: ref.source,
      tags: ref.tags,
    }));

    // Get affected products (CPE matches)
    const affectedProducts: CPEMatch[] = [];
    if (cveData.configurations) {
      for (const config of cveData.configurations) {
        for (const node of config.nodes) {
          for (const match of node.cpeMatch) {
            affectedProducts.push({
              cpe: match.criteria,
              vulnerable: match.vulnerable,
              versionStartIncluding: match.versionStartIncluding,
              versionStartExcluding: match.versionStartExcluding,
              versionEndIncluding: match.versionEndIncluding,
              versionEndExcluding: match.versionEndExcluding,
            });
          }
        }
      }
    }

    return {
      id: cveData.id,
      description,
      published: new Date(cveData.published),
      lastModified: new Date(cveData.lastModified),
      cvss,
      cwes,
      references,
      affectedProducts,
      status: cveData.vulnStatus as CVEStatus,
    };
  }

  /**
   * Normalize CVE ID format
   */
  private normalizeCVEId(cveId: string): string {
    const match = cveId.match(/^(?:CVE-)?(\d{4})-(\d+)$/i);
    if (!match) {
      throw new NVDAPIError(`Invalid CVE ID format: ${cveId}`);
    }
    return `CVE-${match[1]}-${match[2]}`;
  }

  /**
   * Format date for NVD API
   */
  private formatDate(date: Date): string {
    return date.toISOString();
  }

  /**
   * Get CVSS severity string from score
   */
  private getSeverityFromScore(score: number): string {
    if (score >= 9.0) return 'CRITICAL';
    if (score >= 7.0) return 'HIGH';
    if (score >= 4.0) return 'MEDIUM';
    if (score >= 0.1) return 'LOW';
    return 'NONE';
  }

  /**
   * Sleep for specified milliseconds
   */
  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }
}
