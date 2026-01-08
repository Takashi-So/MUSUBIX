/**
 * @fileoverview NVD Client unit tests
 * @trace TSK-CVE-001
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { NVDClient, NVDAPIError } from '../../src/cve/nvd-client.js';

// Mock fetch
const mockFetch = vi.fn();
global.fetch = mockFetch;

describe('NVDClient', () => {
  let client: NVDClient;

  beforeEach(() => {
    vi.clearAllMocks();
    client = new NVDClient({
      timeout: 5000,
      maxRetries: 1,
    });
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('constructor', () => {
    it('should use default options', () => {
      const defaultClient = new NVDClient();
      expect(defaultClient.hasApiKey()).toBe(false);
    });

    it('should accept custom API key', () => {
      const clientWithKey = new NVDClient({ apiKey: 'test-key' });
      expect(clientWithKey.hasApiKey()).toBe(true);
    });

    it('should read API key from environment', () => {
      const originalEnv = process.env.NVD_API_KEY;
      process.env.NVD_API_KEY = 'env-api-key';
      
      const envClient = new NVDClient();
      expect(envClient.hasApiKey()).toBe(true);
      
      process.env.NVD_API_KEY = originalEnv;
    });
  });

  describe('getCVE', () => {
    it('should fetch a single CVE by ID', async () => {
      const mockResponse = createMockNVDResponse([
        createMockVulnerability('CVE-2021-44228', 10.0, 'CRITICAL'),
      ]);

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(mockResponse),
      });

      const result = await client.getCVE('CVE-2021-44228');

      expect(result).not.toBeNull();
      expect(result?.id).toBe('CVE-2021-44228');
      expect(result?.cvss?.baseScore).toBe(10.0);
      expect(result?.cvss?.severity).toBe('CRITICAL');
    });

    it('should return null for non-existent CVE', async () => {
      const mockResponse = createMockNVDResponse([]);

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(mockResponse),
      });

      const result = await client.getCVE('CVE-9999-99999');
      expect(result).toBeNull();
    });

    it('should normalize CVE ID format', async () => {
      const mockResponse = createMockNVDResponse([
        createMockVulnerability('CVE-2021-44228', 10.0, 'CRITICAL'),
      ]);

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(mockResponse),
      });

      await client.getCVE('2021-44228');

      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('cveId=CVE-2021-44228'),
        expect.any(Object)
      );
    });

    it('should throw NVDAPIError for invalid CVE ID format', async () => {
      await expect(client.getCVE('invalid-id')).rejects.toThrow(NVDAPIError);
    });
  });

  describe('searchByKeyword', () => {
    it('should search CVEs by keyword', async () => {
      const mockResponse = createMockNVDResponse([
        createMockVulnerability('CVE-2021-44228', 10.0, 'CRITICAL'),
        createMockVulnerability('CVE-2021-45046', 9.0, 'CRITICAL'),
      ]);

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(mockResponse),
      });

      const result = await client.searchByKeyword('log4j');

      expect(result.cves).toHaveLength(2);
      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('keywordSearch=log4j'),
        expect.any(Object)
      );
    });

    it('should apply search options', async () => {
      const mockResponse = createMockNVDResponse([]);

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(mockResponse),
      });

      await client.searchByKeyword('test', {
        resultsPerPage: 100,
        startIndex: 50,
      });

      const url = mockFetch.mock.calls[0][0] as string;
      expect(url).toContain('resultsPerPage=100');
      expect(url).toContain('startIndex=50');
    });
  });

  describe('searchByCPE', () => {
    it('should search CVEs by CPE', async () => {
      const mockResponse = createMockNVDResponse([
        createMockVulnerability('CVE-2020-11022', 6.1, 'MEDIUM'),
      ]);

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(mockResponse),
      });

      const cpe = 'cpe:2.3:a:jquery:jquery:3.4.1:*:*:*:*:*:*:*';
      const result = await client.searchByCPE(cpe);

      expect(result.cves).toHaveLength(1);
      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining(`cpeName=${encodeURIComponent(cpe)}`),
        expect.any(Object)
      );
    });
  });

  describe('searchByCWE', () => {
    it('should search CVEs by CWE ID', async () => {
      const mockResponse = createMockNVDResponse([
        createMockVulnerability('CVE-2022-22965', 9.8, 'CRITICAL'),
      ]);

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(mockResponse),
      });

      const result = await client.searchByCWE('CWE-94');

      expect(result.cves).toHaveLength(1);
      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('cweId=CWE-94'),
        expect.any(Object)
      );
    });

    it('should normalize CWE ID format', async () => {
      const mockResponse = createMockNVDResponse([]);

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(mockResponse),
      });

      await client.searchByCWE('79');

      expect(mockFetch).toHaveBeenCalledWith(
        expect.stringContaining('cweId=CWE-79'),
        expect.any(Object)
      );
    });
  });

  describe('searchByDateRange', () => {
    it('should search CVEs by date range', async () => {
      const mockResponse = createMockNVDResponse([]);

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(mockResponse),
      });

      const startDate = new Date('2024-01-01');
      const endDate = new Date('2024-12-31');

      await client.searchByDateRange(startDate, endDate);

      const url = mockFetch.mock.calls[0][0] as string;
      expect(url).toContain('pubStartDate=');
      expect(url).toContain('pubEndDate=');
    });
  });

  describe('error handling', () => {
    it('should retry on 5xx errors', async () => {
      mockFetch
        .mockResolvedValueOnce({
          ok: false,
          status: 503,
          statusText: 'Service Unavailable',
        })
        .mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve(createMockNVDResponse([])),
        });

      const result = await client.searchByKeyword('test');

      expect(mockFetch).toHaveBeenCalledTimes(2);
      expect(result.cves).toHaveLength(0);
    });

    it('should retry on rate limit (429)', async () => {
      mockFetch
        .mockResolvedValueOnce({
          ok: false,
          status: 429,
          statusText: 'Too Many Requests',
        })
        .mockResolvedValueOnce({
          ok: true,
          json: () => Promise.resolve(createMockNVDResponse([])),
        });

      const result = await client.searchByKeyword('test');

      expect(mockFetch).toHaveBeenCalledTimes(2);
      expect(result.cves).toHaveLength(0);
    });

    it('should throw after max retries', async () => {
      mockFetch.mockResolvedValue({
        ok: false,
        status: 503,
        statusText: 'Service Unavailable',
      });

      await expect(client.searchByKeyword('test')).rejects.toThrow(NVDAPIError);
      expect(mockFetch).toHaveBeenCalledTimes(2); // initial + 1 retry
    });

    it('should not retry on 4xx errors (except 429)', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 400,
        statusText: 'Bad Request',
      });

      await expect(client.searchByKeyword('test')).rejects.toThrow(NVDAPIError);
      expect(mockFetch).toHaveBeenCalledTimes(1);
    });
  });

  describe('API key handling', () => {
    it('should include API key in headers when provided', async () => {
      const clientWithKey = new NVDClient({
        apiKey: 'test-api-key',
        timeout: 5000,
        maxRetries: 0,
      });

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(createMockNVDResponse([])),
      });

      await clientWithKey.searchByKeyword('test');

      expect(mockFetch).toHaveBeenCalledWith(
        expect.any(String),
        expect.objectContaining({
          headers: expect.objectContaining({
            apiKey: 'test-api-key',
          }),
        })
      );
    });

    it('should not include API key header when not provided', async () => {
      // Clear environment variable for this test
      const originalEnv = process.env.NVD_API_KEY;
      delete process.env.NVD_API_KEY;

      const noKeyClient = new NVDClient({
        timeout: 5000,
        maxRetries: 0,
      });

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(createMockNVDResponse([])),
      });

      await noKeyClient.searchByKeyword('test');

      const headers = mockFetch.mock.calls[0][1].headers as Record<string, string>;
      expect(headers.apiKey).toBeUndefined();

      // Restore environment variable
      if (originalEnv !== undefined) {
        process.env.NVD_API_KEY = originalEnv;
      }
    });
  });

  describe('data transformation', () => {
    it('should correctly transform NVD response to CVE type', async () => {
      const mockResponse = createMockNVDResponse([
        createMockVulnerability('CVE-2021-44228', 10.0, 'CRITICAL', {
          cwes: ['CWE-502', 'CWE-400'],
          references: [
            { url: 'https://example.com/advisory', source: 'MISC', tags: ['Vendor Advisory'] },
          ],
          cpeMatches: [
            {
              cpe: 'cpe:2.3:a:apache:log4j:*:*:*:*:*:*:*:*',
              vulnerable: true,
              versionStartIncluding: '2.0',
              versionEndExcluding: '2.17.0',
            },
          ],
        }),
      ]);

      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: () => Promise.resolve(mockResponse),
      });

      const result = await client.getCVE('CVE-2021-44228');

      expect(result).not.toBeNull();
      expect(result?.id).toBe('CVE-2021-44228');
      expect(result?.cwes).toContain('CWE-502');
      expect(result?.cwes).toContain('CWE-400');
      expect(result?.references).toHaveLength(1);
      expect(result?.references[0].url).toBe('https://example.com/advisory');
      expect(result?.affectedProducts).toHaveLength(1);
      expect(result?.affectedProducts[0].versionStartIncluding).toBe('2.0');
      expect(result?.affectedProducts[0].versionEndExcluding).toBe('2.17.0');
    });
  });
});

// Helper functions for creating mock data

function createMockNVDResponse(vulnerabilities: ReturnType<typeof createMockVulnerability>[]) {
  return {
    resultsPerPage: vulnerabilities.length,
    startIndex: 0,
    totalResults: vulnerabilities.length,
    format: 'NVD_CVE',
    version: '2.0',
    timestamp: new Date().toISOString(),
    vulnerabilities: vulnerabilities.map(v => ({ cve: v })),
  };
}

function createMockVulnerability(
  id: string,
  baseScore: number,
  severity: string,
  options: {
    cwes?: string[];
    references?: Array<{ url: string; source: string; tags?: string[] }>;
    cpeMatches?: Array<{
      cpe: string;
      vulnerable: boolean;
      versionStartIncluding?: string;
      versionStartExcluding?: string;
      versionEndIncluding?: string;
      versionEndExcluding?: string;
    }>;
  } = {}
) {
  return {
    id,
    sourceIdentifier: 'nvd@nist.gov',
    published: '2021-12-10T10:15:00.000',
    lastModified: '2024-01-01T00:00:00.000',
    vulnStatus: 'ANALYZED',
    descriptions: [
      { lang: 'en', value: `Test vulnerability ${id}` },
    ],
    metrics: {
      cvssMetricV31: [
        {
          source: 'nvd@nist.gov',
          type: 'Primary',
          cvssData: {
            version: '3.1',
            vectorString: 'CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:C/C:H/I:H/A:H',
            baseScore,
            baseSeverity: severity,
            attackVector: 'NETWORK',
            attackComplexity: 'LOW',
            privilegesRequired: 'NONE',
            userInteraction: 'NONE',
            scope: 'CHANGED',
            confidentialityImpact: 'HIGH',
            integrityImpact: 'HIGH',
            availabilityImpact: 'HIGH',
          },
        },
      ],
    },
    weaknesses: options.cwes
      ? [
          {
            source: 'nvd@nist.gov',
            type: 'Primary',
            description: options.cwes.map(cwe => ({ lang: 'en', value: cwe })),
          },
        ]
      : [],
    configurations: options.cpeMatches
      ? [
          {
            nodes: [
              {
                operator: 'OR',
                negate: false,
                cpeMatch: options.cpeMatches.map(m => ({
                  vulnerable: m.vulnerable,
                  criteria: m.cpe,
                  versionStartIncluding: m.versionStartIncluding,
                  versionStartExcluding: m.versionStartExcluding,
                  versionEndIncluding: m.versionEndIncluding,
                  versionEndExcluding: m.versionEndExcluding,
                })),
              },
            ],
          },
        ]
      : [],
    references: options.references ?? [],
  };
}
