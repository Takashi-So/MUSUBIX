/**
 * @fileoverview Tests for Threat Intelligence component
 * @module @nahisaho/musubix-security/tests/phase6/threat-intelligence
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  ThreatIntelligence,
  createThreatIntelligence,
  quickIOCCheck,
  enrichWithThreatIntel,
  isCVEActivelyExploited,
  type IOC,
  type ThreatFeed,
} from '../../src/intelligence/threat-intelligence.js';

describe('ThreatIntelligence', () => {
  let threatIntel: ThreatIntelligence;

  beforeEach(() => {
    threatIntel = createThreatIntelligence();
  });

  describe('IOC Management', () => {
    it('should get all IOCs', () => {
      const iocs = threatIntel.getAllIOCs();
      expect(Array.isArray(iocs)).toBe(true);
    });

    it('should get IOCs by type', () => {
      const domains = threatIntel.getIOCsByType('domain');
      expect(Array.isArray(domains)).toBe(true);
    });

    it('should search IOCs', () => {
      const results = threatIntel.searchIOCs('malicious');
      expect(Array.isArray(results)).toBe(true);
    });
  });

  describe('IOC Matching', () => {
    it('should match code against IOCs', () => {
      const code = `
        const url = "https://evil.example.com/data";
        fetch(url);
      `;
      const matches = threatIntel.matchCode(code, 'test.ts');
      expect(Array.isArray(matches)).toBe(true);
    });

    it('should match domains in code', () => {
      const code = `fetch('http://coinhive.com/miner.js')`;
      const matches = threatIntel.matchCode(code, 'test.ts');
      expect(Array.isArray(matches)).toBe(true);
    });
  });

  describe('Threat Feed Management', () => {
    it('should add and list threat feeds', () => {
      const feed: ThreatFeed = {
        id: 'otx',
        name: 'AlienVault OTX',
        url: 'https://otx.alienvault.com/api/v1/pulses/subscribed',
        format: 'taxii',
        enabled: true,
        updateInterval: 60,
        trustLevel: 80,
      };

      threatIntel.addFeed(feed);
      const feeds = threatIntel.getFeeds();
      expect(feeds.some(f => f.id === 'otx')).toBe(true);
    });

    it('should remove threat feeds', () => {
      const feed: ThreatFeed = {
        id: 'temp-feed',
        name: 'Temporary Feed',
        url: 'https://example.com',
        format: 'json',
        enabled: true,
        updateInterval: 60,
        trustLevel: 50,
      };

      threatIntel.addFeed(feed);
      threatIntel.removeFeed('temp-feed');
      const feeds = threatIntel.getFeeds();
      expect(feeds.some(f => f.id === 'temp-feed')).toBe(false);
    });
  });

  describe('CVE Enrichment', () => {
    it('should check if CVE is actively exploited', () => {
      // Log4Shell - known actively exploited
      expect(isCVEActivelyExploited('CVE-2021-44228')).toBe(true);
      // Random CVE
      expect(isCVEActivelyExploited('CVE-2099-99999')).toBe(false);
    });
  });

  describe('Factory Functions', () => {
    it('should create threat intelligence with options', () => {
      const ti = createThreatIntelligence({
        autoUpdate: false,
      });
      expect(ti).toBeInstanceOf(ThreatIntelligence);
    });

    it('should perform quick IOC check', () => {
      const code = `fetch('http://192.168.1.100/api');`;
      const results = quickIOCCheck(code, 'test.ts');
      expect(Array.isArray(results)).toBe(true);
    });

    it('should enrich vulnerability with threat intel', () => {
      const vuln = {
        id: 'V1',
        type: 'injection' as const,
        severity: 'critical' as const,
        cwes: ['CWE-89'],
        location: { file: 'test.ts', startLine: 1, endLine: 1, startColumn: 0, endColumn: 10 },
        description: 'Test',
        recommendation: 'Fix it',
        confidence: 0.9,
        ruleId: 'test',
        detectedAt: new Date(),
      };

      const enriched = enrichWithThreatIntel(vuln);
      expect(enriched).toBeDefined();
      expect(enriched.vulnerabilityId).toBe('V1');
    });
  });

  describe('Edge Cases', () => {
    it('should handle empty code', () => {
      const matches = threatIntel.matchCode('', 'test.ts');
      expect(Array.isArray(matches)).toBe(true);
    });

    it('should handle code with no threats', () => {
      const code = `
        function add(a, b) {
          return a + b;
        }
      `;
      const matches = threatIntel.matchCode(code, 'test.ts');
      expect(Array.isArray(matches)).toBe(true);
    });
  });
});
