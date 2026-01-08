/**
 * @fileoverview CPE Matcher Unit Tests
 * @module @nahisaho/musubix-security/tests/cve/cpe-matcher.test
 */

import { describe, it, expect } from 'vitest';
import {
  CPEMatcher,
  createCPESearchQuery,
  extractPackageFromCPE,
} from '../../src/cve/cpe-matcher.js';
import type { CPEMatch, VersionRange } from '../../src/cve/cpe-matcher.js';

describe('CPEMatcher', () => {
  describe('generateCPE', () => {
    it('should generate valid CPE for simple package', () => {
      const matcher = new CPEMatcher();
      const cpe = matcher.generateCPE('lodash', '4.17.21');
      
      expect(cpe).toBe('cpe:2.3:a:lodash:lodash:4.17.21:*:*:*:*:node.js:*:*');
    });

    it('should use vendor mapping for known packages', () => {
      const matcher = new CPEMatcher();
      const cpe = matcher.generateCPE('express', '4.18.2');
      
      expect(cpe).toContain(':expressjs:');
    });

    it('should handle scoped packages', () => {
      const matcher = new CPEMatcher();
      const cpe = matcher.generateCPE('@angular/core', '15.0.0');
      
      expect(cpe).toBe('cpe:2.3:a:angular:core:15.0.0:*:*:*:*:node.js:*:*');
    });

    it('should normalize package names with special characters', () => {
      const matcher = new CPEMatcher();
      const cpe = matcher.generateCPE('node-fetch', '3.0.0');
      
      expect(cpe).toContain(':node_fetch:');
    });

    it('should strip version prefix', () => {
      const matcher = new CPEMatcher();
      const cpe = matcher.generateCPE('test-pkg', 'v1.2.3');
      
      expect(cpe).toContain(':1.2.3:');
    });
  });

  describe('packageToCPEComponents', () => {
    it('should return correct components', () => {
      const matcher = new CPEMatcher();
      const components = matcher.packageToCPEComponents('express', '4.18.2');
      
      expect(components.part).toBe('a');
      expect(components.vendor).toBe('expressjs');
      expect(components.product).toBe('express');
      expect(components.version).toBe('4.18.2');
      expect(components.targetSw).toBe('node.js');
    });
  });

  describe('parseURI', () => {
    it('should parse valid CPE URI', () => {
      const matcher = new CPEMatcher();
      const parsed = matcher.parseURI('cpe:2.3:a:expressjs:express:4.18.2:*:*:*:*:node.js:*:*');
      
      expect(parsed).not.toBeNull();
      expect(parsed!.part).toBe('a');
      expect(parsed!.vendor).toBe('expressjs');
      expect(parsed!.product).toBe('express');
      expect(parsed!.version).toBe('4.18.2');
      expect(parsed!.targetSw).toBe('node.js');
    });

    it('should return null for invalid URI', () => {
      const matcher = new CPEMatcher();
      
      expect(matcher.parseURI('invalid')).toBeNull();
      expect(matcher.parseURI('cpe:2.2:a:vendor:product')).toBeNull();
    });

    it('should handle wildcard values', () => {
      const matcher = new CPEMatcher();
      const parsed = matcher.parseURI('cpe:2.3:a:*:express:*:*:*:*:*:*:*:*');
      
      expect(parsed).not.toBeNull();
      expect(parsed!.vendor).toBe('*');
      expect(parsed!.version).toBe('*');
    });
  });

  describe('isVersionVulnerable', () => {
    it('should return true when version is in range (inclusive)', () => {
      const matcher = new CPEMatcher();
      const range: VersionRange = {
        versionStart: '1.0.0',
        versionEnd: '2.0.0',
      };
      
      expect(matcher.isVersionVulnerable('1.0.0', range)).toBe(true);
      expect(matcher.isVersionVulnerable('1.5.0', range)).toBe(true);
      expect(matcher.isVersionVulnerable('2.0.0', range)).toBe(true);
    });

    it('should return false when version is outside range', () => {
      const matcher = new CPEMatcher();
      const range: VersionRange = {
        versionStart: '1.0.0',
        versionEnd: '2.0.0',
      };
      
      expect(matcher.isVersionVulnerable('0.9.0', range)).toBe(false);
      expect(matcher.isVersionVulnerable('2.1.0', range)).toBe(false);
    });

    it('should handle exclusive start', () => {
      const matcher = new CPEMatcher();
      const range: VersionRange = {
        versionStart: '1.0.0',
        versionStartExcluding: true,
        versionEnd: '2.0.0',
      };
      
      expect(matcher.isVersionVulnerable('1.0.0', range)).toBe(false);
      expect(matcher.isVersionVulnerable('1.0.1', range)).toBe(true);
    });

    it('should handle exclusive end', () => {
      const matcher = new CPEMatcher();
      const range: VersionRange = {
        versionStart: '1.0.0',
        versionEnd: '2.0.0',
        versionEndExcluding: true,
      };
      
      expect(matcher.isVersionVulnerable('1.9.9', range)).toBe(true);
      expect(matcher.isVersionVulnerable('2.0.0', range)).toBe(false);
    });

    it('should return true when no range specified (all versions)', () => {
      const matcher = new CPEMatcher();
      
      expect(matcher.isVersionVulnerable('1.0.0', {})).toBe(true);
      expect(matcher.isVersionVulnerable('99.99.99', {})).toBe(true);
    });

    it('should handle only start version', () => {
      const matcher = new CPEMatcher();
      const range: VersionRange = {
        versionStart: '2.0.0',
      };
      
      expect(matcher.isVersionVulnerable('1.9.9', range)).toBe(false);
      expect(matcher.isVersionVulnerable('2.0.0', range)).toBe(true);
      expect(matcher.isVersionVulnerable('3.0.0', range)).toBe(true);
    });

    it('should handle only end version', () => {
      const matcher = new CPEMatcher();
      const range: VersionRange = {
        versionEnd: '2.0.0',
      };
      
      expect(matcher.isVersionVulnerable('1.0.0', range)).toBe(true);
      expect(matcher.isVersionVulnerable('2.0.0', range)).toBe(true);
      expect(matcher.isVersionVulnerable('2.0.1', range)).toBe(false);
    });
  });

  describe('compareVersions', () => {
    it('should compare major versions', () => {
      const matcher = new CPEMatcher();
      
      expect(matcher.compareVersions('1.0.0', '2.0.0')).toBe(-1);
      expect(matcher.compareVersions('2.0.0', '1.0.0')).toBe(1);
      expect(matcher.compareVersions('1.0.0', '1.0.0')).toBe(0);
    });

    it('should compare minor versions', () => {
      const matcher = new CPEMatcher();
      
      expect(matcher.compareVersions('1.1.0', '1.2.0')).toBe(-1);
      expect(matcher.compareVersions('1.2.0', '1.1.0')).toBe(1);
    });

    it('should compare patch versions', () => {
      const matcher = new CPEMatcher();
      
      expect(matcher.compareVersions('1.0.1', '1.0.2')).toBe(-1);
      expect(matcher.compareVersions('1.0.2', '1.0.1')).toBe(1);
    });

    it('should handle different version lengths', () => {
      const matcher = new CPEMatcher();
      
      expect(matcher.compareVersions('1.0', '1.0.0')).toBe(0);
      expect(matcher.compareVersions('1.0.0', '1.0')).toBe(0);
      expect(matcher.compareVersions('1.0.1', '1.0')).toBe(1);
    });
  });

  describe('matchPackage', () => {
    it('should match package against CPE criteria', () => {
      const matcher = new CPEMatcher();
      const cpeMatch: CPEMatch = {
        criteria: 'cpe:2.3:a:expressjs:express:*:*:*:*:*:node.js:*:*',
        vulnerable: true,
        matchCriteriaId: 'test-id',
        versionRange: {
          versionStart: '4.0.0',
          versionEnd: '4.19.0',
          versionEndExcluding: true,
        },
      };

      const result = matcher.matchPackage('express', '4.18.2', cpeMatch);
      
      expect(result).not.toBeNull();
      expect(result!.isVulnerable).toBe(true);
      expect(result!.packageName).toBe('express');
      expect(result!.packageVersion).toBe('4.18.2');
    });

    it('should not match different product', () => {
      const matcher = new CPEMatcher();
      const cpeMatch: CPEMatch = {
        criteria: 'cpe:2.3:a:lodash:lodash:*:*:*:*:*:node.js:*:*',
        vulnerable: true,
        matchCriteriaId: 'test-id',
      };

      const result = matcher.matchPackage('express', '4.18.2', cpeMatch);
      
      expect(result).toBeNull();
    });

    it('should match wildcard vendor', () => {
      const matcher = new CPEMatcher();
      const cpeMatch: CPEMatch = {
        criteria: 'cpe:2.3:a:*:express:*:*:*:*:*:*:*:*',
        vulnerable: true,
        matchCriteriaId: 'test-id',
      };

      const result = matcher.matchPackage('express', '4.18.2', cpeMatch);
      
      expect(result).not.toBeNull();
    });

    it('should not be vulnerable when version outside range', () => {
      const matcher = new CPEMatcher();
      const cpeMatch: CPEMatch = {
        criteria: 'cpe:2.3:a:expressjs:express:*:*:*:*:*:node.js:*:*',
        vulnerable: true,
        matchCriteriaId: 'test-id',
        versionRange: {
          versionStart: '4.0.0',
          versionEnd: '4.18.0',
          versionEndExcluding: true,
        },
      };

      const result = matcher.matchPackage('express', '4.19.0', cpeMatch);
      
      expect(result).not.toBeNull();
      expect(result!.isVulnerable).toBe(false);
    });
  });

  describe('addVendorMapping', () => {
    it('should allow adding custom vendor mappings', () => {
      const matcher = new CPEMatcher();
      matcher.addVendorMapping('my-package', 'mycompany');
      
      const cpe = matcher.generateCPE('my-package', '1.0.0');
      
      expect(cpe).toContain(':mycompany:');
    });
  });

  describe('custom mappings in constructor', () => {
    it('should accept custom mappings', () => {
      const matcher = new CPEMatcher({
        'custom-pkg': 'custom_vendor',
      });
      
      const cpe = matcher.generateCPE('custom-pkg', '1.0.0');
      
      expect(cpe).toContain(':custom_vendor:');
    });
  });
});

describe('createCPESearchQuery', () => {
  it('should create search query with wildcards', () => {
    const query = createCPESearchQuery('express');
    
    expect(query).toBe('cpe:2.3:a:expressjs:express:*:*:*:*:*:*:*:*');
  });

  it('should use custom vendor', () => {
    const query = createCPESearchQuery('mypackage', 'myvendor');
    
    expect(query).toBe('cpe:2.3:a:myvendor:mypackage:*:*:*:*:*:*:*:*');
  });
});

describe('extractPackageFromCPE', () => {
  it('should extract package name from CPE', () => {
    const pkg = extractPackageFromCPE('cpe:2.3:a:expressjs:express:4.18.2:*:*:*:*:node.js:*:*');
    
    expect(pkg).toBe('express');
  });

  it('should return null for invalid CPE', () => {
    const pkg = extractPackageFromCPE('invalid');
    
    expect(pkg).toBeNull();
  });
});
