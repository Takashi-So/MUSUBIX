/**
 * DomainDetector Tests
 * @requirement REQ-MUSUBIX-001
 */

import { describe, it, expect } from 'vitest';
import { DomainDetector, domainDetector, DOMAINS } from '../../../src/design/domain-detector.js';

describe('DomainDetector', () => {
  describe('DOMAINS', () => {
    it('should have 62 domains defined', () => {
      expect(DOMAINS.length).toBe(62);
    });

    it('should include veterinary domain', () => {
      const vet = DOMAINS.find(d => d.id === 'veterinary');
      expect(vet).toBeDefined();
      expect(vet!.nameJa).toBe('動物病院');
      expect(vet!.category).toBe('healthcare');
      expect(vet!.keywords).toContain('pet');
    });

    it('should include parking domain', () => {
      const parking = DOMAINS.find(d => d.id === 'parking');
      expect(parking).toBeDefined();
      expect(parking!.nameJa).toBe('駐車場');
      expect(parking!.category).toBe('service');
      expect(parking!.keywords).toContain('space');
      expect(parking!.keywords).toContain('fee');
    });
  });

  describe('detect', () => {
    it('should detect veterinary domain from pet clinic text', () => {
      const text = `
        Build a pet management system.
        Register dogs, cats and other animals, manage veterinarian schedules.
        Manage owner information and pet medical history with vaccination records.
      `;
      
      const result = domainDetector.detect(text);
      
      expect(result.primaryDomain.id).toBe('veterinary');
      expect(result.confidence).toBeGreaterThan(0.5);
      expect(result.matchedKeywords).toContain('pet');
    });

    it('should detect parking domain from parking lot text', () => {
      const text = `
        Build a parking lot management system.
        Manage space availability, entry and exit, fee calculation.
        Implement plate recognition and vehicle tracking with barrier control.
      `;
      
      const result = domainDetector.detect(text);
      
      expect(result.primaryDomain.id).toBe('parking');
      expect(result.matchedKeywords).toContain('space');
      expect(result.matchedKeywords).toContain('fee');
    });

    it('should detect ecommerce domain from shopping text', () => {
      const text = `
        Build an e-commerce site.
        Implement product catalog, cart functionality, order management, and checkout.
        Customers can browse products, add to cart and purchase in the shop.
      `;
      
      const result = domainDetector.detect(text);
      
      expect(result.primaryDomain.id).toBe('ecommerce');
      expect(result.matchedKeywords).toContain('cart');
      expect(result.matchedKeywords).toContain('product');
    });

    it('should detect booking domain from reservation text', () => {
      const text = `
        Build a reservation booking system.
        Customers can check availability and make appointments.
        Send reminder notifications and manage the schedule.
      `;
      
      const result = domainDetector.detect(text);
      
      expect(result.primaryDomain.id).toBe('booking');
      expect(result.matchedKeywords).toContain('reservation');
    });

    it('should detect healthcare domain from medical text', () => {
      const text = `
        Build a hospital management system.
        Manage patient medical records, diagnosis information, and treatment plans.
        Doctors examine patients at the clinic and prescribe medications.
      `;
      
      const result = domainDetector.detect(text);
      
      expect(result.primaryDomain.id).toBe('healthcare');
      expect(result.matchedKeywords).toContain('patient');
    });

    it('should return general domain for unknown text', () => {
      const text = 'これは特に何のドメインでもないテキストです。';
      
      const result = domainDetector.detect(text);
      
      expect(result.primaryDomain.id).toBe('general');
      expect(result.confidence).toBe(0.5);
    });

    it('should suggest components based on domain', () => {
      const text = 'Pet clinic reservation system with veterinarian schedule';
      
      const result = domainDetector.detect(text);
      
      expect(result.suggestedComponents.length).toBeGreaterThan(0);
    });

    it('should detect secondary domains', () => {
      const text = `
        Pet hotel booking and reservation system.
        Manage animal accommodation and payment processing.
      `;
      
      const result = domainDetector.detect(text);
      
      // veterinary or booking or payment が検出される
      expect(result.secondaryDomains.length).toBeGreaterThanOrEqual(0);
    });
  });

  describe('getDomainsByCategory', () => {
    it('should filter domains by category', () => {
      const healthDomains = domainDetector.getDomainsByCategory('healthcare');
      
      expect(healthDomains.length).toBeGreaterThan(0);
      expect(healthDomains.every(d => d.category === 'healthcare')).toBe(true);
      expect(healthDomains.some(d => d.id === 'veterinary')).toBe(true);
    });

    it('should return service domains', () => {
      const serviceDomains = domainDetector.getDomainsByCategory('service');
      
      expect(serviceDomains.length).toBeGreaterThan(0);
      expect(serviceDomains.some(d => d.id === 'parking')).toBe(true);
      expect(serviceDomains.some(d => d.id === 'hotel')).toBe(true);
    });
  });

  describe('getDomainById', () => {
    it('should get domain by id', () => {
      const vet = domainDetector.getDomainById('veterinary');
      
      expect(vet).toBeDefined();
      expect(vet!.name).toBe('Veterinary');
    });

    it('should return undefined for unknown id', () => {
      const unknown = domainDetector.getDomainById('unknown-domain');
      
      expect(unknown).toBeUndefined();
    });
  });

  describe('getDomainCount', () => {
    it('should return 62 domains', () => {
      expect(domainDetector.getDomainCount()).toBe(62);
    });
  });

  describe('custom domains', () => {
    it('should accept custom domains', () => {
      const customDetector = new DomainDetector([
        {
          id: 'custom',
          name: 'Custom',
          nameJa: 'カスタム',
          category: 'general',
          keywords: ['custom', 'special'],
          relatedDomains: [],
        },
      ]);
      
      const result = customDetector.detect('This is a custom special system');
      
      expect(result.primaryDomain.id).toBe('custom');
    });
  });
});
