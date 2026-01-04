/**
 * ComponentInference Tests
 * @requirement REQ-MUSUBIX-001
 */

import { describe, it, expect } from 'vitest';
import { ComponentInference, componentInference } from '../../../src/design/component-inference.js';

describe('ComponentInference', () => {
  describe('infer', () => {
    it('should infer components for veterinary domain', () => {
      const text = `
        Build a pet management system.
        Register dogs, cats and other animals, veterinarian schedule management.
        Owner registration and vaccination records.
      `;
      
      const result = componentInference.infer(text);
      
      expect(result.domain.primaryDomain.id).toBe('veterinary');
      expect(result.components.length).toBeGreaterThan(0);
      expect(result.components.some(c => c.name === 'PetService')).toBe(true);
      expect(result.components.some(c => c.name === 'PetRepository')).toBe(true);
      expect(result.components.some(c => c.name === 'ReservationService')).toBe(true);
    });

    it('should infer components for parking domain', () => {
      const text = `
        Build a parking lot management system.
        Space availability management, entry exit tracking, fee calculation.
        Vehicle plate recognition and barrier control.
      `;
      
      const result = componentInference.infer(text);
      
      expect(result.domain.primaryDomain.id).toBe('parking');
      expect(result.components.some(c => c.name === 'SpaceService')).toBe(true);
      expect(result.components.some(c => c.name === 'EntryExitService')).toBe(true);
      expect(result.components.some(c => c.name === 'FeeCalculator')).toBe(true);
    });

    it('should infer components for ecommerce domain', () => {
      const text = `
        Build an ecommerce site. Product catalog, cart, and order management.
        Customers can browse the shop and checkout.
      `;
      
      const result = componentInference.infer(text);
      
      expect(result.domain.primaryDomain.id).toBe('ecommerce');
      expect(result.components.some(c => c.name === 'CartService')).toBe(true);
      expect(result.components.some(c => c.name === 'ProductRepository')).toBe(true);
    });

    it('should include patterns in result', () => {
      const text = 'Pet clinic reservation system with fee calculation';
      
      const result = componentInference.infer(text);
      
      expect(result.patterns.length).toBeGreaterThan(0);
      expect(result.patterns).toContain('Repository');
      expect(result.patterns).toContain('Service');
    });

    it('should generate architecture recommendation', () => {
      const text = 'Healthcare patient management system';
      
      const result = componentInference.infer(text);
      
      expect(result.architecture).toBeDefined();
      expect(result.architecture.style).toBe('Layered Architecture');
      expect(result.architecture.layers.length).toBe(4);
      expect(result.architecture.layers.some(l => l.layer === 'application')).toBe(true);
      expect(result.architecture.layers.some(l => l.layer === 'infrastructure')).toBe(true);
    });

    it('should include layer information in components', () => {
      const text = 'IoT sensor device management system';
      
      const result = componentInference.infer(text);
      
      const hasApplication = result.components.some(c => c.layer === 'application');
      const hasInfrastructure = result.components.some(c => c.layer === 'infrastructure');
      
      expect(hasApplication).toBe(true);
      expect(hasInfrastructure).toBe(true);
    });

    it('should include dependencies in components', () => {
      const text = 'Event booking system';
      
      const result = componentInference.infer(text);
      
      const eventService = result.components.find(c => c.name === 'EventService');
      
      expect(eventService).toBeDefined();
      expect(eventService!.dependencies.length).toBeGreaterThan(0);
    });
  });

  describe('getTotalComponentCount', () => {
    it('should return total component count', () => {
      const count = componentInference.getTotalComponentCount();
      
      // 59以上のコンポーネントが定義されている
      expect(count).toBeGreaterThanOrEqual(59);
    });
  });

  describe('getComponentCountByDomain', () => {
    it('should return component count by domain', () => {
      const counts = componentInference.getComponentCountByDomain();
      
      expect(counts.veterinary).toBeGreaterThan(0);
      expect(counts.parking).toBeGreaterThan(0);
      expect(counts.ecommerce).toBeGreaterThan(0);
      expect(counts.general).toBeGreaterThan(0);
    });
  });

  describe('architecture recommendation', () => {
    it('should recommend data flow', () => {
      const text = 'Financial transaction system';
      
      const result = componentInference.infer(text);
      
      expect(result.architecture.dataFlow).toContain('Presentation');
      expect(result.architecture.dataFlow).toContain('Application');
      expect(result.architecture.dataFlow).toContain('Infrastructure');
    });

    it('should include scalability recommendation', () => {
      const text = 'IoT telemetry processing system';
      
      const result = componentInference.infer(text);
      
      expect(result.architecture.scalability).toBeDefined();
    });
  });
});
