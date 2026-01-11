/**
 * SkillRegistry Entity Tests
 * 
 * @see REQ-SKILL-001 - Skill Loading
 * @see REQ-SKILL-002 - Skill Validation
 */

import { describe, it, expect } from 'vitest';
import {
  type SkillRegistry,
  createSkillRegistry,
  addSkillToRegistry,
  removeSkillFromRegistry,
  getSkillById,
  findSkills,
} from '../../src/domain/entities/SkillRegistry.js';
import {
  type Skill,
  createSkill,
} from '../../src/domain/entities/Skill.js';
import {
  createSkillMetadata,
} from '../../src/domain/value-objects/SkillMetadata.js';
import type { SkillType } from '../../src/domain/value-objects/SkillType.js';

describe('SkillRegistry', () => {
  // Helper to create test skills
  const createTestSkill = (id: string, type: SkillType = 'testing', enabled = true): Skill => {
    const metadata = createSkillMetadata({
      id,
      name: `Test Skill ${id}`,
      description: `Test skill description for ${id}`,
      type,
      tags: ['test', type],
    });
    
    return createSkill(
      metadata,
      async () => ({ success: true, duration: 0, timestamp: new Date() }),
      enabled
    );
  };

  describe('createSkillRegistry', () => {
    it('should create empty registry', () => {
      const registry = createSkillRegistry();
      expect(registry.skills.size).toBe(0);
      expect(registry.updatedAt).toBeInstanceOf(Date);
    });
  });

  describe('addSkillToRegistry', () => {
    it('should add skill to registry', () => {
      const registry = createSkillRegistry();
      const skill = createTestSkill('SKL-001');
      const updated = addSkillToRegistry(registry, skill);
      
      expect(updated.skills.size).toBe(1);
      expect(updated.skills.has('SKL-001')).toBe(true);
    });

    it('should replace skill with same ID', () => {
      const registry = createSkillRegistry();
      const skill1 = createTestSkill('SKL-001');
      const skill2 = createTestSkill('SKL-001');
      
      let updated = addSkillToRegistry(registry, skill1);
      updated = addSkillToRegistry(updated, skill2);
      
      expect(updated.skills.size).toBe(1);
    });
  });

  describe('removeSkillFromRegistry', () => {
    it('should remove skill from registry', () => {
      const registry = createSkillRegistry();
      const skill = createTestSkill('SKL-001');
      let updated = addSkillToRegistry(registry, skill);
      updated = removeSkillFromRegistry(updated, 'SKL-001');
      
      expect(updated.skills.size).toBe(0);
    });

    it('should handle removing non-existent skill', () => {
      const registry = createSkillRegistry();
      const updated = removeSkillFromRegistry(registry, 'NON-EXISTENT');
      
      expect(updated.skills.size).toBe(0);
    });
  });

  describe('getSkillById', () => {
    it('should find skill by ID', () => {
      const registry = createSkillRegistry();
      const skill = createTestSkill('SKL-001');
      const updated = addSkillToRegistry(registry, skill);
      
      const found = getSkillById(updated, 'SKL-001');
      expect(found).toBeDefined();
      expect(found?.metadata.id).toBe('SKL-001');
    });

    it('should return undefined for unknown ID', () => {
      const registry = createSkillRegistry();
      const found = getSkillById(registry, 'NON-EXISTENT');
      
      expect(found).toBeUndefined();
    });
  });

  describe('findSkills', () => {
    it('should filter by type', () => {
      let registry = createSkillRegistry();
      registry = addSkillToRegistry(registry, createTestSkill('SKL-001', 'testing'));
      registry = addSkillToRegistry(registry, createTestSkill('SKL-002', 'design'));
      registry = addSkillToRegistry(registry, createTestSkill('SKL-003', 'testing'));
      
      const testingSkills = findSkills(registry, { type: 'testing' });
      expect(testingSkills).toHaveLength(2);
    });

    it('should filter by enabledOnly', () => {
      let registry = createSkillRegistry();
      registry = addSkillToRegistry(registry, createTestSkill('SKL-001', 'testing', true));
      registry = addSkillToRegistry(registry, createTestSkill('SKL-002', 'testing', false));
      
      const enabledSkills = findSkills(registry, { enabledOnly: true });
      expect(enabledSkills).toHaveLength(1);
      expect(enabledSkills[0].metadata.id).toBe('SKL-001');
    });

    it('should return all skills when no filter', () => {
      let registry = createSkillRegistry();
      registry = addSkillToRegistry(registry, createTestSkill('SKL-001'));
      registry = addSkillToRegistry(registry, createTestSkill('SKL-002'));
      
      const allSkills = findSkills(registry, {});
      expect(allSkills).toHaveLength(2);
    });
  });
});
