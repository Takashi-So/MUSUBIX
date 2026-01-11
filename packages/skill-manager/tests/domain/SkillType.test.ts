/**
 * SkillType Value Object Tests
 * 
 * @see REQ-SKILL-001 - Skill Loading
 * @see DES-SKILL-001 - SkillManager
 */

import { describe, it, expect } from 'vitest';
import {
  type SkillType,
  SKILL_TYPES,
  getAllSkillTypes,
  getSkillTypeMetadata,
  getSkillTypeIcon,
} from '../../src/domain/value-objects/SkillType.js';

describe('SkillType', () => {
  describe('SKILL_TYPES', () => {
    it('should include all 11 skill types', () => {
      expect(SKILL_TYPES.size).toBe(11);
      expect(SKILL_TYPES.has('file-operation')).toBe(true);
      expect(SKILL_TYPES.has('code-analysis')).toBe(true);
      expect(SKILL_TYPES.has('code-generation')).toBe(true);
      expect(SKILL_TYPES.has('requirements')).toBe(true);
      expect(SKILL_TYPES.has('design')).toBe(true);
      expect(SKILL_TYPES.has('testing')).toBe(true);
      expect(SKILL_TYPES.has('knowledge-graph')).toBe(true);
      expect(SKILL_TYPES.has('orchestration')).toBe(true);
      expect(SKILL_TYPES.has('security')).toBe(true);
      expect(SKILL_TYPES.has('documentation')).toBe(true);
      expect(SKILL_TYPES.has('custom')).toBe(true);
    });
  });

  describe('getAllSkillTypes', () => {
    it('should return all skill types as array', () => {
      const types = getAllSkillTypes();
      expect(types).toHaveLength(11);
      expect(types).toContain('requirements');
      expect(types).toContain('design');
      expect(types).toContain('testing');
    });
  });

  describe('getSkillTypeMetadata', () => {
    it('should return Japanese labels', () => {
      expect(getSkillTypeMetadata('requirements').label).toBe('要件分析');
      expect(getSkillTypeMetadata('design').label).toBe('設計');
      expect(getSkillTypeMetadata('testing').label).toBe('テスト');
    });

    it('should return descriptions', () => {
      const meta = getSkillTypeMetadata('requirements');
      expect(meta.description).toContain('EARS');
    });

    it('should throw for invalid type', () => {
      expect(() => getSkillTypeMetadata('invalid' as SkillType)).toThrow();
    });
  });

  describe('getSkillTypeIcon', () => {
    it('should return emoji icons', () => {
      expect(getSkillTypeIcon('requirements')).toBe('📋');
      expect(getSkillTypeIcon('design')).toBe('🏗️');
      expect(getSkillTypeIcon('testing')).toBe('🧪');
      expect(getSkillTypeIcon('file-operation')).toBe('📁');
      expect(getSkillTypeIcon('code-analysis')).toBe('🔍');
      expect(getSkillTypeIcon('security')).toBe('🔒');
    });
  });
});
