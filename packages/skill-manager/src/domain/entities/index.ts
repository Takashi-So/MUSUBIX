/**
 * Entities barrel export
 * 
 * @see REQ-SKILL-001 - Skill Loading
 * @see REQ-SKILL-002 - Skill Validation
 */

export {
  type SkillContext,
  type SkillResult,
  type SkillExecutor,
  type Skill,
  createSkill,
  executeSkill,
  enableSkill,
  disableSkill,
  skillMatchesFilter,
  createNoOpResult,
  createErrorResult,
} from './Skill.js';

export {
  type SkillFilter,
  type SkillRegistry,
  createSkillRegistry,
  addSkillToRegistry,
  removeSkillFromRegistry,
  getSkillById,
  findSkills,
  getAllSkills,
  getSkillsByType,
  executeSkillFromRegistry,
  getRegistryStats,
} from './SkillRegistry.js';
