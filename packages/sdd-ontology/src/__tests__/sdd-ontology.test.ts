/**
 * @fileoverview SDD Ontology tests
 * @traceability TSK-SDD-ONTO-001 through TSK-SDD-ONTO-006
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { getCoreModule, corePrefixes } from '../modules/core.js';
import { getEarsModule, parseEarsRequirement, earsTemplates } from '../modules/ears.js';
import { getC4Module, validateC4Hierarchy, c4LevelHierarchy } from '../modules/c4.js';
import { getTraceModule, validateTraceLink, createTraceLink } from '../modules/traceability.js';
import { OntologyLoader } from '../loader/ontology-loader.js';
import { OntologyValidator } from '../validator/ontology-validator.js';
import type { C4Element } from '../types.js';

describe('Core Module', () => {
  it('should return core module metadata', () => {
    const module = getCoreModule();
    expect(module.id).toBe('sdd-core');
    expect(module.namespace).toContain('musubix.dev');
  });

  it('should have standard prefixes', () => {
    expect(corePrefixes.owl).toContain('owl');
    expect(corePrefixes.rdf).toContain('rdf');
  });
});

describe('EARS Module', () => {
  it('should return EARS module metadata', () => {
    const module = getEarsModule();
    expect(module.id).toBe('sdd-ears');
    expect(module.dependencies).toContain('sdd-core');
  });

  it('should have templates for all patterns', () => {
    expect(earsTemplates.ubiquitous).toContain('SHALL');
    expect(earsTemplates['event-driven']).toContain('WHEN');
    expect(earsTemplates['state-driven']).toContain('WHILE');
    expect(earsTemplates.unwanted).toContain('SHALL NOT');
    expect(earsTemplates.optional).toContain('IF');
  });

  it('should parse ubiquitous requirement', () => {
    const result = parseEarsRequirement('THE system SHALL respond within 100ms');
    expect(result?.pattern).toBe('ubiquitous');
    expect(result?.system).toBe('system');
  });

  it('should parse event-driven requirement', () => {
    const result = parseEarsRequirement('WHEN user clicks button, THE system SHALL save data');
    expect(result?.pattern).toBe('event-driven');
    expect(result?.trigger).toBe('user clicks button');
  });
});

describe('C4 Module', () => {
  it('should return C4 module metadata', () => {
    const module = getC4Module();
    expect(module.id).toBe('sdd-c4');
  });

  it('should have correct level hierarchy', () => {
    expect(c4LevelHierarchy).toEqual(['context', 'container', 'component', 'code']);
  });

  it('should validate parent-child hierarchy', () => {
    const parent: C4Element = {
      id: 'ctx-1',
      level: 'context',
      name: 'System',
      type: 'system',
      description: 'Main system',
      relationships: [],
    };
    const validChild: C4Element = {
      id: 'cont-1',
      level: 'container',
      name: 'API',
      type: 'container',
      description: 'API container',
      relationships: [],
    };
    const invalidChild: C4Element = {
      id: 'code-1',
      level: 'code',
      name: 'Class',
      type: 'class',
      description: 'Some class',
      relationships: [],
    };

    expect(validateC4Hierarchy(parent, validChild)).toBe(true);
    expect(validateC4Hierarchy(parent, invalidChild)).toBe(false);
  });
});

describe('Traceability Module', () => {
  it('should return trace module metadata', () => {
    const module = getTraceModule();
    expect(module.id).toBe('sdd-trace');
    expect(module.dependencies).toContain('sdd-core');
  });

  it('should validate trace link types', () => {
    expect(validateTraceLink('requirement', 'design', 'satisfies')).toBe(true);
    expect(validateTraceLink('design', 'task', 'implements')).toBe(true);
    expect(validateTraceLink('requirement', 'design', 'tests')).toBe(false);
  });

  it('should create trace link', () => {
    const link = createTraceLink('REQ-001', 'DES-001', 'satisfies', 'Design satisfies requirement');
    expect(link.source).toBe('REQ-001');
    expect(link.target).toBe('DES-001');
    expect(link.type).toBe('satisfies');
  });
});

describe('OntologyLoader', () => {
  let loader: OntologyLoader;

  beforeEach(() => {
    loader = new OntologyLoader();
  });

  it('should list all modules', () => {
    const modules = loader.listModules();
    expect(modules.length).toBe(4);
    expect(modules.map(m => m.id)).toContain('sdd-core');
  });

  it('should get module metadata', () => {
    const meta = loader.getModuleMetadata('sdd-ears');
    expect(meta?.name).toContain('EARS');
  });

  it('should load sdd-core.ttl file', async () => {
    const content = await loader.loadModule('sdd-core');
    expect(content).not.toBeNull();
    expect(content).toContain('@prefix sdd:');
    expect(content).toContain('sdd:Artifact');
    expect(content).toContain('sdd:Requirement');
    expect(content).toContain('sdd:ConstitutionalArticle');
  });

  it('should report loaded count', async () => {
    await loader.loadModule('sdd-core');
    expect(loader.loadedCount).toBe(1);
    expect(loader.isLoaded('sdd-core')).toBe(true);
  });
});

describe('OntologyValidator', () => {
  let validator: OntologyValidator;

  beforeEach(() => {
    validator = new OntologyValidator();
  });

  it('should validate EARS text with correct syntax', () => {
    const result = validator.validateEarsText('THE system SHALL respond');
    expect(result.valid).toBe(true);
  });

  it('should reject EARS text without SHALL', () => {
    const result = validator.validateEarsText('THE system responds');
    expect(result.valid).toBe(false);
    expect(result.errors[0].code).toBe('MISSING_SHALL');
  });

  it('should warn about ambiguous words', () => {
    const result = validator.validateEarsText('THE system SHALL maybe respond');
    // 'maybe' is not in the list, but 'should' would be
    const result2 = validator.validateEarsText('THE system should respond quickly');
    expect(result2.warnings.some(w => w.code === 'AMBIGUOUS_WORD')).toBe(true);
  });

  it('should validate C4 element ID', () => {
    expect(validator.validateC4ElementId('api-gateway').valid).toBe(true);
    expect(validator.validateC4ElementId('123-invalid').valid).toBe(false);
  });
});
