/**
 * @fileoverview EARS ontology module
 * @traceability TSK-SDD-ONTO-002
 */

import type { OntologyModule, EarsPatternType, EarsRequirement } from '../types.js';

/**
 * EARS ontology module
 */
export const earsModule: OntologyModule = {
  id: 'sdd-ears',
  name: 'SDD EARS Ontology',
  namespace: 'https://musubix.dev/ontology/sdd/ears#',
  version: '1.0.0',
  description: 'EARS (Easy Approach to Requirements Syntax) patterns',
  dependencies: ['sdd-core'],
  filePath: 'ttl/sdd-ears.ttl',
};

/**
 * EARS namespace prefixes
 */
export const earsPrefixes = {
  'ears': 'https://musubix.dev/ontology/sdd/ears#',
};

/**
 * EARS pattern templates
 */
export const earsTemplates: Record<EarsPatternType, string> = {
  'ubiquitous': 'THE {system} SHALL {response}',
  'event-driven': 'WHEN {trigger}, THE {system} SHALL {response}',
  'state-driven': 'WHILE {condition}, THE {system} SHALL {response}',
  'unwanted': 'THE {system} SHALL NOT {response}',
  'optional': 'IF {condition}, THEN THE {system} SHALL {response}',
};

/**
 * Parse EARS requirement from text
 */
export function parseEarsRequirement(text: string): Partial<EarsRequirement> | null {
  // Ubiquitous: THE [system] SHALL [response]
  const ubiquitousMatch = text.match(/^THE\s+(.+?)\s+SHALL\s+(.+)$/i);
  if (ubiquitousMatch && !text.includes('SHALL NOT')) {
    return {
      pattern: 'ubiquitous',
      system: ubiquitousMatch[1],
      response: ubiquitousMatch[2],
    };
  }

  // Event-driven: WHEN [trigger], THE [system] SHALL [response]
  const eventMatch = text.match(/^WHEN\s+(.+?),\s+THE\s+(.+?)\s+SHALL\s+(.+)$/i);
  if (eventMatch) {
    return {
      pattern: 'event-driven',
      trigger: eventMatch[1],
      system: eventMatch[2],
      response: eventMatch[3],
    };
  }

  // State-driven: WHILE [condition], THE [system] SHALL [response]
  const stateMatch = text.match(/^WHILE\s+(.+?),\s+THE\s+(.+?)\s+SHALL\s+(.+)$/i);
  if (stateMatch) {
    return {
      pattern: 'state-driven',
      condition: stateMatch[1],
      system: stateMatch[2],
      response: stateMatch[3],
    };
  }

  // Unwanted: THE [system] SHALL NOT [behavior]
  const unwantedMatch = text.match(/^THE\s+(.+?)\s+SHALL\s+NOT\s+(.+)$/i);
  if (unwantedMatch) {
    return {
      pattern: 'unwanted',
      system: unwantedMatch[1],
      response: unwantedMatch[2],
    };
  }

  // Optional: IF [condition], THEN THE [system] SHALL [response]
  const optionalMatch = text.match(/^IF\s+(.+?),\s+THEN\s+THE\s+(.+?)\s+SHALL\s+(.+)$/i);
  if (optionalMatch) {
    return {
      pattern: 'optional',
      condition: optionalMatch[1],
      system: optionalMatch[2],
      response: optionalMatch[3],
    };
  }

  return null;
}

/**
 * Get EARS module metadata
 */
export function getEarsModule(): OntologyModule {
  return { ...earsModule };
}
