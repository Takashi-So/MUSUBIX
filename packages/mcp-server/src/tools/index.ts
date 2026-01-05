/**
 * MCP Tools Module
 *
 * @packageDocumentation
 * @module tools
 */

export {
  createRequirementsTool,
  validateRequirementsTool,
  createDesignTool,
  validateDesignTool,
  createTasksTool,
  queryKnowledgeTool,
  updateKnowledgeTool,
  validateConstitutionTool,
  validateTraceabilityTool,
  sddTools,
  getSddTools,
} from './sdd-tools.js';

export {
  filterCodeTool,
  detectHallucinationsTool,
  checkConstitutionTool,
  estimateConfidenceTool,
  getPipelineInfoTool,
  symbolicTools,
  getSymbolicTools,
} from './symbolic-tools.js';

export {
  learnPatternTool,
  consolidatePatternsTool,
  queryPatternRelationsTool,
  searchPatternsTool,
  getLearningStatsTool,
  importToKnowledgeGraphTool,
  exportKnowledgeGraphTool,
  patternIntegrationTools,
  getPatternIntegrationTools,
  handlePatternIntegrationTool,
  resetPatternIntegration,
} from './pattern-tools.js';

export {
  consistencyValidateTool,
  validateTripleTool,
  checkCircularTool,
  ontologyTools,
  getOntologyTools,
} from './ontology-tools.js';

/**
 * Get all available tools
 */
export function getAllTools() {
  const { getSddTools } = require('./sdd-tools.js');
  const { getSymbolicTools } = require('./symbolic-tools.js');
  const { getPatternIntegrationTools } = require('./pattern-tools.js');
  const { getOntologyTools } = require('./ontology-tools.js');
  return [...getSddTools(), ...getSymbolicTools(), ...getPatternIntegrationTools(), ...getOntologyTools()];
}
