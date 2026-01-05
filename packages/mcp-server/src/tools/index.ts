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

/**
 * Get all available tools
 */
export function getAllTools() {
  const { getSddTools } = require('./sdd-tools.js');
  const { getSymbolicTools } = require('./symbolic-tools.js');
  return [...getSddTools(), ...getSymbolicTools()];
}
