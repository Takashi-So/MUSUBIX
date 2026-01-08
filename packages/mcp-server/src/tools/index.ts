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

export {
  analyzeCodeTool,
  updateKnowledgeFromCodeTool,
  bulkUpdateKnowledgeTool,
  queryKnowledgeGraphTool,
  yataTools,
  getYataTools,
} from './yata-tools.js';

export {
  kgprCreateTool,
  kgprDiffTool,
  kgprListTool,
  kgprSubmitTool,
  kgprReviewTool,
  kgprTools,
} from './kgpr-tools.js';

export {
  verifyPreconditionTool,
  verifyPostconditionTool,
  earsToSmtTool,
  traceAddLinkTool,
  traceQueryTool,
  traceImpactTool,
  formalVerifyTools,
  getFormalVerifyTools,
  handleFormalVerifyTool,
} from './formal-verify-tools.js';

export {
  synthesizeFromExamples,
  analyzeExamples,
  learnPatterns,
  queryPatterns,
  getSynthesisStats,
  SYNTHESIS_TOOLS,
} from './synthesis-tools.js';

/**
 * Get all available tools
 */
export function getAllTools() {
  const { getSddTools } = require('./sdd-tools.js');
  const { getSymbolicTools } = require('./symbolic-tools.js');
  const { getPatternIntegrationTools } = require('./pattern-tools.js');
  const { getOntologyTools } = require('./ontology-tools.js');
  const { getYataTools } = require('./yata-tools.js');
  const { kgprTools } = require('./kgpr-tools.js');
  const { getFormalVerifyTools } = require('./formal-verify-tools.js');
  const { SYNTHESIS_TOOLS } = require('./synthesis-tools.js');
  return [
    ...getSddTools(),
    ...getSymbolicTools(),
    ...getPatternIntegrationTools(),
    ...getOntologyTools(),
    ...getYataTools(),
    ...kgprTools,
    ...getFormalVerifyTools(),
    ...SYNTHESIS_TOOLS,
  ];
}
