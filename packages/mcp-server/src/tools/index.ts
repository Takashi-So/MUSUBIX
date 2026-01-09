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

export {
  codegraphIndexTool,
  codegraphQueryTool,
  codegraphFindDependenciesTool,
  codegraphFindCallersTool,
  codegraphFindCalleesTool,
  codegraphGlobalSearchTool,
  codegraphLocalSearchTool,
  codegraphStatsTool,
  codegraphTools,
  getCodeGraphTools,
  handleCodeGraphTool,
  resetCodeGraph,
} from './codegraph-tools.js';

import { getSddTools as _getSddTools } from './sdd-tools.js';
import { getSymbolicTools as _getSymbolicTools } from './symbolic-tools.js';
import { getPatternIntegrationTools as _getPatternIntegrationTools } from './pattern-tools.js';
import { getOntologyTools as _getOntologyTools } from './ontology-tools.js';
import { getYataTools as _getYataTools } from './yata-tools.js';
import { kgprTools as _kgprTools } from './kgpr-tools.js';
import { getFormalVerifyTools as _getFormalVerifyTools } from './formal-verify-tools.js';
import { SYNTHESIS_TOOLS as _SYNTHESIS_TOOLS } from './synthesis-tools.js';
import { getCodeGraphTools as _getCodeGraphTools } from './codegraph-tools.js';

/**
 * Get all available tools
 */
export function getAllTools() {
  return [
    ..._getSddTools(),
    ..._getSymbolicTools(),
    ..._getPatternIntegrationTools(),
    ..._getOntologyTools(),
    ..._getYataTools(),
    ..._kgprTools,
    ..._getFormalVerifyTools(),
    ..._SYNTHESIS_TOOLS,
    ..._getCodeGraphTools(),
  ];
}
