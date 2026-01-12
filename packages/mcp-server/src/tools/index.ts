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

// v3.0.0 NEW - Git-Native Knowledge Tools
export {
  knowledgePutEntityTool,
  knowledgeGetEntityTool,
  knowledgeDeleteEntityTool,
  knowledgeAddRelationTool,
  knowledgeQueryTool,
  knowledgeTraverseTool,
  knowledgeTools,
  getKnowledgeTools,
  handleKnowledgeTool,
  getKnowledgeStore,
  resetKnowledgeStore,
} from './knowledge-tools.js';

// v3.0.0 NEW - Policy Tools
export {
  policyValidateTool,
  policyListTool,
  policyGetTool,
  policyCheckFileTool,
  policyTools,
  getPolicyTools,
  handlePolicyTool,
  getPolicyEngine,
  resetPolicyEngine,
  constitutionPolicies,
} from './policy-tools.js';

// v3.0.0 NEW - Decision Tools
export {
  decisionCreateTool,
  decisionListTool,
  decisionGetTool,
  decisionAcceptTool,
  decisionDeprecateTool,
  decisionSearchTool,
  decisionFindByRequirementTool,
  decisionGenerateIndexTool,
  decisionTools,
  getDecisionTools,
  handleDecisionTool,
  getDecisionManager,
  resetDecisionManager,
  ADR_TEMPLATE,
} from './decision-tools.js';

// v2.4.0 NEW - Agent Orchestration Tools
export {
  agentDispatchTool,
  agentStatusTool,
  agentCancelTool,
  agentAnalyzeTool,
  type AgentDispatchInput,
  type AgentStatusInput,
  type AgentCancelInput,
  type AgentAnalyzeInput,
} from './agent-tools.js';

export {
  handleAgentDispatch,
  handleAgentStatus,
  handleAgentCancel,
  handleAgentAnalyze,
} from './agent-handlers.js';

// v2.4.0 NEW - Workflow Engine Tools
export {
  workflowCreateTool,
  workflowTransitionTool,
  workflowStatusTool,
  workflowReviewTool,
  workflowGateTool,
  type WorkflowCreateInput,
  type WorkflowTransitionInput,
  type WorkflowStatusInput,
  type WorkflowReviewInput,
  type WorkflowGateInput,
} from './workflow-tools.js';

export {
  handleWorkflowCreate,
  handleWorkflowTransition,
  handleWorkflowStatus,
  handleWorkflowReview,
  handleWorkflowGate,
} from './workflow-handlers.js';

// v2.4.0 NEW - Skill Manager Tools
export {
  skillListTool,
  skillExecuteTool,
  skillValidateTool,
  skillInfoTool,
  skillRegisterTool,
  type SkillListInput,
  type SkillExecuteInput,
  type SkillValidateInput,
  type SkillInfoInput,
  type SkillRegisterInput,
} from './skill-tools.js';

export {
  handleSkillList,
  handleSkillExecute,
  handleSkillValidate,
  handleSkillInfo,
  handleSkillRegister,
} from './skill-handlers.js';

// v3.1.0 NEW - Watch Tools
export {
  watchStartTool,
  watchStopTool,
  watchStatusTool,
  watchRunNowTool,
  watchReportTool,
  watchTools,
  getWatchTools,
  handleWatchTool,
  handleWatchStart,
  handleWatchStop,
  handleWatchStatus,
  handleWatchRunNow,
  handleWatchReport,
} from './watch-tools.js';

// v3.1.0 NEW - CodeQL Tools
export {
  codeqlParseSarifTool,
  codeqlAggregateTool,
  codeqlCweLookupTool,
  codeqlListCwesTool,
  codeqlSummaryTool,
  codeqlFixSuggestionsTool,
  codeqlTools,
  getCodeQLTools,
  handleCodeQLTool,
  handleCodeQLParseSarif,
  handleCodeQLAggregate,
  handleCodeQLCweLookup,
  handleCodeQLListCwes,
  handleCodeQLSummary,
  handleCodeQLFixSuggestions,
} from './codeql-tools.js';

// v3.1.0 NEW - Team Tools
export {
  teamSharePatternTool,
  teamListPatternsTool,
  teamSyncTool,
  teamStatusTool,
  teamAddKnowledgeTool,
  teamQueryKnowledgeTool,
  teamTools,
} from './team-tools.js';

// v3.1.0 NEW - Spaces Tools
export {
  spacesCreateTool,
  spacesActivateTool,
  spacesListTool,
  spacesStatusTool,
  spacesSuggestTool,
  spacesTools,
} from './spaces-tools.js';

import { getSddTools as _getSddTools } from './sdd-tools.js';
import { getSymbolicTools as _getSymbolicTools } from './symbolic-tools.js';
import { getPatternIntegrationTools as _getPatternIntegrationTools } from './pattern-tools.js';
import { getOntologyTools as _getOntologyTools } from './ontology-tools.js';
import { getFormalVerifyTools as _getFormalVerifyTools } from './formal-verify-tools.js';
import { SYNTHESIS_TOOLS as _SYNTHESIS_TOOLS } from './synthesis-tools.js';
import { getCodeGraphTools as _getCodeGraphTools } from './codegraph-tools.js';
// v3.0.0 NEW - Git-Native Knowledge imports
import { getKnowledgeTools as _getKnowledgeTools } from './knowledge-tools.js';
import { getPolicyTools as _getPolicyTools } from './policy-tools.js';
import { getDecisionTools as _getDecisionTools } from './decision-tools.js';
import {
  agentDispatchTool as _agentDispatchTool,
  agentStatusTool as _agentStatusTool,
  agentCancelTool as _agentCancelTool,
  agentAnalyzeTool as _agentAnalyzeTool,
} from './agent-tools.js';
import {
  workflowCreateTool as _workflowCreateTool,
  workflowTransitionTool as _workflowTransitionTool,
  workflowStatusTool as _workflowStatusTool,
  workflowReviewTool as _workflowReviewTool,
  workflowGateTool as _workflowGateTool,
} from './workflow-tools.js';
import {
  skillListTool as _skillListTool,
  skillExecuteTool as _skillExecuteTool,
  skillValidateTool as _skillValidateTool,
  skillInfoTool as _skillInfoTool,
  skillRegisterTool as _skillRegisterTool,
} from './skill-tools.js';

// v3.1.0 NEW - Watch Tools import
import { getWatchTools as _getWatchTools } from './watch-tools.js';

// v3.1.0 NEW - CodeQL Tools import
import { getCodeQLTools as _getCodeQLTools } from './codeql-tools.js';

// v3.1.0 NEW - Team Tools import
import { teamTools as _teamTools } from './team-tools.js';

// v3.1.0 NEW - Spaces Tools import
import { spacesTools as _spacesTools } from './spaces-tools.js';

/**
 * v2.4.0 Agent Orchestration Tools
 */
export const agentTools = [
  _agentDispatchTool,
  _agentStatusTool,
  _agentCancelTool,
  _agentAnalyzeTool,
];

/**
 * v2.4.0 Workflow Engine Tools
 */
export const workflowTools = [
  _workflowCreateTool,
  _workflowTransitionTool,
  _workflowStatusTool,
  _workflowReviewTool,
  _workflowGateTool,
];

/**
 * v2.4.0 Skill Manager Tools
 */
export const skillTools = [
  _skillListTool,
  _skillExecuteTool,
  _skillValidateTool,
  _skillInfoTool,
  _skillRegisterTool,
];

/**
 * Get all available tools
 */
export function getAllTools() {
  return [
    ..._getSddTools(),
    ..._getSymbolicTools(),
    ..._getPatternIntegrationTools(),
    ..._getOntologyTools(),
    ..._getFormalVerifyTools(),
    ..._SYNTHESIS_TOOLS,
    ..._getCodeGraphTools(),
    // v2.4.0 NEW
    ...agentTools,
    ...workflowTools,
    ...skillTools,
    // v3.0.0 NEW - Git-Native Knowledge
    ..._getKnowledgeTools(),
    ..._getPolicyTools(),
    ..._getDecisionTools(),
    // v3.1.0 NEW - Watch Tools
    ..._getWatchTools(),
    // v3.1.0 NEW - CodeQL Tools
    ..._getCodeQLTools(),
    // v3.1.0 NEW - Team Tools
    ..._teamTools,
    // v3.1.0 NEW - Spaces Tools
    ..._spacesTools,
  ];
}

/**
 * v2.4.0 Tool Categories
 */
export const toolCategories = {
  sdd: ['sdd_create_requirements', 'sdd_validate_requirements', 'sdd_create_design', 'sdd_validate_design', 'sdd_create_tasks', 'sdd_validate_constitution', 'sdd_validate_traceability'],
  agent: ['agent_dispatch', 'agent_status', 'agent_cancel', 'agent_analyze'],
  workflow: ['workflow_create', 'workflow_transition', 'workflow_status', 'workflow_review', 'workflow_gate'],
  skill: ['skill_list', 'skill_execute', 'skill_validate', 'skill_info', 'skill_register'],
  // v3.0.0 NEW
  knowledge: ['knowledge_put_entity', 'knowledge_get_entity', 'knowledge_delete_entity', 'knowledge_add_relation', 'knowledge_query', 'knowledge_traverse'],
  policy: ['policy_validate', 'policy_list', 'policy_get', 'policy_check_file'],
  decision: ['decision_create', 'decision_list', 'decision_get', 'decision_accept', 'decision_deprecate', 'decision_search', 'decision_find_by_requirement', 'decision_generate_index'],
  // v3.1.0 NEW
  watch: ['watch_start', 'watch_stop', 'watch_status', 'watch_run_now', 'watch_report'],
  codeql: ['codeql_parse_sarif', 'codeql_aggregate', 'codeql_cwe_lookup', 'codeql_list_cwes', 'codeql_summary', 'codeql_fix_suggestions'],
  team: ['team_share_pattern', 'team_list_patterns', 'team_sync', 'team_status', 'team_add_knowledge', 'team_query_knowledge'],
  spaces: ['spaces_create', 'spaces_activate', 'spaces_list', 'spaces_status', 'spaces_suggest'],
};
