// Type Definitions for Deep Research
// REQ: REQ-DR-CORE-001 through REQ-DR-NFR-006
// DES: DES-DR-v3.4.0 - Level 4: Code

/**
 * Research Configuration
 * REQ: REQ-DR-CORE-001
 */
export interface ResearchConfig {
  /** Research query */
  query: string;
  /** Maximum number of iterations (default: 10) */
  maxIterations?: number;
  /** Token budget for LM API calls (default: 15000) */
  tokenBudget?: number;
  /** Search provider configuration */
  providers?: {
    jinaApiKey?: string;
    braveApiKey?: string;
  };
  /** Output format (default: 'markdown') */
  outputFormat?: 'markdown' | 'json';
}

/**
 * SERP Query
 * REQ: REQ-DR-CORE-002
 */
export interface SERPQuery {
  /** Search keywords */
  keywords: string;
  /** Number of results to return (default: 5) */
  topK?: number;
  /** Timestamp of the query */
  timestamp: number;
  /** Iteration number */
  iteration: number;
}

/**
 * Search Result
 * REQ: REQ-DR-CORE-002
 */
export interface SearchResult {
  /** Page title */
  title: string;
  /** Page URL */
  url: string;
  /** Snippet/description */
  snippet: string;
  /** Published date (if available) */
  date?: string;
  /** Relevance score (0-1) */
  relevance?: number;
}

/**
 * Web Content
 * REQ: REQ-DR-CORE-003
 */
export interface WebContent {
  /** Source URL */
  url: string;
  /** Page title */
  title: string;
  /** Markdown content */
  content: string;
  /** Extracted facts */
  extractedFacts: string[];
}

/**
 * Web Read Request
 * REQ: REQ-DR-CORE-003
 */
export interface WebReadRequest {
  /** URL to read */
  url: string;
  /** Timeout in milliseconds (default: 5000) */
  timeout?: number;
}

/**
 * Reasoning Result
 * REQ: REQ-DR-CORE-004
 */
export interface ReasoningResult {
  /** Generated knowledge items */
  knowledgeItems: KnowledgeItem[];
  /** Token usage */
  tokensUsed: number;
}

/**
 * Reflective Question
 * REQ: REQ-DR-CORE-009
 */
export interface ReflectiveQuestion {
  /** Question text */
  question: string;
  /** Reason for asking */
  reason: string;
  /** Priority (1-5, higher = more important) */
  priority: number;
}

/**
 * Knowledge Item
 * REQ: REQ-DR-CORE-008
 */
export interface KnowledgeItem {
  /** Unique ID (auto-generated) */
  id?: string;
  /** Item type */
  type: 'fact' | 'opinion' | 'question' | 'recommendation';
  /** Content text */
  content: string;
  /** Source URLs */
  sources: string[];
  /** Relevance score (0-1) */
  relevance: number;
  /** Iteration number */
  iteration?: number;
  /** Timestamp */
  timestamp: number;
}

/**
 * Research Context (for LM reasoning)
 * REQ: REQ-DR-CORE-004
 */
export interface ResearchContext {
  /** Research query */
  query: string;
  /** Current iteration */
  iteration: number;
  /** Maximum iterations */
  maxIterations: number;
  /** Current knowledge base */
  knowledgeBase: KnowledgeItem[];
}

/**
 * Reference (Citation)
 * REQ: REQ-DR-CORE-007
 */
export interface Reference {
  /** Reference ID */
  id: string;
  /** Source URL */
  url: string;
  /** Source title */
  title: string;
  /** Access date */
  accessDate: string;
}

/**
 * Research Report
 * REQ: REQ-DR-CORE-005
 */
export interface ResearchReport {
  /** Original query */
  query: string;
  /** Executive summary */
  summary: string;
  /** Key findings */
  findings: Finding[];
  /** Technical options */
  options: TechnicalOption[];
  /** Recommendations */
  recommendations: Recommendation[];
  /** References/citations */
  references: Reference[];
  /** Metadata */
  metadata: ReportMetadata;
}

/**
 * Finding
 * REQ: REQ-DR-CORE-005
 */
export interface Finding {
  /** Finding statement */
  statement: string;
  /** Supporting citations */
  citations: string[];
  /** Confidence score (0-1) */
  confidence: number;
}

/**
 * Technical Option
 * REQ: REQ-DR-CORE-005
 */
export interface TechnicalOption {
  /** Option name */
  name: string;
  /** Description */
  description: string;
  /** Pros */
  pros: string[];
  /** Cons */
  cons: string[];
  /** Use cases */
  useCases: string[];
}

/**
 * Recommendation
 * REQ: REQ-DR-CORE-005
 */
export interface Recommendation {
  /** Recommendation text */
  recommendation: string;
  /** Rationale */
  rationale: string;
  /** Priority (1-5) */
  priority: number;
}

/**
 * Report Metadata
 * REQ: REQ-DR-CORE-005
 */
export interface ReportMetadata {
  /** Number of iterations */
  iterations: number;
  /** Total tokens used */
  tokensUsed: number;
  /** Duration in milliseconds */
  duration: number;
  /** Overall confidence (0-1) */
  confidence: number;
}

/**
 * Iteration Log
 * REQ: REQ-DR-CORE-010
 */
export interface IterationLog {
  /** Iteration number */
  iteration: number;
  /** Action taken */
  action: ResearchAction;
  /** Tokens used in this iteration */
  tokensUsed: number;
  /** Knowledge items gained */
  knowledgeGained: number;
  /** Timestamp */
  timestamp: number;
}

/**
 * Research Action (Union Type)
 * REQ: REQ-DR-CORE-010
 */
export type ResearchAction =
  | { type: 'search'; query: string; resultsCount: number }
  | { type: 'read'; url: string; success: boolean }
  | { type: 'reason'; tokensUsed: number; knowledgeGained: number }
  | { type: 'answer'; answer: string; isDefinitive: boolean };

/**
 * Token Usage
 * REQ: REQ-DR-CORE-006
 */
export interface TokenUsage {
  /** Operation name */
  operation: string;
  /** Tokens consumed */
  tokens: number;
  /** Timestamp */
  timestamp: number;
}

/**
 * Search Provider Interface
 * REQ: REQ-DR-CORE-002
 */
export interface SearchProvider {
  /** Provider name */
  name: string;
  /** Search method */
  search(query: SERPQuery): Promise<SearchResult[]>;
  /** Availability check */
  isAvailable(): Promise<boolean>;
}

/**
 * LM Provider Interface
 * REQ: REQ-DR-CORE-004
 * ADR: ADR-v3.4.0-003
 */
export interface LMProvider {
  /** Generate text from LM */
  generateText(request: LMRequest): Promise<LMResponse>;
}

/**
 * LM Request
 * REQ: REQ-DR-CORE-004
 */
export interface LMRequest {
  /** Messages (conversation history) */
  messages: Array<{ role: 'user' | 'assistant'; content: string }>;
  /** Maximum tokens to generate */
  maxTokens?: number;
  /** Temperature (0-1) */
  temperature?: number;
}

/**
 * LM Response
 * REQ: REQ-DR-CORE-004
 */
export interface LMResponse {
  /** Generated text */
  text: string;
  /** Tokens used */
  tokensUsed: number;
  /** Model name */
  model: string;
}

/**
 * Evaluation Result
 * REQ: REQ-DR-CORE-001
 */
export interface EvaluationResult {
  /** Is the answer definitive? */
  isDefinitive: boolean;
  /** Confidence score (0-1) */
  confidence: number;
  /** Missing aspects */
  missingAspects: string[];
  /** Recommendations for next steps */
  recommendations: string[];
}

/**
 * Answer Action
 * REQ: REQ-DR-CORE-001
 */
export interface AnswerAction {
  /** Answer text */
  answer: string;
  /** Supporting knowledge items */
  supportingKnowledge: KnowledgeItem[];
}

/**
 * Research Metadata
 * Internal use
 */
export interface ResearchMetadata {
  /** Total tokens used */
  totalTokens: number;
  /** Duration in milliseconds */
  durationMs: number;
}

/**
 * Provider Configuration
 * REQ: REQ-DR-CORE-002
 */
export interface ProviderConfig {
  /** Jina AI API Key */
  jinaApiKey?: string;
  /** Brave API Key */
  braveApiKey?: string;
}

/**
 * Cache Entry
 * REQ: REQ-DR-NFR-001
 */
export interface CacheEntry<V> {
  /** Cached value */
  value: V;
  /** Expiration timestamp */
  expiresAt: number;
}
