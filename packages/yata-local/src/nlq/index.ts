/**
 * Natural Language Query Module for YATA
 *
 * @packageDocumentation
 * @module @nahisaho/yata-local/nlq
 *
 * @see REQ-YL-NLQ-001 - Natural Language Query Support
 */

export {
  NLQueryParser,
  createNLQueryParser,
  type ParsedQuery,
  type NLQueryResult,
  type QueryParserConfig,
  type QueryIntent,
} from './parser.js';

export {
  NLQueryEngine,
  createNLQueryEngine,
  type NLQueryEngineConfig,
} from './engine.js';
