/**
 * CodeQL Types - SARIF 2.1.0 type definitions
 *
 * Implements: TSK-CODEQL-001, REQ-CODEQL-001
 * @see SARIF 2.1.0 Specification: https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html
 */

/**
 * SARIF 2.1.0 Log format
 */
export interface SARIFLog {
  $schema?: string;
  version: '2.1.0';
  runs: SARIFRun[];
}

/**
 * SARIF Run - single execution of an analysis tool
 */
export interface SARIFRun {
  tool: SARIFTool;
  results?: SARIFResult[];
  taxonomies?: SARIFTaxonomy[];
  invocations?: SARIFInvocation[];
  artifacts?: SARIFArtifact[];
  baselineGuid?: string;
  automationDetails?: SARIFRunAutomationDetails;
}

/**
 * SARIF Tool information
 */
export interface SARIFTool {
  driver: SARIFToolComponent;
  extensions?: SARIFToolComponent[];
}

/**
 * SARIF Tool Component
 */
export interface SARIFToolComponent {
  name: string;
  version?: string;
  semanticVersion?: string;
  informationUri?: string;
  rules?: SARIFRule[];
  notifications?: SARIFReportingDescriptor[];
  taxa?: SARIFReportingDescriptor[];
  supportedTaxonomies?: SARIFToolComponentReference[];
}

/**
 * SARIF Rule definition
 */
export interface SARIFRule {
  id: string;
  name?: string;
  shortDescription?: SARIFMultiformatMessage;
  fullDescription?: SARIFMultiformatMessage;
  help?: SARIFMultiformatMessage;
  helpUri?: string;
  defaultConfiguration?: SARIFReportingConfiguration;
  relationships?: SARIFRelationship[];
  properties?: Record<string, unknown>;
}

/**
 * SARIF Reporting Descriptor (for rules, taxa, notifications)
 */
export interface SARIFReportingDescriptor {
  id: string;
  name?: string;
  shortDescription?: SARIFMultiformatMessage;
  fullDescription?: SARIFMultiformatMessage;
  helpUri?: string;
  properties?: Record<string, unknown>;
}

/**
 * SARIF Result - a single finding
 */
export interface SARIFResult {
  ruleId?: string;
  ruleIndex?: number;
  rule?: SARIFRuleReference;
  kind?: 'notApplicable' | 'pass' | 'fail' | 'review' | 'open' | 'informational';
  level?: 'none' | 'note' | 'warning' | 'error';
  message: SARIFMessage;
  locations?: SARIFLocation[];
  analysisTarget?: SARIFArtifactLocation;
  codeFlows?: SARIFCodeFlow[];
  relatedLocations?: SARIFLocation[];
  fingerprints?: Record<string, string>;
  partialFingerprints?: Record<string, string>;
  properties?: Record<string, unknown>;
  taxa?: SARIFTaxaReference[];
  fixes?: SARIFFix[];
}

/**
 * SARIF Message
 */
export interface SARIFMessage {
  text?: string;
  markdown?: string;
  id?: string;
  arguments?: string[];
}

/**
 * SARIF Multiformat Message
 */
export interface SARIFMultiformatMessage {
  text: string;
  markdown?: string;
}

/**
 * SARIF Location
 */
export interface SARIFLocation {
  id?: number;
  physicalLocation?: SARIFPhysicalLocation;
  logicalLocations?: SARIFLogicalLocation[];
  message?: SARIFMessage;
}

/**
 * SARIF Physical Location
 */
export interface SARIFPhysicalLocation {
  artifactLocation?: SARIFArtifactLocation;
  region?: SARIFRegion;
  contextRegion?: SARIFRegion;
}

/**
 * SARIF Artifact Location
 */
export interface SARIFArtifactLocation {
  uri?: string;
  uriBaseId?: string;
  index?: number;
  description?: SARIFMessage;
}

/**
 * SARIF Region
 */
export interface SARIFRegion {
  startLine?: number;
  startColumn?: number;
  endLine?: number;
  endColumn?: number;
  charOffset?: number;
  charLength?: number;
  byteOffset?: number;
  byteLength?: number;
  snippet?: SARIFArtifactContent;
  message?: SARIFMessage;
}

/**
 * SARIF Artifact Content
 */
export interface SARIFArtifactContent {
  text?: string;
  binary?: string;
  rendered?: SARIFMultiformatMessage;
}

/**
 * SARIF Logical Location
 */
export interface SARIFLogicalLocation {
  name?: string;
  index?: number;
  fullyQualifiedName?: string;
  decoratedName?: string;
  kind?: string;
  parentIndex?: number;
}

/**
 * SARIF Code Flow
 */
export interface SARIFCodeFlow {
  message?: SARIFMessage;
  threadFlows: SARIFThreadFlow[];
}

/**
 * SARIF Thread Flow
 */
export interface SARIFThreadFlow {
  id?: string;
  message?: SARIFMessage;
  locations: SARIFThreadFlowLocation[];
}

/**
 * SARIF Thread Flow Location
 */
export interface SARIFThreadFlowLocation {
  location?: SARIFLocation;
  kinds?: string[];
  nestingLevel?: number;
  executionOrder?: number;
  state?: Record<string, SARIFMultiformatMessage>;
  importance?: 'important' | 'essential' | 'unimportant';
}

/**
 * SARIF Rule Reference
 */
export interface SARIFRuleReference {
  id?: string;
  index?: number;
  guid?: string;
  toolComponent?: SARIFToolComponentReference;
}

/**
 * SARIF Tool Component Reference
 */
export interface SARIFToolComponentReference {
  name?: string;
  index?: number;
  guid?: string;
}

/**
 * SARIF Taxonomy
 */
export interface SARIFTaxonomy {
  name: string;
  guid?: string;
  taxa: SARIFReportingDescriptor[];
  informationUri?: string;
  organization?: string;
  shortDescription?: SARIFMultiformatMessage;
}

/**
 * SARIF Taxa Reference
 */
export interface SARIFTaxaReference {
  id?: string;
  index?: number;
  guid?: string;
  toolComponent?: SARIFToolComponentReference;
}

/**
 * SARIF Relationship
 */
export interface SARIFRelationship {
  target: SARIFReportingDescriptorReference;
  kinds?: string[];
  description?: SARIFMessage;
}

/**
 * SARIF Reporting Descriptor Reference
 */
export interface SARIFReportingDescriptorReference {
  id?: string;
  index?: number;
  guid?: string;
  toolComponent?: SARIFToolComponentReference;
}

/**
 * SARIF Reporting Configuration
 */
export interface SARIFReportingConfiguration {
  enabled?: boolean;
  level?: 'none' | 'note' | 'warning' | 'error';
  rank?: number;
  parameters?: Record<string, unknown>;
}

/**
 * SARIF Invocation
 */
export interface SARIFInvocation {
  commandLine?: string;
  arguments?: string[];
  workingDirectory?: SARIFArtifactLocation;
  environmentVariables?: Record<string, string>;
  startTimeUtc?: string;
  endTimeUtc?: string;
  exitCode?: number;
  exitCodeDescription?: string;
  exitSignalName?: string;
  exitSignalNumber?: number;
  processStartFailureMessage?: string;
  executionSuccessful: boolean;
  toolConfigurationNotifications?: SARIFNotification[];
  toolExecutionNotifications?: SARIFNotification[];
}

/**
 * SARIF Notification
 */
export interface SARIFNotification {
  descriptor?: SARIFReportingDescriptorReference;
  level?: 'none' | 'note' | 'warning' | 'error';
  message: SARIFMessage;
  associatedRule?: SARIFRuleReference;
  exception?: SARIFException;
}

/**
 * SARIF Exception
 */
export interface SARIFException {
  kind?: string;
  message?: string;
  stack?: SARIFStack;
  innerExceptions?: SARIFException[];
}

/**
 * SARIF Stack
 */
export interface SARIFStack {
  message?: SARIFMessage;
  frames: SARIFStackFrame[];
}

/**
 * SARIF Stack Frame
 */
export interface SARIFStackFrame {
  location?: SARIFLocation;
  module?: string;
  threadId?: number;
}

/**
 * SARIF Artifact
 */
export interface SARIFArtifact {
  location?: SARIFArtifactLocation;
  parentIndex?: number;
  length?: number;
  mimeType?: string;
  encoding?: string;
  sourceLanguage?: string;
  hashes?: Record<string, string>;
  lastModifiedTimeUtc?: string;
  roles?: string[];
  contents?: SARIFArtifactContent;
}

/**
 * SARIF Run Automation Details
 */
export interface SARIFRunAutomationDetails {
  description?: SARIFMessage;
  id?: string;
  guid?: string;
  correlationGuid?: string;
}

/**
 * SARIF Fix
 */
export interface SARIFFix {
  description?: SARIFMessage;
  artifactChanges: SARIFArtifactChange[];
}

/**
 * SARIF Artifact Change
 */
export interface SARIFArtifactChange {
  artifactLocation: SARIFArtifactLocation;
  replacements: SARIFReplacement[];
}

/**
 * SARIF Replacement
 */
export interface SARIFReplacement {
  deletedRegion: SARIFRegion;
  insertedContent?: SARIFArtifactContent;
}

// ============== MUSUBIX-specific types ==============

/**
 * Parsed CodeQL finding (normalized for MUSUBIX)
 */
export interface CodeQLFinding {
  /** Unique finding ID */
  id: string;
  
  /** Rule ID from CodeQL */
  ruleId: string;
  
  /** Rule name */
  ruleName?: string;
  
  /** Severity level */
  severity: 'critical' | 'high' | 'medium' | 'low' | 'info';
  
  /** Finding message */
  message: string;
  
  /** File path */
  file: string;
  
  /** Start line */
  startLine?: number;
  
  /** End line */
  endLine?: number;
  
  /** Start column */
  startColumn?: number;
  
  /** End column */
  endColumn?: number;
  
  /** Code snippet */
  snippet?: string;
  
  /** CWE IDs */
  cweIds?: string[];
  
  /** Japanese explanation */
  explanation?: string;
  
  /** Suggested fix */
  fix?: string;
  
  /** Code flow (for taint analysis) */
  codeFlow?: CodeFlowStep[];
  
  /** Raw SARIF result */
  raw?: SARIFResult;
}

/**
 * Code flow step
 */
export interface CodeFlowStep {
  file: string;
  line?: number;
  column?: number;
  message?: string;
  kind?: string;
}

/**
 * CodeQL scan result summary
 */
export interface CodeQLScanResult {
  /** Timestamp */
  timestamp: Date;
  
  /** Tool name and version */
  tool: {
    name: string;
    version?: string;
  };
  
  /** Findings */
  findings: CodeQLFinding[];
  
  /** Statistics */
  stats: {
    total: number;
    bySeverity: Record<string, number>;
    byRule: Record<string, number>;
    filesAffected: number;
  };
  
  /** Scan metadata */
  metadata?: {
    database?: string;
    query?: string;
    duration?: number;
  };
}
