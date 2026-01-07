/**
 * @fileoverview Attack Pattern Matcher with MITRE ATT&CK Integration
 * @module @nahisaho/musubix-security/intelligence/attack-pattern-matcher
 * 
 * Provides MITRE ATT&CK framework integration, attack pattern recognition,
 * and technique mapping for security analysis.
 */

import type { Vulnerability, SourceLocation } from '../types/index.js';

// ============================================================================
// Types
// ============================================================================

/**
 * MITRE ATT&CK Tactic
 */
export type MitreTactic =
  | 'reconnaissance'
  | 'resource-development'
  | 'initial-access'
  | 'execution'
  | 'persistence'
  | 'privilege-escalation'
  | 'defense-evasion'
  | 'credential-access'
  | 'discovery'
  | 'lateral-movement'
  | 'collection'
  | 'command-and-control'
  | 'exfiltration'
  | 'impact';

/**
 * MITRE ATT&CK Platform
 */
export type MitrePlatform =
  | 'windows'
  | 'macos'
  | 'linux'
  | 'cloud'
  | 'containers'
  | 'network'
  | 'saas'
  | 'iaas'
  | 'office-365'
  | 'azure-ad'
  | 'google-workspace';

/**
 * MITRE ATT&CK Technique
 */
export interface MitreTechnique {
  /** Technique ID (e.g., T1059) */
  id: string;
  /** Technique name */
  name: string;
  /** Description */
  description: string;
  /** Parent tactic(s) */
  tactics: MitreTactic[];
  /** Applicable platforms */
  platforms: MitrePlatform[];
  /** Detection methods */
  detection: string[];
  /** Mitigation strategies */
  mitigations: string[];
  /** Sub-techniques */
  subTechniques?: MitreTechnique[];
  /** Data sources for detection */
  dataSources: string[];
  /** External references */
  references: string[];
}

/**
 * Attack pattern definition
 */
export interface AttackPattern {
  /** Pattern ID */
  id: string;
  /** Pattern name */
  name: string;
  /** Description */
  description: string;
  /** Code patterns (regex) */
  patterns: string[];
  /** Mapped MITRE technique IDs */
  techniques: string[];
  /** Severity */
  severity: 'critical' | 'high' | 'medium' | 'low';
  /** Confidence when matched */
  confidence: number;
  /** Tags */
  tags: string[];
  /** Example code */
  examples?: string[];
}

/**
 * Pattern match result
 */
export interface PatternMatch {
  /** Match ID */
  id: string;
  /** Matched pattern */
  pattern: AttackPattern;
  /** Location in code */
  location: SourceLocation;
  /** Matched code snippet */
  codeSnippet: string;
  /** Match confidence (0-1) */
  confidence: number;
  /** Mapped techniques */
  techniques: MitreTechnique[];
  /** Kill chain phase */
  killChainPhase: string;
  /** Recommendations */
  recommendations: string[];
}

/**
 * Attack chain analysis
 */
export interface AttackChain {
  /** Chain ID */
  id: string;
  /** Chain name */
  name: string;
  /** Involved patterns */
  patterns: PatternMatch[];
  /** Kill chain stages covered */
  killChainStages: string[];
  /** Overall risk score */
  riskScore: number;
  /** Attack narrative */
  narrative: string;
  /** Detection gaps */
  detectionGaps: string[];
  /** Recommended mitigations */
  mitigations: string[];
}

/**
 * Attack Pattern Matcher options
 */
export interface AttackPatternMatcherOptions {
  /** Enable MITRE ATT&CK mapping */
  enableMitreMapping?: boolean;
  /** Minimum confidence threshold */
  minConfidence?: number;
  /** Enable attack chain analysis */
  enableChainAnalysis?: boolean;
  /** Custom patterns */
  customPatterns?: AttackPattern[];
  /** Target platforms */
  platforms?: MitrePlatform[];
}

// ============================================================================
// MITRE ATT&CK Database (Subset)
// ============================================================================

const MITRE_TECHNIQUES: Record<string, MitreTechnique> = {
  'T1059': {
    id: 'T1059',
    name: 'Command and Scripting Interpreter',
    description: 'Adversaries may abuse command and script interpreters to execute commands, scripts, or binaries.',
    tactics: ['execution'],
    platforms: ['windows', 'macos', 'linux'],
    detection: ['Process monitoring', 'Command-line logging', 'Script block logging'],
    mitigations: ['Execution Prevention', 'Disable or Remove Feature or Program'],
    dataSources: ['Command', 'Process', 'Script'],
    references: ['https://attack.mitre.org/techniques/T1059'],
    subTechniques: [
      {
        id: 'T1059.001',
        name: 'PowerShell',
        description: 'Adversaries may abuse PowerShell commands and scripts for execution.',
        tactics: ['execution'],
        platforms: ['windows'],
        detection: ['PowerShell logging', 'Script block logging'],
        mitigations: ['Code Signing', 'Disable or Remove Feature'],
        dataSources: ['Command', 'Process', 'Script'],
        references: ['https://attack.mitre.org/techniques/T1059/001'],
      },
      {
        id: 'T1059.007',
        name: 'JavaScript',
        description: 'Adversaries may abuse JavaScript for execution.',
        tactics: ['execution'],
        platforms: ['windows', 'macos', 'linux'],
        detection: ['Script execution monitoring'],
        mitigations: ['Execution Prevention'],
        dataSources: ['Command', 'Process', 'Script'],
        references: ['https://attack.mitre.org/techniques/T1059/007'],
      },
    ],
  },
  'T1190': {
    id: 'T1190',
    name: 'Exploit Public-Facing Application',
    description: 'Adversaries may attempt to exploit a weakness in an Internet-facing host or system.',
    tactics: ['initial-access'],
    platforms: ['windows', 'linux', 'macos', 'cloud', 'containers'],
    detection: ['Application logs', 'Web Application Firewall logs', 'Network traffic analysis'],
    mitigations: ['Application Isolation', 'Exploit Protection', 'Network Segmentation', 'Update Software', 'Vulnerability Scanning'],
    dataSources: ['Application Log', 'Network Traffic'],
    references: ['https://attack.mitre.org/techniques/T1190'],
  },
  'T1505': {
    id: 'T1505',
    name: 'Server Software Component',
    description: 'Adversaries may abuse legitimate server software components.',
    tactics: ['persistence'],
    platforms: ['windows', 'linux', 'macos'],
    detection: ['File monitoring', 'Process monitoring', 'Application logs'],
    mitigations: ['Audit', 'Code Signing', 'Privileged Account Management'],
    dataSources: ['Application Log', 'File', 'Network Traffic', 'Process'],
    references: ['https://attack.mitre.org/techniques/T1505'],
    subTechniques: [
      {
        id: 'T1505.003',
        name: 'Web Shell',
        description: 'Adversaries may use web shells to persist on a victim system.',
        tactics: ['persistence'],
        platforms: ['windows', 'linux', 'macos'],
        detection: ['File monitoring', 'Network traffic analysis', 'Process monitoring'],
        mitigations: ['Disable or Remove Feature', 'Network Segmentation'],
        dataSources: ['Application Log', 'File', 'Network Traffic', 'Process'],
        references: ['https://attack.mitre.org/techniques/T1505/003'],
      },
    ],
  },
  'T1552': {
    id: 'T1552',
    name: 'Unsecured Credentials',
    description: 'Adversaries may search compromised systems to find and obtain insecurely stored credentials.',
    tactics: ['credential-access'],
    platforms: ['windows', 'linux', 'macos', 'cloud', 'containers'],
    detection: ['File access monitoring', 'Command-line logging'],
    mitigations: ['Active Directory Configuration', 'Encrypt Sensitive Information', 'Password Policies', 'Privileged Account Management'],
    dataSources: ['Command', 'File', 'Process', 'Windows Registry'],
    references: ['https://attack.mitre.org/techniques/T1552'],
    subTechniques: [
      {
        id: 'T1552.001',
        name: 'Credentials In Files',
        description: 'Adversaries may search for credentials in files.',
        tactics: ['credential-access'],
        platforms: ['windows', 'linux', 'macos', 'containers'],
        detection: ['File access monitoring'],
        mitigations: ['Audit', 'Password Policies', 'Restrict File and Directory Permissions'],
        dataSources: ['Command', 'File', 'Process'],
        references: ['https://attack.mitre.org/techniques/T1552/001'],
      },
    ],
  },
  'T1078': {
    id: 'T1078',
    name: 'Valid Accounts',
    description: 'Adversaries may obtain and abuse credentials of existing accounts.',
    tactics: ['defense-evasion', 'persistence', 'privilege-escalation', 'initial-access'],
    platforms: ['windows', 'linux', 'macos', 'cloud', 'containers', 'network'],
    detection: ['Authentication logs', 'User account monitoring'],
    mitigations: ['Account Use Policies', 'Multi-factor Authentication', 'Password Policies', 'Privileged Account Management', 'User Account Management'],
    dataSources: ['Logon Session', 'User Account'],
    references: ['https://attack.mitre.org/techniques/T1078'],
  },
  'T1041': {
    id: 'T1041',
    name: 'Exfiltration Over C2 Channel',
    description: 'Adversaries may steal data by exfiltrating it over an existing command and control channel.',
    tactics: ['exfiltration'],
    platforms: ['windows', 'linux', 'macos'],
    detection: ['Network traffic analysis', 'Command-line logging'],
    mitigations: ['Network Intrusion Prevention', 'Network Segmentation'],
    dataSources: ['Command', 'File', 'Network Traffic'],
    references: ['https://attack.mitre.org/techniques/T1041'],
  },
  'T1055': {
    id: 'T1055',
    name: 'Process Injection',
    description: 'Adversaries may inject code into processes in order to evade process-based defenses.',
    tactics: ['defense-evasion', 'privilege-escalation'],
    platforms: ['windows', 'linux', 'macos'],
    detection: ['Process monitoring', 'OS API execution'],
    mitigations: ['Behavior Prevention on Endpoint', 'Privileged Account Management'],
    dataSources: ['File', 'Module', 'Process'],
    references: ['https://attack.mitre.org/techniques/T1055'],
  },
  'T1185': {
    id: 'T1185',
    name: 'Browser Session Hijacking',
    description: 'Adversaries may take advantage of security vulnerabilities and browser capabilities.',
    tactics: ['collection'],
    platforms: ['windows', 'linux', 'macos'],
    detection: ['Authentication logs', 'Process monitoring'],
    mitigations: ['User Account Management', 'User Training'],
    dataSources: ['Logon Session', 'Process'],
    references: ['https://attack.mitre.org/techniques/T1185'],
  },
  'T1005': {
    id: 'T1005',
    name: 'Data from Local System',
    description: 'Adversaries may search local system sources, such as file systems.',
    tactics: ['collection'],
    platforms: ['windows', 'linux', 'macos'],
    detection: ['Command-line logging', 'File monitoring'],
    mitigations: ['Data Loss Prevention'],
    dataSources: ['Command', 'File', 'Script'],
    references: ['https://attack.mitre.org/techniques/T1005'],
  },
  'T1083': {
    id: 'T1083',
    name: 'File and Directory Discovery',
    description: 'Adversaries may enumerate files and directories.',
    tactics: ['discovery'],
    platforms: ['windows', 'linux', 'macos'],
    detection: ['Command-line logging', 'Process monitoring'],
    mitigations: [],
    dataSources: ['Command', 'Process'],
    references: ['https://attack.mitre.org/techniques/T1083'],
  },
  'T1090': {
    id: 'T1090',
    name: 'Proxy',
    description: 'Adversaries may use a connection proxy to direct network traffic.',
    tactics: ['command-and-control'],
    platforms: ['windows', 'linux', 'macos', 'network'],
    detection: ['Network traffic analysis'],
    mitigations: ['Filter Network Traffic', 'Network Intrusion Prevention', 'SSL/TLS Inspection'],
    dataSources: ['Network Traffic'],
    references: ['https://attack.mitre.org/techniques/T1090'],
  },
  'T1071': {
    id: 'T1071',
    name: 'Application Layer Protocol',
    description: 'Adversaries may communicate using application layer protocols.',
    tactics: ['command-and-control'],
    platforms: ['windows', 'linux', 'macos'],
    detection: ['Network traffic analysis'],
    mitigations: ['Network Intrusion Prevention'],
    dataSources: ['Network Traffic'],
    references: ['https://attack.mitre.org/techniques/T1071'],
  },
  'T1132': {
    id: 'T1132',
    name: 'Data Encoding',
    description: 'Adversaries may encode data to make the content of command and control traffic more difficult to detect.',
    tactics: ['command-and-control'],
    platforms: ['windows', 'linux', 'macos'],
    detection: ['Network traffic analysis'],
    mitigations: ['Network Intrusion Prevention'],
    dataSources: ['Network Traffic'],
    references: ['https://attack.mitre.org/techniques/T1132'],
  },
  'T1203': {
    id: 'T1203',
    name: 'Exploitation for Client Execution',
    description: 'Adversaries may exploit software vulnerabilities in client applications.',
    tactics: ['execution'],
    platforms: ['windows', 'linux', 'macos'],
    detection: ['Application logs', 'Process monitoring'],
    mitigations: ['Application Isolation', 'Exploit Protection', 'Update Software'],
    dataSources: ['Application Log', 'Process'],
    references: ['https://attack.mitre.org/techniques/T1203'],
  },
  'T1496': {
    id: 'T1496',
    name: 'Resource Hijacking',
    description: 'Adversaries may leverage the resources of co-opted systems in order to solve resource intensive problems.',
    tactics: ['impact'],
    platforms: ['windows', 'linux', 'macos', 'containers', 'iaas'],
    detection: ['Process monitoring', 'Network traffic analysis'],
    mitigations: ['Network Intrusion Prevention', 'Resource Management'],
    dataSources: ['Command', 'File', 'Network Traffic', 'Process', 'Sensor Health'],
    references: ['https://attack.mitre.org/techniques/T1496'],
  },
  'T1600': {
    id: 'T1600',
    name: 'Weaken Encryption',
    description: 'Adversaries may compromise a network device encryption key.',
    tactics: ['defense-evasion'],
    platforms: ['network'],
    detection: ['Network traffic analysis', 'File monitoring'],
    mitigations: ['Encryption', 'Multi-factor Authentication'],
    dataSources: ['File', 'Network Traffic'],
    references: ['https://attack.mitre.org/techniques/T1600'],
  },
  'T1040': {
    id: 'T1040',
    name: 'Network Sniffing',
    description: 'Adversaries may sniff network traffic to capture information.',
    tactics: ['credential-access', 'discovery'],
    platforms: ['windows', 'linux', 'macos', 'network'],
    detection: ['Process monitoring', 'Host network interface monitoring'],
    mitigations: ['Encrypt Sensitive Information', 'Multi-factor Authentication'],
    dataSources: ['Command', 'Process'],
    references: ['https://attack.mitre.org/techniques/T1040'],
  },
  'T1110': {
    id: 'T1110',
    name: 'Brute Force',
    description: 'Adversaries may use brute force techniques to gain access to accounts.',
    tactics: ['credential-access'],
    platforms: ['windows', 'linux', 'macos', 'cloud', 'containers', 'network', 'azure-ad', 'office-365', 'saas', 'google-workspace'],
    detection: ['Authentication logs', 'User account monitoring'],
    mitigations: ['Account Use Policies', 'Multi-factor Authentication', 'Password Policies', 'User Account Management'],
    dataSources: ['Application Log', 'User Account'],
    references: ['https://attack.mitre.org/techniques/T1110'],
  },
};

// ============================================================================
// Built-in Attack Patterns
// ============================================================================

const BUILTIN_ATTACK_PATTERNS: AttackPattern[] = [
  // Command Injection
  {
    id: 'ATK-CMD-001',
    name: 'Command Injection via exec/spawn',
    description: 'Direct use of exec/spawn with user input',
    patterns: [
      'exec\\s*\\([^)]*\\$\\{',
      'execSync\\s*\\([^)]*\\+',
      'spawn\\s*\\([^)]*\\$\\{',
      'child_process.*exec',
    ],
    techniques: ['T1059', 'T1203'],
    severity: 'critical',
    confidence: 0.9,
    tags: ['command-injection', 'rce'],
    examples: ['exec(`rm -rf ${userInput}`)'],
  },
  {
    id: 'ATK-CMD-002',
    name: 'Shell Command Construction',
    description: 'Dynamic shell command construction',
    patterns: [
      '/bin/(?:ba)?sh.*-c.*\\$\\{',
      'cmd\\.exe.*\\/c.*\\+',
      'powershell.*-(?:Command|c).*\\$',
    ],
    techniques: ['T1059', 'T1059.001'],
    severity: 'critical',
    confidence: 0.85,
    tags: ['command-injection', 'shell'],
  },
  
  // SQL Injection
  {
    id: 'ATK-SQL-001',
    name: 'SQL Injection via String Concatenation',
    description: 'SQL query built with string concatenation',
    patterns: [
      'SELECT.*FROM.*WHERE.*\\+.*["\']',
      'INSERT\\s+INTO.*VALUES.*\\$\\{',
      'UPDATE.*SET.*=.*\\+.*req\\.',
      'DELETE.*WHERE.*\\+.*input',
    ],
    techniques: ['T1190', 'T1505'],
    severity: 'critical',
    confidence: 0.9,
    tags: ['sql-injection', 'database'],
  },
  {
    id: 'ATK-SQL-002',
    name: 'NoSQL Injection',
    description: 'NoSQL query with user input',
    patterns: [
      '\\.find\\s*\\(\\s*\\{[^}]*\\$where',
      '\\$where.*function',
      'eval\\s*\\([^)]*db\\.',
    ],
    techniques: ['T1190'],
    severity: 'high',
    confidence: 0.8,
    tags: ['nosql-injection', 'mongodb'],
  },
  
  // XSS Patterns
  {
    id: 'ATK-XSS-001',
    name: 'DOM-based XSS',
    description: 'Direct innerHTML assignment',
    patterns: [
      '\\.innerHTML\\s*=',
      '\\.outerHTML\\s*=',
      'document\\.write\\s*\\(',
      'document\\.writeln\\s*\\(',
    ],
    techniques: ['T1059.007', 'T1185'],
    severity: 'high',
    confidence: 0.75,
    tags: ['xss', 'dom'],
  },
  {
    id: 'ATK-XSS-002',
    name: 'React dangerouslySetInnerHTML',
    description: 'Unsafe HTML rendering in React',
    patterns: [
      'dangerouslySetInnerHTML\\s*=\\s*\\{\\{\\s*__html:',
    ],
    techniques: ['T1059.007', 'T1185'],
    severity: 'medium',
    confidence: 0.7,
    tags: ['xss', 'react'],
  },
  
  // Path Traversal
  {
    id: 'ATK-PATH-001',
    name: 'Path Traversal',
    description: 'File path construction with user input',
    patterns: [
      'fs\\.readFile(?:Sync)?\\s*\\([^)]*\\+',
      'path\\.join\\s*\\([^)]*req\\.',
      'path\\.resolve\\s*\\([^)]*user',
      '__dirname.*\\+.*input',
    ],
    techniques: ['T1083', 'T1005'],
    severity: 'high',
    confidence: 0.85,
    tags: ['path-traversal', 'lfi'],
  },
  
  // SSRF
  {
    id: 'ATK-SSRF-001',
    name: 'Server-Side Request Forgery',
    description: 'HTTP request with user-controlled URL',
    patterns: [
      'fetch\\s*\\([^)]*\\$\\{',
      'axios\\.[a-z]+\\s*\\([^)]*\\+',
      'request\\s*\\(\\s*\\{[^}]*url.*\\+',
      'http\\.(?:get|request)\\s*\\([^)]*\\+',
    ],
    techniques: ['T1090', 'T1071'],
    severity: 'high',
    confidence: 0.8,
    tags: ['ssrf', 'network'],
  },
  
  // Credential Exposure
  {
    id: 'ATK-CRED-001',
    name: 'Hardcoded Credentials',
    description: 'Credentials embedded in code',
    patterns: [
      'password\\s*[=:]\\s*["\'][^"\']{8,}["\']',
      'api[_-]?key\\s*[=:]\\s*["\'][^"\']{16,}["\']',
      'secret\\s*[=:]\\s*["\'][^"\']{8,}["\']',
      'token\\s*[=:]\\s*["\'][a-zA-Z0-9_-]{20,}["\']',
    ],
    techniques: ['T1552.001', 'T1078'],
    severity: 'high',
    confidence: 0.7,
    tags: ['credentials', 'secrets'],
  },
  {
    id: 'ATK-CRED-002',
    name: 'AWS Credentials',
    description: 'AWS credentials in code',
    patterns: [
      'AKIA[0-9A-Z]{16}',
      'aws_access_key_id\\s*[=:]',
      'aws_secret_access_key\\s*[=:]',
    ],
    techniques: ['T1552.001', 'T1078'],
    severity: 'critical',
    confidence: 0.95,
    tags: ['aws', 'credentials', 'cloud'],
  },
  
  // Deserialization
  {
    id: 'ATK-DESER-001',
    name: 'Unsafe Deserialization',
    description: 'Dangerous deserialization patterns',
    patterns: [
      'JSON\\.parse\\s*\\(.*req\\.',
      'eval\\s*\\(.*JSON',
      'serialize\\s*\\(.*user',
      'unserialize\\s*\\(',
    ],
    techniques: ['T1059', 'T1055'],
    severity: 'high',
    confidence: 0.75,
    tags: ['deserialization', 'rce'],
  },
  
  // Crypto Weaknesses
  {
    id: 'ATK-CRYPTO-001',
    name: 'Weak Cryptography',
    description: 'Use of weak cryptographic algorithms',
    patterns: [
      'createHash\\s*\\(["\'](?:md5|sha1)["\']\\)',
      'createCipher\\s*\\(["\'](?:des|rc4)',
      'Math\\.random\\s*\\(\\).*(?:key|token|secret|password)',
    ],
    techniques: ['T1600', 'T1040'],
    severity: 'medium',
    confidence: 0.85,
    tags: ['crypto', 'weak-algorithm'],
  },
  
  // Prototype Pollution
  {
    id: 'ATK-PROTO-001',
    name: 'Prototype Pollution',
    description: 'Potential prototype pollution vectors',
    patterns: [
      '\\[\\s*["\']__proto__["\']\\s*\\]',
      '\\[\\s*["\']constructor["\']\\s*\\]\\[\\s*["\']prototype',
      'Object\\.assign\\s*\\([^)]*req\\.',
      '\\.merge\\s*\\([^)]*input',
    ],
    techniques: ['T1059.007'],
    severity: 'high',
    confidence: 0.8,
    tags: ['prototype-pollution', 'javascript'],
  },
  
  // Data Exfiltration
  {
    id: 'ATK-EXFIL-001',
    name: 'Data Exfiltration Pattern',
    description: 'Patterns indicating data exfiltration',
    patterns: [
      'btoa\\s*\\(.*(?:password|secret|key|token)',
      'encodeURIComponent\\s*\\(.*(?:password|secret)',
      'fetch\\s*\\([^)]*\\+.*(?:password|secret|key)',
    ],
    techniques: ['T1041', 'T1132'],
    severity: 'high',
    confidence: 0.7,
    tags: ['exfiltration', 'data-theft'],
  },
  
  // Backdoor Patterns
  {
    id: 'ATK-BACKDOOR-001',
    name: 'Potential Backdoor',
    description: 'Patterns indicating backdoor functionality',
    patterns: [
      'eval\\s*\\(\\s*(?:atob|Buffer\\.from)',
      'Function\\s*\\([^)]*\\)\\s*\\(\\)',
      'require\\s*\\([^)]*\\+.*\\)\\s*\\(',
    ],
    techniques: ['T1059', 'T1505.003'],
    severity: 'critical',
    confidence: 0.75,
    tags: ['backdoor', 'malware'],
  },
];

// Kill Chain Phases
const KILL_CHAIN_PHASES: Record<MitreTactic, string> = {
  'reconnaissance': 'Reconnaissance',
  'resource-development': 'Weaponization',
  'initial-access': 'Delivery',
  'execution': 'Exploitation',
  'persistence': 'Installation',
  'privilege-escalation': 'Installation',
  'defense-evasion': 'Installation',
  'credential-access': 'Installation',
  'discovery': 'Command & Control',
  'lateral-movement': 'Command & Control',
  'collection': 'Actions on Objectives',
  'command-and-control': 'Command & Control',
  'exfiltration': 'Actions on Objectives',
  'impact': 'Actions on Objectives',
};

// ============================================================================
// AttackPatternMatcher Class
// ============================================================================

/**
 * Attack Pattern Matcher with MITRE ATT&CK integration
 */
export class AttackPatternMatcher {
  private options: Required<AttackPatternMatcherOptions>;
  private patterns: Map<string, AttackPattern> = new Map();
  private techniques: Map<string, MitreTechnique> = new Map();

  constructor(options: AttackPatternMatcherOptions = {}) {
    this.options = {
      enableMitreMapping: options.enableMitreMapping ?? true,
      minConfidence: options.minConfidence ?? 0.7,
      enableChainAnalysis: options.enableChainAnalysis ?? true,
      customPatterns: options.customPatterns ?? [],
      platforms: options.platforms ?? ['windows', 'linux', 'macos'],
    };

    // Load built-in patterns
    this.loadBuiltinPatterns();

    // Load custom patterns
    for (const pattern of this.options.customPatterns) {
      this.patterns.set(pattern.id, pattern);
    }

    // Load MITRE techniques
    this.loadMitreTechniques();
  }

  /**
   * Load built-in attack patterns
   */
  private loadBuiltinPatterns(): void {
    for (const pattern of BUILTIN_ATTACK_PATTERNS) {
      this.patterns.set(pattern.id, pattern);
    }
  }

  /**
   * Load MITRE ATT&CK techniques
   */
  private loadMitreTechniques(): void {
    for (const [id, technique] of Object.entries(MITRE_TECHNIQUES)) {
      this.techniques.set(id, technique);
      
      // Also load sub-techniques
      if (technique.subTechniques) {
        for (const sub of technique.subTechniques) {
          this.techniques.set(sub.id, sub);
        }
      }
    }
  }

  /**
   * Add custom pattern
   */
  addPattern(pattern: AttackPattern): void {
    this.patterns.set(pattern.id, pattern);
  }

  /**
   * Remove pattern
   */
  removePattern(patternId: string): boolean {
    return this.patterns.delete(patternId);
  }

  /**
   * Get all patterns
   */
  getPatterns(): AttackPattern[] {
    return Array.from(this.patterns.values());
  }

  /**
   * Get pattern by ID
   */
  getPattern(id: string): AttackPattern | undefined {
    return this.patterns.get(id);
  }

  /**
   * Get MITRE technique by ID
   */
  getTechnique(id: string): MitreTechnique | undefined {
    return this.techniques.get(id);
  }

  /**
   * Get all techniques
   */
  getAllTechniques(): MitreTechnique[] {
    return Array.from(this.techniques.values());
  }

  /**
   * Get techniques by tactic
   */
  getTechniquesByTactic(tactic: MitreTactic): MitreTechnique[] {
    return this.getAllTechniques().filter(t => t.tactics.includes(tactic));
  }

  /**
   * Match code against patterns
   */
  matchCode(code: string, filePath: string): PatternMatch[] {
    const matches: PatternMatch[] = [];
    const lines = code.split('\n');

    for (const pattern of this.patterns.values()) {
      for (const patternStr of pattern.patterns) {
        try {
          const regex = new RegExp(patternStr, 'gi');
          
          for (let lineNum = 0; lineNum < lines.length; lineNum++) {
            const line = lines[lineNum];
            const match = regex.exec(line);
            
            if (match && pattern.confidence >= this.options.minConfidence) {
              // Get mapped techniques
              const techniques = pattern.techniques
                .map(id => this.techniques.get(id))
                .filter((t): t is MitreTechnique => t !== undefined);

              // Determine kill chain phase
              const killChainPhase = techniques.length > 0
                ? KILL_CHAIN_PHASES[techniques[0].tactics[0]]
                : 'Unknown';

              matches.push({
                id: `MATCH-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
                pattern,
                location: {
                  file: filePath,
                  startLine: lineNum + 1,
                  endLine: lineNum + 1,
                  startColumn: match.index,
                  endColumn: match.index + match[0].length,
                },
                codeSnippet: line.trim(),
                confidence: pattern.confidence,
                techniques,
                killChainPhase,
                recommendations: this.generateRecommendations(pattern, techniques),
              });
            }
          }
        } catch {
          // Invalid regex, skip
          continue;
        }
      }
    }

    return matches;
  }

  /**
   * Generate recommendations based on pattern and techniques
   */
  private generateRecommendations(
    pattern: AttackPattern,
    techniques: MitreTechnique[]
  ): string[] {
    const recommendations: string[] = [];

    // Add pattern-specific recommendations
    switch (pattern.id.split('-')[1]) {
      case 'CMD':
        recommendations.push('Avoid using shell commands with user input');
        recommendations.push('Use parameterized commands or libraries');
        recommendations.push('Implement strict input validation');
        break;
      case 'SQL':
        recommendations.push('Use parameterized queries or prepared statements');
        recommendations.push('Implement input validation and sanitization');
        recommendations.push('Use an ORM with built-in escaping');
        break;
      case 'XSS':
        recommendations.push('Use context-aware output encoding');
        recommendations.push('Implement Content Security Policy');
        recommendations.push('Use framework-provided safe rendering methods');
        break;
      case 'PATH':
        recommendations.push('Validate and sanitize file paths');
        recommendations.push('Use path.resolve() with base directory checks');
        recommendations.push('Implement allow-lists for accessible paths');
        break;
      case 'SSRF':
        recommendations.push('Validate and whitelist allowed URLs/domains');
        recommendations.push('Block internal IP ranges');
        recommendations.push('Use URL parsing to prevent bypass attempts');
        break;
      case 'CRED':
        recommendations.push('Move credentials to environment variables');
        recommendations.push('Use a secrets management solution');
        recommendations.push('Implement credential rotation');
        break;
      default:
        recommendations.push('Review and remediate the identified pattern');
    }

    // Add technique-based mitigations
    for (const technique of techniques) {
      for (const mitigation of technique.mitigations.slice(0, 2)) {
        if (!recommendations.includes(mitigation)) {
          recommendations.push(`MITRE Mitigation: ${mitigation}`);
        }
      }
    }

    return recommendations;
  }

  /**
   * Map vulnerability to MITRE ATT&CK
   */
  mapVulnerabilityToMitre(vulnerability: Vulnerability): MitreTechnique[] {
    if (!this.options.enableMitreMapping) {
      return [];
    }

    const typeMapping: Record<string, string[]> = {
      'xss': ['T1059.007', 'T1185'],
      'sql-injection': ['T1190', 'T1505'],
      'command-injection': ['T1059', 'T1203'],
      'path-traversal': ['T1083', 'T1005'],
      'ssrf': ['T1090', 'T1071'],
      'xxe': ['T1005', 'T1083'],
      'deserialization': ['T1059', 'T1055'],
      'hardcoded-secret': ['T1552.001', 'T1078'],
      'weak-crypto': ['T1600', 'T1040'],
      'insecure-auth': ['T1078', 'T1110'],
      'prototype-pollution': ['T1059.007'],
      'open-redirect': ['T1090'],
      'code-injection': ['T1059', 'T1203'],
    };

    const techniqueIds = typeMapping[vulnerability.type] || [];
    return techniqueIds
      .map(id => this.techniques.get(id))
      .filter((t): t is MitreTechnique => t !== undefined);
  }

  /**
   * Analyze attack chain from multiple matches
   */
  analyzeAttackChain(matches: PatternMatch[]): AttackChain | null {
    if (!this.options.enableChainAnalysis || matches.length < 2) {
      return null;
    }

    // Group by kill chain stage
    const stageMap = new Map<string, PatternMatch[]>();
    for (const match of matches) {
      const stage = match.killChainPhase;
      if (!stageMap.has(stage)) {
        stageMap.set(stage, []);
      }
      stageMap.get(stage)!.push(match);
    }

    // Calculate risk score
    let riskScore = 0;
    for (const match of matches) {
      const severityScore = {
        critical: 40,
        high: 30,
        medium: 20,
        low: 10,
      }[match.pattern.severity];
      riskScore += severityScore * match.confidence;
    }

    // Cap at 100
    riskScore = Math.min(100, riskScore);

    // Get kill chain stages covered
    const killChainStages = Array.from(stageMap.keys()).sort();

    // Generate narrative
    const narrative = this.generateAttackNarrative(matches, killChainStages);

    // Identify detection gaps
    const detectionGaps = this.identifyDetectionGaps(matches);

    // Aggregate mitigations
    const mitigations = new Set<string>();
    for (const match of matches) {
      for (const rec of match.recommendations) {
        mitigations.add(rec);
      }
    }

    return {
      id: `CHAIN-${Date.now()}`,
      name: `Attack Chain (${killChainStages.length} stages)`,
      patterns: matches,
      killChainStages,
      riskScore,
      narrative,
      detectionGaps,
      mitigations: Array.from(mitigations),
    };
  }

  /**
   * Generate attack narrative
   */
  private generateAttackNarrative(
    matches: PatternMatch[],
    stages: string[]
  ): string {
    const parts: string[] = [];

    if (stages.includes('Delivery') || stages.includes('Exploitation')) {
      parts.push('Initial access may be gained through');
      const initialPatterns = matches.filter(
        m => m.killChainPhase === 'Delivery' || m.killChainPhase === 'Exploitation'
      );
      parts.push(initialPatterns.map(p => p.pattern.name).join(', '));
    }

    if (stages.includes('Installation')) {
      parts.push('Persistence could be established via');
      const persistPatterns = matches.filter(m => m.killChainPhase === 'Installation');
      parts.push(persistPatterns.map(p => p.pattern.name).join(', '));
    }

    if (stages.includes('Actions on Objectives')) {
      parts.push('Ultimate goals may include');
      const actionPatterns = matches.filter(m => m.killChainPhase === 'Actions on Objectives');
      parts.push(actionPatterns.map(p => p.pattern.name).join(', '));
    }

    return parts.join('. ') + '.';
  }

  /**
   * Identify detection gaps
   */
  private identifyDetectionGaps(matches: PatternMatch[]): string[] {
    const gaps: Set<string> = new Set();
    const allDataSources = new Set<string>();

    for (const match of matches) {
      for (const technique of match.techniques) {
        for (const ds of technique.dataSources) {
          allDataSources.add(ds);
        }
      }
    }

    // Check common detection capabilities
    if (allDataSources.has('Network Traffic')) {
      gaps.add('Ensure network traffic monitoring is in place');
    }
    if (allDataSources.has('Process')) {
      gaps.add('Enable process execution monitoring');
    }
    if (allDataSources.has('Command')) {
      gaps.add('Enable command-line logging');
    }
    if (allDataSources.has('File')) {
      gaps.add('Implement file integrity monitoring');
    }

    return Array.from(gaps);
  }

  /**
   * Get statistics
   */
  getStatistics(): {
    totalPatterns: number;
    byCategory: Record<string, number>;
    bySeverity: Record<string, number>;
    totalTechniques: number;
    byTactic: Record<MitreTactic, number>;
  } {
    const byCategory: Record<string, number> = {};
    const bySeverity: Record<string, number> = {};
    const byTactic: Record<MitreTactic, number> = {} as Record<MitreTactic, number>;

    for (const pattern of this.patterns.values()) {
      const category = pattern.id.split('-')[1];
      byCategory[category] = (byCategory[category] || 0) + 1;
      bySeverity[pattern.severity] = (bySeverity[pattern.severity] || 0) + 1;
    }

    for (const technique of this.techniques.values()) {
      for (const tactic of technique.tactics) {
        byTactic[tactic] = (byTactic[tactic] || 0) + 1;
      }
    }

    return {
      totalPatterns: this.patterns.size,
      byCategory,
      bySeverity,
      totalTechniques: this.techniques.size,
      byTactic,
    };
  }
}

// ============================================================================
// Factory Functions
// ============================================================================

/**
 * Create an AttackPatternMatcher instance
 */
export function createAttackPatternMatcher(
  options?: AttackPatternMatcherOptions
): AttackPatternMatcher {
  return new AttackPatternMatcher(options);
}

/**
 * Quick pattern match
 */
export function quickPatternMatch(
  code: string,
  filePath: string
): PatternMatch[] {
  const matcher = createAttackPatternMatcher();
  return matcher.matchCode(code, filePath);
}

/**
 * Map vulnerability to MITRE techniques
 */
export function mapToMitre(vulnerability: Vulnerability): MitreTechnique[] {
  const matcher = createAttackPatternMatcher();
  return matcher.mapVulnerabilityToMitre(vulnerability);
}

/**
 * Get MITRE technique by ID
 */
export function getMitreTechnique(id: string): MitreTechnique | undefined {
  const matcher = createAttackPatternMatcher();
  return matcher.getTechnique(id);
}
