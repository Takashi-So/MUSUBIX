/**
 * @fileoverview Vulnerability Model - Define vulnerability patterns
 * @module @nahisaho/musubix-security/variant/model
 * @trace TSK-023, REQ-SEC-VARIANT-001
 */

import type {
  VulnerabilityModel,
  VulnerabilityCategory,
  VulnerabilitySeverity,
  RegexMatcher,
} from '../types/variant.js';

// ============================================================================
// CWE Database
// ============================================================================

/**
 * CWE ID to Name mappings
 */
export const CWE_DATABASE: Record<string, { name: string; description: string }> = {
  'CWE-89': {
    name: 'SQL Injection',
    description: 'Improper Neutralization of Special Elements used in an SQL Command',
  },
  'CWE-79': {
    name: 'Cross-site Scripting (XSS)',
    description: 'Improper Neutralization of Input During Web Page Generation',
  },
  'CWE-78': {
    name: 'OS Command Injection',
    description: 'Improper Neutralization of Special Elements used in an OS Command',
  },
  'CWE-22': {
    name: 'Path Traversal',
    description: 'Improper Limitation of a Pathname to a Restricted Directory',
  },
  'CWE-611': {
    name: 'XXE (XML External Entity)',
    description: 'Improper Restriction of XML External Entity Reference',
  },
  'CWE-918': {
    name: 'Server-Side Request Forgery (SSRF)',
    description: 'Server-Side Request Forgery',
  },
  'CWE-798': {
    name: 'Use of Hard-coded Credentials',
    description: 'Use of Hard-coded Credentials',
  },
  'CWE-502': {
    name: 'Deserialization of Untrusted Data',
    description: 'Deserialization of Untrusted Data',
  },
};

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Create a regex matcher
 */
function regex(pattern: string, flags?: string): RegexMatcher {
  return { type: 'regex', pattern, flags };
}

/**
 * Generate unique ID
 */
let idCounter = 0;
function genId(prefix: string): string {
  return `${prefix}-${++idCounter}`;
}

// ============================================================================
// Built-in Vulnerability Models
// ============================================================================

/**
 * SQL Injection Model
 */
const SQL_INJECTION_MODEL: VulnerabilityModel = {
  id: 'sql-injection',
  name: 'SQL Injection',
  description: 'Detection of SQL injection vulnerabilities where user input is used in SQL queries without proper sanitization',
  cwe: [89],
  cweId: 'CWE-89',
  category: 'injection',
  severity: 'critical',
  languages: ['java', 'javascript', 'typescript', 'go', 'python', 'php'],
  sources: [
    {
      id: genId('src'),
      type: 'function',
      matcher: regex('request\\.getParameter|req\\.query|req\\.body|req\\.params'),
      taintLabel: 'user-input',
      description: 'HTTP request parameters',
    },
    {
      id: genId('src'),
      type: 'function',
      matcher: regex('r\\.URL\\.Query|c\\.Query|c\\.Param|FormValue'),
      taintLabel: 'user-input',
      description: 'Go HTTP request parameters',
    },
    {
      id: genId('src'),
      type: 'annotation',
      matcher: regex('@RequestParam|@PathVariable|@RequestBody'),
      taintLabel: 'user-input',
      description: 'Spring MVC annotations',
    },
  ],
  sinks: [
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('executeQuery|executeUpdate|execute\\(|prepareStatement.*\\+'),
      vulnerableArgs: [0],
      description: 'JDBC query execution',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('db\\.Query|db\\.Exec|db\\.QueryRow|tx\\.Query|tx\\.Exec'),
      vulnerableArgs: [0],
      description: 'Go database query execution',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('query\\(|raw\\(|knex\\.raw|sequelize\\.query'),
      vulnerableArgs: [0],
      description: 'Node.js database query execution',
    },
  ],
  sanitizers: [
    {
      id: genId('san'),
      type: 'function',
      matcher: regex('prepareStatement|setString|setInt|setParameter'),
      description: 'Parameterized queries',
    },
    {
      id: genId('san'),
      type: 'function',
      matcher: regex('escape|sanitize|parameterize'),
      description: 'Input escaping functions',
    },
  ],
  messageTemplate: 'SQL Injection vulnerability: user input flows to SQL query without sanitization',
  references: [
    { type: 'cwe', value: '89', title: 'CWE-89: SQL Injection' },
    { type: 'owasp', value: 'A03:2021', title: 'OWASP Top 10 - Injection' },
  ],
  enabled: true,
  tags: ['injection', 'database', 'critical'],
};

/**
 * XSS Model
 */
const XSS_MODEL: VulnerabilityModel = {
  id: 'xss',
  name: 'Cross-site Scripting (XSS)',
  description: 'Detection of XSS vulnerabilities where user input is rendered in HTML without proper encoding',
  cwe: [79],
  cweId: 'CWE-79',
  category: 'xss',
  severity: 'high',
  languages: ['javascript', 'typescript', 'java', 'go', 'php'],
  sources: [
    {
      id: genId('src'),
      type: 'function',
      matcher: regex('req\\.query|req\\.body|req\\.params|request\\.getParameter'),
      taintLabel: 'user-input',
      description: 'HTTP request parameters',
    },
    {
      id: genId('src'),
      type: 'property',
      matcher: regex('location\\.search|location\\.hash|document\\.URL|document\\.referrer'),
      taintLabel: 'user-input',
      description: 'Browser DOM properties',
    },
  ],
  sinks: [
    {
      id: genId('sink'),
      type: 'property',
      matcher: regex('innerHTML|outerHTML'),
      description: 'DOM innerHTML assignment',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('document\\.write|document\\.writeln'),
      description: 'Document write functions',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('res\\.send|res\\.write|c\\.HTML|c\\.String'),
      vulnerableArgs: [0],
      description: 'HTTP response output',
    },
    {
      id: genId('sink'),
      type: 'property',
      matcher: regex('dangerouslySetInnerHTML|v-html'),
      description: 'Framework unsafe HTML rendering',
    },
  ],
  sanitizers: [
    {
      id: genId('san'),
      type: 'function',
      matcher: regex('escapeHtml|htmlEscape|sanitize|encode|DOMPurify\\.sanitize'),
      description: 'HTML encoding functions',
    },
    {
      id: genId('san'),
      type: 'function',
      matcher: regex('template\\.HTMLEscapeString|html\\.EscapeString'),
      description: 'Go HTML escape functions',
    },
  ],
  messageTemplate: 'XSS vulnerability: user input rendered in HTML without proper encoding',
  references: [
    { type: 'cwe', value: '79', title: 'CWE-79: Cross-site Scripting' },
    { type: 'owasp', value: 'A03:2021', title: 'OWASP Top 10 - Injection' },
  ],
  enabled: true,
  tags: ['xss', 'injection', 'web'],
};

/**
 * Command Injection Model
 */
const COMMAND_INJECTION_MODEL: VulnerabilityModel = {
  id: 'command-injection',
  name: 'OS Command Injection',
  description: 'Detection of command injection vulnerabilities where user input is used in OS commands',
  cwe: [78, 77],
  cweId: 'CWE-78',
  category: 'command-injection',
  severity: 'critical',
  languages: ['java', 'javascript', 'typescript', 'go', 'python', 'php', 'ruby'],
  sources: [
    {
      id: genId('src'),
      type: 'function',
      matcher: regex('req\\.query|req\\.body|req\\.params|request\\.getParameter'),
      taintLabel: 'user-input',
      description: 'HTTP request parameters',
    },
    {
      id: genId('src'),
      type: 'function',
      matcher: regex('c\\.Query|c\\.Param|FormValue'),
      taintLabel: 'user-input',
      description: 'Go HTTP request parameters',
    },
  ],
  sinks: [
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('Runtime\\.getRuntime\\(\\)\\.exec|ProcessBuilder'),
      vulnerableArgs: [0],
      description: 'Java process execution',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('exec\\(|spawn\\(|execSync\\(|spawnSync\\('),
      vulnerableArgs: [0],
      description: 'Node.js child process execution',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('exec\\.Command|os\\.exec'),
      vulnerableArgs: [0],
      description: 'Go command execution',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('os\\.system|subprocess\\.call|subprocess\\.run|subprocess\\.Popen'),
      vulnerableArgs: [0],
      description: 'Python command execution',
    },
  ],
  sanitizers: [
    {
      id: genId('san'),
      type: 'function',
      matcher: regex('shlex\\.quote|escapeshellarg|escapeshellcmd'),
      description: 'Shell argument escaping',
    },
    {
      id: genId('san'),
      type: 'validation',
      matcher: regex('whitelist|allowlist'),
      description: 'Whitelist validation',
    },
  ],
  messageTemplate: 'Command Injection vulnerability: user input used in OS command execution',
  references: [
    { type: 'cwe', value: '78', title: 'CWE-78: OS Command Injection' },
    { type: 'owasp', value: 'A03:2021', title: 'OWASP Top 10 - Injection' },
  ],
  enabled: true,
  tags: ['injection', 'command', 'critical'],
};

/**
 * Path Traversal Model
 */
const PATH_TRAVERSAL_MODEL: VulnerabilityModel = {
  id: 'path-traversal',
  name: 'Path Traversal',
  description: 'Detection of path traversal vulnerabilities where user input is used in file paths',
  cwe: [22, 23],
  cweId: 'CWE-22',
  category: 'path-traversal',
  severity: 'high',
  languages: ['java', 'javascript', 'typescript', 'go', 'python', 'php'],
  sources: [
    {
      id: genId('src'),
      type: 'function',
      matcher: regex('req\\.query|req\\.body|req\\.params|request\\.getParameter'),
      taintLabel: 'user-input',
      description: 'HTTP request parameters',
    },
  ],
  sinks: [
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('fs\\.readFile|fs\\.writeFile|fs\\.readFileSync|fs\\.writeFileSync'),
      vulnerableArgs: [0],
      description: 'Node.js file operations',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('new File\\(|FileInputStream|FileOutputStream|FileReader|FileWriter'),
      vulnerableArgs: [0],
      description: 'Java file operations',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('os\\.Open|ioutil\\.ReadFile|os\\.Create'),
      vulnerableArgs: [0],
      description: 'Go file operations',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('open\\(|file_get_contents|fopen'),
      vulnerableArgs: [0],
      description: 'PHP/Python file operations',
    },
  ],
  sanitizers: [
    {
      id: genId('san'),
      type: 'function',
      matcher: regex('path\\.normalize|path\\.resolve|filepath\\.Clean'),
      description: 'Path normalization',
    },
    {
      id: genId('san'),
      type: 'validation',
      matcher: regex('realpath|canonicalize'),
      description: 'Canonical path validation',
    },
  ],
  messageTemplate: 'Path Traversal vulnerability: user input used in file path without validation',
  references: [
    { type: 'cwe', value: '22', title: 'CWE-22: Path Traversal' },
    { type: 'owasp', value: 'A01:2021', title: 'OWASP Top 10 - Broken Access Control' },
  ],
  enabled: true,
  tags: ['path-traversal', 'file', 'access-control'],
};

/**
 * XXE Model
 */
const XXE_MODEL: VulnerabilityModel = {
  id: 'xxe',
  name: 'XML External Entity (XXE)',
  description: 'Detection of XXE vulnerabilities in XML parsers',
  cwe: [611],
  cweId: 'CWE-611',
  category: 'xxe',
  severity: 'high',
  languages: ['java', 'python', 'php'],
  sources: [
    {
      id: genId('src'),
      type: 'function',
      matcher: regex('req\\.body|request\\.getInputStream'),
      taintLabel: 'xml-input',
      description: 'XML input from request',
    },
  ],
  sinks: [
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('DocumentBuilder\\.parse|SAXParser\\.parse|XMLReader\\.parse'),
      vulnerableArgs: [0],
      description: 'Java XML parsing',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('etree\\.parse|etree\\.fromstring|minidom\\.parse'),
      vulnerableArgs: [0],
      description: 'Python XML parsing',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('simplexml_load_string|DOMDocument->loadXML'),
      vulnerableArgs: [0],
      description: 'PHP XML parsing',
    },
  ],
  sanitizers: [
    {
      id: genId('san'),
      type: 'function',
      matcher: regex('setFeature.*disallow-doctype-decl|FEATURE_SECURE_PROCESSING'),
      description: 'Secure XML parser configuration',
    },
    {
      id: genId('san'),
      type: 'function',
      matcher: regex('defusedxml|libxml_disable_entity_loader'),
      description: 'Secure XML libraries',
    },
  ],
  messageTemplate: 'XXE vulnerability: XML parser accepts external entities',
  references: [
    { type: 'cwe', value: '611', title: 'CWE-611: XXE' },
    { type: 'owasp', value: 'A05:2017', title: 'OWASP - XXE' },
  ],
  enabled: true,
  tags: ['xxe', 'xml', 'injection'],
};

/**
 * SSRF Model
 */
const SSRF_MODEL: VulnerabilityModel = {
  id: 'ssrf',
  name: 'Server-Side Request Forgery (SSRF)',
  description: 'Detection of SSRF vulnerabilities where user input controls server-side HTTP requests',
  cwe: [918],
  cweId: 'CWE-918',
  category: 'ssrf',
  severity: 'high',
  languages: ['java', 'javascript', 'typescript', 'go', 'python', 'php'],
  sources: [
    {
      id: genId('src'),
      type: 'function',
      matcher: regex('req\\.query|req\\.body|req\\.params|request\\.getParameter'),
      taintLabel: 'user-url',
      description: 'User-provided URL',
    },
  ],
  sinks: [
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('fetch\\(|axios\\(|http\\.get|https\\.get|request\\('),
      vulnerableArgs: [0],
      description: 'Node.js HTTP requests',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('HttpURLConnection|HttpClient|RestTemplate'),
      vulnerableArgs: [0],
      description: 'Java HTTP requests',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('http\\.Get|http\\.Post|http\\.NewRequest'),
      vulnerableArgs: [0],
      description: 'Go HTTP requests',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('requests\\.get|urllib\\.request\\.urlopen|curl_exec'),
      vulnerableArgs: [0],
      description: 'Python/PHP HTTP requests',
    },
  ],
  sanitizers: [
    {
      id: genId('san'),
      type: 'validation',
      matcher: regex('allowlist|whitelist|validateUrl'),
      description: 'URL allowlist validation',
    },
  ],
  messageTemplate: 'SSRF vulnerability: user input used in server-side HTTP request URL',
  references: [
    { type: 'cwe', value: '918', title: 'CWE-918: SSRF' },
    { type: 'owasp', value: 'A10:2021', title: 'OWASP Top 10 - SSRF' },
  ],
  enabled: true,
  tags: ['ssrf', 'network', 'injection'],
};

/**
 * Hardcoded Credentials Model
 */
const HARDCODED_CREDENTIALS_MODEL: VulnerabilityModel = {
  id: 'hardcoded-credentials',
  name: 'Hardcoded Credentials',
  description: 'Detection of hardcoded passwords, API keys, and secrets in source code',
  cwe: [798],
  cweId: 'CWE-798',
  category: 'hardcoded-credentials',
  severity: 'high',
  languages: ['java', 'javascript', 'typescript', 'go', 'python', 'php', 'ruby', 'rust'],
  sources: [],
  sinks: [],
  sanitizers: [],
  patterns: [
    /password\s*[=:]\s*['"][^'"]{4,}['"]/i,
    /api[_-]?key\s*[=:]\s*['"][^'"]{8,}['"]/i,
    /secret\s*[=:]\s*['"][^'"]{8,}['"]/i,
    /token\s*[=:]\s*['"][^'"]{16,}['"]/i,
    /AWS[_A-Za-z0-9]{16,}/,
    /AKIA[0-9A-Z]{16}/,
    /sk-[a-zA-Z0-9]{48}/,
    /ghp_[a-zA-Z0-9]{36}/,
    /-----BEGIN (RSA |EC )?PRIVATE KEY-----/,
  ],
  messageTemplate: 'Hardcoded credential detected in source code',
  references: [
    { type: 'cwe', value: '798', title: 'CWE-798: Hardcoded Credentials' },
  ],
  enabled: true,
  tags: ['credentials', 'secrets', 'security'],
};

/**
 * Insecure Deserialization Model
 */
const INSECURE_DESERIALIZATION_MODEL: VulnerabilityModel = {
  id: 'insecure-deserialization',
  name: 'Insecure Deserialization',
  description: 'Detection of insecure deserialization vulnerabilities',
  cwe: [502],
  cweId: 'CWE-502',
  category: 'deserialization',
  severity: 'critical',
  languages: ['java', 'python', 'php', 'ruby'],
  sources: [
    {
      id: genId('src'),
      type: 'function',
      matcher: regex('req\\.body|request\\.getInputStream'),
      taintLabel: 'untrusted-data',
      description: 'Untrusted input data',
    },
  ],
  sinks: [
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('ObjectInputStream\\.readObject|XMLDecoder\\.readObject'),
      vulnerableArgs: [0],
      description: 'Java deserialization',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('pickle\\.load|pickle\\.loads|yaml\\.load'),
      vulnerableArgs: [0],
      description: 'Python deserialization',
    },
    {
      id: genId('sink'),
      type: 'function',
      matcher: regex('unserialize\\(|Marshal\\.load'),
      vulnerableArgs: [0],
      description: 'PHP/Ruby deserialization',
    },
  ],
  sanitizers: [
    {
      id: genId('san'),
      type: 'function',
      matcher: regex('ObjectInputFilter|yaml\\.safe_load|json\\.loads'),
      description: 'Safe deserialization methods',
    },
  ],
  messageTemplate: 'Insecure deserialization vulnerability: untrusted data deserialized without validation',
  references: [
    { type: 'cwe', value: '502', title: 'CWE-502: Deserialization of Untrusted Data' },
    { type: 'owasp', value: 'A08:2017', title: 'OWASP - Insecure Deserialization' },
  ],
  enabled: true,
  tags: ['deserialization', 'injection', 'critical'],
};

// ============================================================================
// Model Collection
// ============================================================================

/**
 * All built-in vulnerability models
 */
export const VULNERABILITY_MODELS: VulnerabilityModel[] = [
  SQL_INJECTION_MODEL,
  XSS_MODEL,
  COMMAND_INJECTION_MODEL,
  PATH_TRAVERSAL_MODEL,
  XXE_MODEL,
  SSRF_MODEL,
  HARDCODED_CREDENTIALS_MODEL,
  INSECURE_DESERIALIZATION_MODEL,
];

// ============================================================================
// Model Manager
// ============================================================================

/**
 * Vulnerability Model Manager
 */
export class VulnerabilityModelManager {
  private models: Map<string, VulnerabilityModel> = new Map();
  private enabledModels: Set<string> = new Set();

  constructor() {
    // Register built-in models
    for (const model of VULNERABILITY_MODELS) {
      this.models.set(model.id, model);
      if (model.enabled) {
        this.enabledModels.add(model.id);
      }
    }
  }

  /**
   * Get all models
   */
  getAllModels(): VulnerabilityModel[] {
    return Array.from(this.models.values());
  }

  /**
   * Get enabled models
   */
  getEnabledModels(): VulnerabilityModel[] {
    return this.getAllModels().filter((m) => this.enabledModels.has(m.id));
  }

  /**
   * Get model by ID
   */
  getModel(id: string): VulnerabilityModel | undefined {
    return this.models.get(id);
  }

  /**
   * Enable a model
   */
  enableModel(id: string): boolean {
    if (this.models.has(id)) {
      this.enabledModels.add(id);
      return true;
    }
    return false;
  }

  /**
   * Disable a model
   */
  disableModel(id: string): boolean {
    return this.enabledModels.delete(id);
  }

  /**
   * Check if model is enabled
   */
  isEnabled(id: string): boolean {
    return this.enabledModels.has(id);
  }

  /**
   * Register a custom model
   */
  registerModel(model: VulnerabilityModel): void {
    this.models.set(model.id, model);
    if (model.enabled) {
      this.enabledModels.add(model.id);
    }
  }

  /**
   * Get models by category
   */
  getModelsByCategory(category: VulnerabilityCategory): VulnerabilityModel[] {
    return this.getAllModels().filter((m) => m.category === category);
  }

  /**
   * Get models by CWE
   */
  getModelsByCWE(cweId: number): VulnerabilityModel[] {
    return this.getAllModels().filter((m) => m.cwe.includes(cweId));
  }

  /**
   * Get models by severity
   */
  getModelsBySeverity(severity: VulnerabilitySeverity): VulnerabilityModel[] {
    return this.getAllModels().filter((m) => m.severity === severity);
  }

  /**
   * Get models supporting a language
   */
  getModelsByLanguage(language: string): VulnerabilityModel[] {
    return this.getAllModels().filter(
      (m) => !m.languages || m.languages.includes(language)
    );
  }
}

/**
 * Create a new model manager
 */
export function createModelManager(): VulnerabilityModelManager {
  return new VulnerabilityModelManager();
}

/**
 * Default model manager instance
 */
export const defaultModelManager = new VulnerabilityModelManager();
