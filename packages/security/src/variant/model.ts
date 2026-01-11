/**
 * @fileoverview Vulnerability Model - Define vulnerability patterns
 * @module @nahisaho/musubix-security/variant/model
 * @trace TSK-023, REQ-SEC-VARIANT-001
 */

import type {
  VulnerabilityModel,
  SourcePattern,
  SinkPattern,
  SanitizerPattern,
  VulnerabilityCategory,
  BUILTIN_MODELS,
  CWE_MAPPINGS,
} from '../types/variant.js';

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
  'CWE-94': {
    name: 'Code Injection',
    description: 'Improper Control of Generation of Code',
  },
  'CWE-611': {
    name: 'XXE (XML External Entity)',
    description: 'Improper Restriction of XML External Entity Reference',
  },
  'CWE-502': {
    name: 'Deserialization of Untrusted Data',
    description: 'Deserialization of Untrusted Data',
  },
  'CWE-918': {
    name: 'Server-Side Request Forgery (SSRF)',
    description: 'Server-Side Request Forgery',
  },
  'CWE-327': {
    name: 'Use of a Broken or Risky Cryptographic Algorithm',
    description: 'Use of a Broken or Risky Cryptographic Algorithm',
  },
  'CWE-295': {
    name: 'Improper Certificate Validation',
    description: 'Improper Certificate Validation',
  },
  'CWE-200': {
    name: 'Exposure of Sensitive Information',
    description: 'Exposure of Sensitive Information to an Unauthorized Actor',
  },
  'CWE-532': {
    name: 'Information Exposure Through Log Files',
    description: 'Information Exposure Through Log Files',
  },
  'CWE-601': {
    name: 'Open Redirect',
    description: 'URL Redirection to Untrusted Site',
  },
  'CWE-352': {
    name: 'Cross-Site Request Forgery (CSRF)',
    description: 'Cross-Site Request Forgery',
  },
  'CWE-287': {
    name: 'Improper Authentication',
    description: 'Improper Authentication',
  },
  'CWE-798': {
    name: 'Use of Hard-coded Credentials',
    description: 'Use of Hard-coded Credentials',
  },
  'CWE-312': {
    name: 'Cleartext Storage of Sensitive Information',
    description: 'Cleartext Storage of Sensitive Information',
  },
  'CWE-319': {
    name: 'Cleartext Transmission of Sensitive Information',
    description: 'Cleartext Transmission of Sensitive Information',
  },
};

/**
 * Built-in vulnerability models
 */
export const VULNERABILITY_MODELS: VulnerabilityModel[] = [
  // SQL Injection
  {
    id: 'sql-injection',
    name: 'SQL Injection',
    description: 'Detection of SQL injection vulnerabilities',
    cweId: 'CWE-89',
    severity: 'critical',
    category: 'injection',
    sources: [
      {
        type: 'function_call',
        patterns: [
          /request\.getParameter/,
          /request\.getQueryString/,
          /req\.query/,
          /req\.body/,
          /req\.params/,
          /r\.URL\.Query/,
          /c\.Query/,
          /c\.Param/,
          /c\.PostForm/,
          /FormValue/,
        ],
        languages: ['java', 'javascript', 'typescript', 'go'],
      },
      {
        type: 'parameter',
        patterns: [/@RequestParam/, /@PathVariable/, /@RequestBody/],
        languages: ['java'],
      },
    ],
    sinks: [
      {
        type: 'function_call',
        patterns: [
          /executeQuery/,
          /executeUpdate/,
          /execute\(/,
          /prepareStatement.*\+/,
          /createQuery.*\+/,
          /nativeQuery.*\+/,
          /db\.Query\(/,
          /db\.Exec\(/,
          /db\.QueryRow\(/,
          /tx\.Query\(/,
          /tx\.Exec\(/,
          /\.Raw\(/,
          /\.Exec\(/,
        ],
        languages: ['java', 'go'],
        parameterPosition: [0],
      },
      {
        type: 'function_call',
        patterns: [
          /query\(/,
          /execute\(/,
          /raw\(/,
          /knex\.raw/,
          /sequelize\.query/,
          /mongoose\..*\.find.*\{.*\$where/,
        ],
        languages: ['javascript', 'typescript'],
        parameterPosition: [0],
      },
    ],
    sanitizers: [
      {
        type: 'function_call',
        patterns: [
          /prepareStatement\(/,
          /setString\(/,
          /setInt\(/,
          /setParameter\(/,
          /createNativeQuery.*setParameter/,
          /Stmt\.Exec/,
          /Stmt\.Query/,
          /sqlx\.Named/,
        ],
        effect: 'neutralize',
      },
      {
        type: 'function_call',
        patterns: [
          /escape/i,
          /sanitize/i,
          /parameterize/i,
          /bindValue/,
          /bindParam/,
        ],
        effect: 'neutralize',
      },
    ],
    enabled: true,
  },

  // XSS
  {
    id: 'xss',
    name: 'Cross-site Scripting (XSS)',
    description: 'Detection of XSS vulnerabilities',
    cweId: 'CWE-79',
    severity: 'high',
    category: 'injection',
    sources: [
      {
        type: 'function_call',
        patterns: [
          /request\.getParameter/,
          /req\.query/,
          /req\.body/,
          /req\.params/,
          /c\.Query/,
          /c\.Param/,
          /FormValue/,
          /location\.search/,
          /location\.hash/,
          /document\.URL/,
          /document\.referrer/,
        ],
        languages: ['java', 'javascript', 'typescript', 'go'],
      },
    ],
    sinks: [
      {
        type: 'property_access',
        patterns: [/innerHTML/, /outerHTML/, /document\.write/, /document\.writeln/],
        languages: ['javascript', 'typescript'],
      },
      {
        type: 'function_call',
        patterns: [
          /res\.send\(/,
          /res\.write\(/,
          /response\.getWriter\(\)\.print/,
          /out\.print/,
          /c\.HTML\(/,
          /c\.String\(/,
          /w\.Write\(/,
          /fmt\.Fprint.*w/,
          /template\.HTML\(/,
        ],
        languages: ['java', 'javascript', 'typescript', 'go'],
      },
      {
        type: 'function_call',
        patterns: [/dangerouslySetInnerHTML/, /v-html/, /\[innerHTML\]/],
        languages: ['javascript', 'typescript'],
      },
    ],
    sanitizers: [
      {
        type: 'function_call',
        patterns: [
          /escapeHtml/,
          /htmlEncode/,
          /sanitize/,
          /DOMPurify\.sanitize/,
          /xss\(/,
          /html\.EscapeString/,
          /template\.HTMLEscapeString/,
          /StringEscapeUtils\.escapeHtml/,
        ],
        effect: 'neutralize',
      },
      {
        type: 'function_call',
        patterns: [
          /textContent/,
          /innerText/,
          /createTextNode/,
        ],
        effect: 'neutralize',
      },
    ],
    enabled: true,
  },

  // Command Injection
  {
    id: 'command-injection',
    name: 'OS Command Injection',
    description: 'Detection of OS command injection vulnerabilities',
    cweId: 'CWE-78',
    severity: 'critical',
    category: 'injection',
    sources: [
      {
        type: 'function_call',
        patterns: [
          /request\.getParameter/,
          /req\.query/,
          /req\.body/,
          /req\.params/,
          /c\.Query/,
          /FormValue/,
          /process\.argv/,
        ],
        languages: ['java', 'javascript', 'typescript', 'go'],
      },
    ],
    sinks: [
      {
        type: 'function_call',
        patterns: [
          /Runtime\.getRuntime\(\)\.exec/,
          /ProcessBuilder/,
          /child_process\.exec/,
          /child_process\.spawn/,
          /execSync/,
          /spawnSync/,
          /exec\.Command/,
          /os\/exec\.Command/,
          /syscall\.Exec/,
        ],
        languages: ['java', 'javascript', 'typescript', 'go'],
        parameterPosition: [0],
      },
      {
        type: 'function_call',
        patterns: [/eval\(/, /Function\(/, /setTimeout\(.*,.*\+/, /setInterval\(.*,.*\+/],
        languages: ['javascript', 'typescript'],
      },
    ],
    sanitizers: [
      {
        type: 'function_call',
        patterns: [
          /shellescape/i,
          /escapeshellarg/i,
          /escapeshellcmd/i,
          /quote/i,
        ],
        effect: 'neutralize',
      },
    ],
    enabled: true,
  },

  // Path Traversal
  {
    id: 'path-traversal',
    name: 'Path Traversal',
    description: 'Detection of path traversal vulnerabilities',
    cweId: 'CWE-22',
    severity: 'high',
    category: 'injection',
    sources: [
      {
        type: 'function_call',
        patterns: [
          /request\.getParameter/,
          /req\.query/,
          /req\.body/,
          /req\.params/,
          /c\.Query/,
          /c\.Param/,
          /FormValue/,
        ],
        languages: ['java', 'javascript', 'typescript', 'go'],
      },
    ],
    sinks: [
      {
        type: 'function_call',
        patterns: [
          /new File\(/,
          /FileInputStream/,
          /FileOutputStream/,
          /Files\.read/,
          /Files\.write/,
          /fs\.readFile/,
          /fs\.writeFile/,
          /fs\.readFileSync/,
          /fs\.writeFileSync/,
          /os\.Open/,
          /os\.Create/,
          /ioutil\.ReadFile/,
          /ioutil\.WriteFile/,
        ],
        languages: ['java', 'javascript', 'typescript', 'go'],
        parameterPosition: [0],
      },
    ],
    sanitizers: [
      {
        type: 'function_call',
        patterns: [
          /path\.Clean/,
          /filepath\.Clean/,
          /filepath\.Base/,
          /path\.normalize/,
          /path\.basename/,
          /getCanonicalPath/,
          /toRealPath/,
        ],
        effect: 'neutralize',
      },
      {
        type: 'validation',
        patterns: [
          /\.startsWith\(/,
          /strings\.HasPrefix/,
          /\.indexOf\(.*\.\.\//,
        ],
        effect: 'validate',
      },
    ],
    enabled: true,
  },

  // XXE
  {
    id: 'xxe',
    name: 'XML External Entity (XXE)',
    description: 'Detection of XXE vulnerabilities',
    cweId: 'CWE-611',
    severity: 'high',
    category: 'injection',
    sources: [
      {
        type: 'function_call',
        patterns: [
          /request\.getInputStream/,
          /request\.getReader/,
          /req\.body/,
          /r\.Body/,
        ],
        languages: ['java', 'javascript', 'typescript', 'go'],
      },
    ],
    sinks: [
      {
        type: 'function_call',
        patterns: [
          /DocumentBuilder.*parse/,
          /SAXParser.*parse/,
          /XMLReader.*parse/,
          /Unmarshaller.*unmarshal/,
          /TransformerFactory.*newTransformer/,
          /xml\.Unmarshal/,
          /xml\.NewDecoder/,
        ],
        languages: ['java', 'go'],
      },
      {
        type: 'function_call',
        patterns: [
          /xml2js\.parseString/,
          /DOMParser.*parseFromString/,
          /\.parseXML/,
        ],
        languages: ['javascript', 'typescript'],
      },
    ],
    sanitizers: [
      {
        type: 'configuration',
        patterns: [
          /setFeature.*XMLConstants\.FEATURE_SECURE_PROCESSING/,
          /setFeature.*disallow-doctype-decl/,
          /setFeature.*external-general-entities.*false/,
          /setFeature.*external-parameter-entities.*false/,
          /setExpandEntityReferences.*false/,
        ],
        effect: 'neutralize',
      },
    ],
    enabled: true,
  },

  // SSRF
  {
    id: 'ssrf',
    name: 'Server-Side Request Forgery (SSRF)',
    description: 'Detection of SSRF vulnerabilities',
    cweId: 'CWE-918',
    severity: 'high',
    category: 'injection',
    sources: [
      {
        type: 'function_call',
        patterns: [
          /request\.getParameter/,
          /req\.query/,
          /req\.body/,
          /c\.Query/,
          /FormValue/,
        ],
        languages: ['java', 'javascript', 'typescript', 'go'],
      },
    ],
    sinks: [
      {
        type: 'function_call',
        patterns: [
          /URL\(/,
          /HttpURLConnection/,
          /HttpClient.*send/,
          /RestTemplate.*getForObject/,
          /WebClient.*get/,
          /fetch\(/,
          /axios\./,
          /http\.request/,
          /https\.request/,
          /http\.Get/,
          /http\.Post/,
          /http\.NewRequest/,
        ],
        languages: ['java', 'javascript', 'typescript', 'go'],
        parameterPosition: [0],
      },
    ],
    sanitizers: [
      {
        type: 'validation',
        patterns: [
          /URL\.getHost/,
          /url\.parse.*hostname/,
          /allowlist/i,
          /whitelist/i,
        ],
        effect: 'validate',
      },
    ],
    enabled: true,
  },

  // Hardcoded Credentials
  {
    id: 'hardcoded-credentials',
    name: 'Hardcoded Credentials',
    description: 'Detection of hardcoded passwords, API keys, and secrets',
    cweId: 'CWE-798',
    severity: 'high',
    category: 'secrets',
    sources: [], // Not taint-based
    sinks: [],
    sanitizers: [],
    patterns: [
      /password\s*[:=]\s*["'][^"']{8,}["']/i,
      /api[_-]?key\s*[:=]\s*["'][^"']{16,}["']/i,
      /secret\s*[:=]\s*["'][^"']{8,}["']/i,
      /token\s*[:=]\s*["'][^"']{16,}["']/i,
      /auth[_-]?token\s*[:=]\s*["'][^"']{16,}["']/i,
      /private[_-]?key\s*[:=]\s*["']/i,
      /aws[_-]?(access|secret)/i,
      /-----BEGIN (RSA |EC |DSA |OPENSSH )?PRIVATE KEY-----/,
      /ghp_[a-zA-Z0-9]{36}/,  // GitHub Personal Access Token
      /gho_[a-zA-Z0-9]{36}/,  // GitHub OAuth Token
      /sk-[a-zA-Z0-9]{48}/,   // OpenAI API Key
      /AKIA[0-9A-Z]{16}/,     // AWS Access Key
    ],
    enabled: true,
  },

  // Insecure Deserialization
  {
    id: 'insecure-deserialization',
    name: 'Insecure Deserialization',
    description: 'Detection of insecure deserialization vulnerabilities',
    cweId: 'CWE-502',
    severity: 'critical',
    category: 'injection',
    sources: [
      {
        type: 'function_call',
        patterns: [
          /request\.getInputStream/,
          /req\.body/,
          /r\.Body/,
        ],
        languages: ['java', 'javascript', 'typescript', 'go'],
      },
    ],
    sinks: [
      {
        type: 'function_call',
        patterns: [
          /ObjectInputStream.*readObject/,
          /XMLDecoder.*readObject/,
          /Yaml\.load/,
          /SnakeYaml.*load/,
          /JSON\.parse.*eval/,
          /pickle\.load/,
          /yaml\.load.*Loader/,
          /unserialize/,
          /gob\.NewDecoder/,
        ],
        languages: ['java', 'javascript', 'typescript', 'python', 'php', 'go'],
      },
    ],
    sanitizers: [
      {
        type: 'validation',
        patterns: [
          /ObjectInputFilter/,
          /serialVersionUID/,
          /SafeConstructor/,
        ],
        effect: 'validate',
      },
    ],
    enabled: true,
  },
];

/**
 * Vulnerability Model Manager
 */
export class VulnerabilityModelManager {
  private models: Map<string, VulnerabilityModel> = new Map();
  private customModels: Map<string, VulnerabilityModel> = new Map();

  constructor() {
    this.loadBuiltinModels();
  }

  /**
   * Load built-in vulnerability models
   */
  private loadBuiltinModels(): void {
    for (const model of VULNERABILITY_MODELS) {
      this.models.set(model.id, model);
    }
  }

  /**
   * Get all models
   */
  getAllModels(): VulnerabilityModel[] {
    return [...this.models.values(), ...this.customModels.values()];
  }

  /**
   * Get enabled models
   */
  getEnabledModels(): VulnerabilityModel[] {
    return this.getAllModels().filter((m) => m.enabled);
  }

  /**
   * Get model by ID
   */
  getModel(id: string): VulnerabilityModel | undefined {
    return this.models.get(id) ?? this.customModels.get(id);
  }

  /**
   * Get models by category
   */
  getModelsByCategory(category: VulnerabilityCategory): VulnerabilityModel[] {
    return this.getAllModels().filter((m) => m.category === category);
  }

  /**
   * Get models by CWE ID
   */
  getModelsByCWE(cweId: string): VulnerabilityModel[] {
    return this.getAllModels().filter((m) => m.cweId === cweId);
  }

  /**
   * Get models by severity
   */
  getModelsBySeverity(
    severity: 'critical' | 'high' | 'medium' | 'low' | 'info',
  ): VulnerabilityModel[] {
    return this.getAllModels().filter((m) => m.severity === severity);
  }

  /**
   * Get models for language
   */
  getModelsForLanguage(language: string): VulnerabilityModel[] {
    return this.getAllModels().filter((m) => {
      // Check if any source/sink supports this language
      const sourceSupports = m.sources.some(
        (s) => !s.languages || s.languages.includes(language),
      );
      const sinkSupports = m.sinks.some(
        (s) => !s.languages || s.languages.includes(language),
      );
      // Pattern-only models (like hardcoded credentials) apply to all
      const isPatternOnly =
        m.sources.length === 0 && m.sinks.length === 0 && m.patterns;
      return sourceSupports || sinkSupports || isPatternOnly;
    });
  }

  /**
   * Register custom model
   */
  registerModel(model: VulnerabilityModel): void {
    if (this.models.has(model.id)) {
      throw new Error(`Model '${model.id}' already exists as builtin`);
    }
    this.customModels.set(model.id, model);
  }

  /**
   * Unregister custom model
   */
  unregisterModel(id: string): boolean {
    return this.customModels.delete(id);
  }

  /**
   * Enable model
   */
  enableModel(id: string): boolean {
    const model = this.getModel(id);
    if (model) {
      model.enabled = true;
      return true;
    }
    return false;
  }

  /**
   * Disable model
   */
  disableModel(id: string): boolean {
    const model = this.getModel(id);
    if (model) {
      model.enabled = false;
      return true;
    }
    return false;
  }

  /**
   * Get CWE info
   */
  getCWEInfo(cweId: string): { name: string; description: string } | undefined {
    return CWE_DATABASE[cweId];
  }

  /**
   * Export models as JSON
   */
  exportModels(): string {
    return JSON.stringify(
      {
        builtin: [...this.models.values()],
        custom: [...this.customModels.values()],
      },
      null,
      2,
    );
  }

  /**
   * Import custom models from JSON
   */
  importModels(json: string): number {
    const data = JSON.parse(json);
    let count = 0;

    if (data.custom && Array.isArray(data.custom)) {
      for (const model of data.custom) {
        this.customModels.set(model.id, model);
        count++;
      }
    }

    return count;
  }
}

/**
 * Create vulnerability model manager
 */
export function createModelManager(): VulnerabilityModelManager {
  return new VulnerabilityModelManager();
}
