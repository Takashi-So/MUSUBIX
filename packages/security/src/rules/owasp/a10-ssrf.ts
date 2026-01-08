/**
 * @fileoverview OWASP A10:2021 - Server-Side Request Forgery (SSRF)
 * @module @nahisaho/musubix-security/rules/owasp/a10
 * @trace REQ-SEC-OWASP-010
 */

import type { SecurityRule, RuleContext, RuleFinding, RuleReference } from '../types.js';

/**
 * OWASP A10:2021 - Server-Side Request Forgery (SSRF)
 *
 * Detects:
 * - URL fetching with user input
 * - Missing URL validation
 * - Internal network access risks
 * - Metadata endpoint access
 */
export const owaspA10SSRF: SecurityRule = {
  id: 'owasp-a10-ssrf',
  name: 'OWASP A10:2021 - Server-Side Request Forgery (SSRF)',
  description: 'Detects potential SSRF vulnerabilities where user input controls server-side requests',
  defaultSeverity: 'critical',
  category: 'ssrf',
  owasp: ['A10:2021'],
  cwe: ['918', '441', '611'],
  references: [
    {
      title: 'OWASP A10:2021',
      url: 'https://owasp.org/Top10/A10_2021-Server-Side_Request_Forgery_%28SSRF%29/',
    },
    {
      title: 'CWE-918: Server-Side Request Forgery (SSRF)',
      url: 'https://cwe.mitre.org/data/definitions/918.html',
    },
  ] as RuleReference[],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];

    checkUserControlledURLs(context, findings);
    checkMetadataEndpoints(context, findings);
    checkInternalNetworkAccess(context, findings);
    checkRedirectFollowing(context, findings);
    checkXMLExternalEntities(context, findings);

    return findings;
  },
};

/**
 * Check for user-controlled URLs in fetch/request operations
 */
function checkUserControlledURLs(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const ssrfPatterns = [
    // fetch with user input
    { pattern: /fetch\s*\(\s*(?:req\.(?:body|query|params)\.\w+|url|targetUrl|endpoint)/i, type: 'fetch' },
    { pattern: /fetch\s*\(\s*`[^`]*\$\{req\./i, type: 'fetch with template' },
    // axios with user input
    { pattern: /axios\.(?:get|post|put|delete|patch)\s*\(\s*(?:req\.(?:body|query|params)|url|targetUrl)/i, type: 'axios' },
    { pattern: /axios\s*\(\s*\{[^}]*url\s*:\s*(?:req\.|url|targetUrl)/i, type: 'axios config' },
    // request library
    { pattern: /request\s*\(\s*(?:req\.(?:body|query|params)|url|targetUrl)/i, type: 'request' },
    // got library
    { pattern: /got\s*\(\s*(?:req\.(?:body|query|params)|url|targetUrl)/i, type: 'got' },
    // http/https module
    { pattern: /https?\.(?:get|request)\s*\(\s*(?:req\.(?:body|query|params)|url|targetUrl)/i, type: 'http(s) module' },
    // URL constructor with user input
    { pattern: /new\s+URL\s*\(\s*req\.(?:body|query|params)/i, type: 'URL constructor' },
    // Image loading from user URL
    { pattern: /(?:img|image)\.src\s*=\s*(?:req\.|url|userUrl)/i, type: 'image source' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type } of ssrfPatterns) {
      if (pattern.test(line)) {
        // Check for URL validation
        const surroundingCode = lines.slice(Math.max(0, lineNum - 5), lineNum + 1).join('\n');
        const hasValidation = /(?:validate.*url|allowlist|whitelist|isValidUrl|URL\.parse|new URL)/i.test(surroundingCode);
        const hasAllowlist = /(?:allowedHosts|allowedDomains|whitelist)/i.test(surroundingCode);

        if (!hasValidation && !hasAllowlist) {
          findings.push({
            id: `owasp-a10-url-${findings.length + 1}`,
            ruleId: 'owasp-a10-ssrf',
            severity: 'critical',
            message: `Potential SSRF vulnerability: ${type} with user-controlled URL`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            cwe: ['918'],
            suggestion: {
              description: 'Validate and restrict URLs to allowed domains',
              example: `// Validate URLs with allowlist:
const ALLOWED_HOSTS = ['api.trusted.com', 'cdn.trusted.com'];

function isAllowedUrl(urlString) {
  try {
    const url = new URL(urlString);
    return ALLOWED_HOSTS.includes(url.hostname) && 
           url.protocol === 'https:';
  } catch {
    return false;
  }
}

if (!isAllowedUrl(req.body.url)) {
  return res.status(400).json({ error: 'Invalid URL' });
}`,
            },
          });
        }
        break;
      }
    }
  }
}

/**
 * Check for access to cloud metadata endpoints
 */
function checkMetadataEndpoints(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const metadataPatterns = [
    // AWS metadata
    { pattern: /169\.254\.169\.254/i, cloud: 'AWS', endpoint: 'EC2 metadata' },
    // GCP metadata
    { pattern: /metadata\.google\.internal/i, cloud: 'GCP', endpoint: 'metadata service' },
    { pattern: /169\.254\.169\.254.*computeMetadata/i, cloud: 'GCP', endpoint: 'compute metadata' },
    // Azure metadata
    { pattern: /169\.254\.169\.254.*metadata\/instance/i, cloud: 'Azure', endpoint: 'instance metadata' },
    // Generic internal IPs that might be targeted
    { pattern: /(?:10\.\d+\.\d+\.\d+|172\.(?:1[6-9]|2\d|3[01])\.\d+\.\d+|192\.168\.\d+\.\d+)/i, cloud: 'Private', endpoint: 'internal network' },
    // localhost variants
    { pattern: /(?:localhost|127\.0\.0\.1|0\.0\.0\.0|::1)(?::\d+)?/i, cloud: 'Local', endpoint: 'localhost' },
  ];

  // Check if user input can control these
  const hasUserInput = /(?:req\.(?:body|query|params)|url\s*=|targetUrl|endpoint)/i.test(sourceCode);

  if (!hasUserInput) return;

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, cloud, endpoint } of metadataPatterns) {
      if (pattern.test(line)) {
        // This is more of an informational finding - the real risk is if user input can reach these
        findings.push({
          id: `owasp-a10-metadata-${findings.length + 1}`,
          ruleId: 'owasp-a10-ssrf',
          severity: cloud === 'Private' ? 'high' : 'critical',
          message: `${cloud} ${endpoint} detected - ensure user input cannot access this`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['918'],
          suggestion: {
            description: 'Block access to metadata endpoints and internal networks',
            example: `// Block internal/metadata URLs:
const BLOCKED_HOSTS = [
  /^169\\.254\\.169\\.254$/,
  /^metadata\\.google\\.internal$/,
  /^10\\./,
  /^172\\.(1[6-9]|2\\d|3[01])\\./,
  /^192\\.168\\./,
  /^localhost$/,
  /^127\\./
];

function isBlockedUrl(urlString) {
  const url = new URL(urlString);
  return BLOCKED_HOSTS.some(pattern => pattern.test(url.hostname));
}`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for internal network access patterns
 */
function checkInternalNetworkAccess(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const internalPatterns = [
    // File protocol
    { pattern: /['"`]file:\/\//i, protocol: 'file://', issue: 'Local file access' },
    // gopher protocol
    { pattern: /['"`]gopher:\/\//i, protocol: 'gopher://', issue: 'Gopher protocol (can be used for SSRF attacks)' },
    // dict protocol
    { pattern: /['"`]dict:\/\//i, protocol: 'dict://', issue: 'Dict protocol' },
    // ftp with credentials
    { pattern: /['"`]ftp:\/\/[^@]*@/i, protocol: 'ftp://', issue: 'FTP with credentials in URL' },
    // Internal hostnames
    { pattern: /['"`]https?:\/\/(?:internal|intranet|corp|private|admin)\./i, protocol: 'http(s)', issue: 'Internal hostname pattern' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, protocol, issue } of internalPatterns) {
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a10-internal-${findings.length + 1}`,
          ruleId: 'owasp-a10-ssrf',
          severity: 'high',
          message: `Potential internal access via ${protocol}: ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['918'],
          suggestion: {
            description: 'Restrict allowed protocols and validate URLs',
            example: `// Only allow safe protocols:
const ALLOWED_PROTOCOLS = ['https:'];

function validateUrl(urlString) {
  const url = new URL(urlString);
  if (!ALLOWED_PROTOCOLS.includes(url.protocol)) {
    throw new Error('Protocol not allowed');
  }
  return url;
}`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for unsafe redirect following
 */
function checkRedirectFollowing(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const redirectPatterns = [
    // Follow redirects without limit
    { pattern: /follow.*redirect.*(?:true|unlimited)/i, issue: 'Unlimited redirect following' },
    { pattern: /maxRedirects\s*:\s*(?:-1|Infinity|100|50)/i, issue: 'High redirect limit' },
    // Location header following
    { pattern: /res\.headers\.location/i, issue: 'Manual redirect following' },
    // Open redirect potential
    { pattern: /res\.redirect\s*\(\s*(?:req\.(?:body|query|params)|url|next|returnUrl)/i, issue: 'Open redirect vulnerability' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, issue } of redirectPatterns) {
      if (pattern.test(line)) {
        findings.push({
          id: `owasp-a10-redirect-${findings.length + 1}`,
          ruleId: 'owasp-a10-ssrf',
          severity: issue.includes('Open redirect') ? 'high' : 'medium',
          message: `Unsafe redirect handling: ${issue}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['918', '601'],
          suggestion: {
            description: 'Limit redirects and validate redirect targets',
            example: `// Limit redirects and validate targets:
const response = await fetch(url, {
  redirect: 'manual', // Handle redirects manually
  follow: 0
});

// For user-controlled redirects:
const ALLOWED_REDIRECT_HOSTS = ['mysite.com', 'auth.mysite.com'];

function safeRedirect(url, allowedHosts) {
  const parsed = new URL(url, 'https://mysite.com');
  if (!allowedHosts.includes(parsed.hostname)) {
    return '/';
  }
  return parsed.pathname + parsed.search;
}`,
          },
        });
        break;
      }
    }
  }
}

/**
 * Check for XML External Entity (XXE) vulnerabilities related to SSRF
 */
function checkXMLExternalEntities(context: RuleContext, findings: RuleFinding[]): void {
  const sourceCode = context.sourceCode;
  const lines = sourceCode.split('\n');

  const xxePatterns = [
    // XML parsing without disabling external entities
    { pattern: /xml2js.*parseString|DOMParser\(\)|XMLParser/i, parser: 'XML parser', issue: 'XML parsing - ensure external entities disabled' },
    // libxmljs
    { pattern: /libxmljs.*parseXml/i, parser: 'libxmljs', issue: 'Ensure noent: false, nonet: true' },
    // External entity reference
    { pattern: /<!ENTITY/i, parser: 'XML', issue: 'XML entity declaration detected' },
    // SVG processing (can contain XXE)
    { pattern: /(?:svg|image\/svg\+xml)/i, parser: 'SVG', issue: 'SVG processing may contain XXE risks' },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, parser, issue } of xxePatterns) {
      if (pattern.test(line)) {
        // Check for safe configuration
        const surroundingCode = lines.slice(Math.max(0, lineNum - 3), Math.min(lines.length, lineNum + 4)).join('\n');
        const hasDisabledExternal = /(?:noent|external.*false|disableEntity|NOENT)/i.test(surroundingCode);

        if (!hasDisabledExternal) {
          findings.push({
            id: `owasp-a10-xxe-${findings.length + 1}`,
            ruleId: 'owasp-a10-ssrf',
            severity: 'high',
            message: `XXE/SSRF risk via ${parser}: ${issue}`,
            location: {
              file: context.filePath,
              startLine: lineNum + 1,
              endLine: lineNum + 1,
              startColumn: 0,
              endColumn: line.length,
            },
            cwe: ['611', '918'],
            suggestion: {
              description: 'Disable external entity processing in XML parsers',
              example: `// Disable external entities in XML parsing:
const parser = new xml2js.Parser({
  explicitRoot: false,
  // xml2js is safe by default, but verify configuration
});

// For DOMParser in Node:
const doc = new DOMParser().parseFromString(xml, 'text/xml');

// Validate/sanitize SVG before processing`,
            },
          });
        }
        break;
      }
    }
  }
}

export default owaspA10SSRF;
