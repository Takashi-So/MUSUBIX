/**
 * @fileoverview OWASP Top 10 Rules Module
 * @module @nahisaho/musubix-security/rules/owasp
 * @trace TSK-RULE-003, TSK-RULE-004
 */

// Import A01-A05 rules
import { owaspA01BrokenAccessControl } from './a01-broken-access-control.js';
import { owaspA02CryptographicFailures } from './a02-cryptographic-failures.js';
import { owaspA03Injection } from './a03-injection.js';
import { owaspA04InsecureDesign } from './a04-insecure-design.js';
import { owaspA05SecurityMisconfiguration } from './a05-security-misconfiguration.js';

// Import A06-A10 rules
import { owaspA06VulnerableComponents } from './a06-vulnerable-components.js';
import { owaspA07AuthFailures } from './a07-auth-failures.js';
import { owaspA08IntegrityFailures } from './a08-integrity-failures.js';
import { owaspA09LoggingFailures } from './a09-logging-failures.js';
import { owaspA10SSRF } from './a10-ssrf.js';

// Re-export individual rules (A01-A05)
export { owaspA01BrokenAccessControl } from './a01-broken-access-control.js';
export { owaspA02CryptographicFailures } from './a02-cryptographic-failures.js';
export { owaspA03Injection } from './a03-injection.js';
export { owaspA04InsecureDesign } from './a04-insecure-design.js';
export { owaspA05SecurityMisconfiguration } from './a05-security-misconfiguration.js';

// Re-export individual rules (A06-A10)
export { owaspA06VulnerableComponents } from './a06-vulnerable-components.js';
export { owaspA07AuthFailures } from './a07-auth-failures.js';
export { owaspA08IntegrityFailures } from './a08-integrity-failures.js';
export { owaspA09LoggingFailures } from './a09-logging-failures.js';
export { owaspA10SSRF } from './a10-ssrf.js';

// All OWASP A01-A05 rules
export const owaspRulesA01A05 = [
  owaspA01BrokenAccessControl,
  owaspA02CryptographicFailures,
  owaspA03Injection,
  owaspA04InsecureDesign,
  owaspA05SecurityMisconfiguration,
];

// All OWASP A06-A10 rules
export const owaspRulesA06A10 = [
  owaspA06VulnerableComponents,
  owaspA07AuthFailures,
  owaspA08IntegrityFailures,
  owaspA09LoggingFailures,
  owaspA10SSRF,
];

// All OWASP Top 10 rules
export const owaspTop10Rules = [
  ...owaspRulesA01A05,
  ...owaspRulesA06A10,
];

// Re-export default for convenience
export { owaspA01BrokenAccessControl as default } from './a01-broken-access-control.js';

