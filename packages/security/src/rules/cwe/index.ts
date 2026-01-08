/**
 * @fileoverview CWE Top 25 Rules Index
 * @module @nahisaho/musubix-security/rules/cwe
 * @trace TSK-RULE-005, TSK-RULE-006
 */

// CWE Top 25 (1-13)
export { cwe787OutOfBoundsWrite } from './cwe-787-oob-write.js';
export { cwe79XSS } from './cwe-79-xss.js';
export { cwe89SQLInjection } from './cwe-89-sql-injection.js';
export { cwe416UseAfterFree } from './cwe-416-use-after-free.js';
export { cwe78CommandInjection } from './cwe-78-command-injection.js';
export { cwe20InputValidation } from './cwe-20-input-validation.js';
export { cwe125OutOfBoundsRead } from './cwe-125-oob-read.js';
export { cwe22PathTraversal } from './cwe-22-path-traversal.js';
export { cwe352CSRF } from './cwe-352-csrf.js';
export { cwe434FileUpload } from './cwe-434-file-upload.js';
export { cwe862MissingAuth } from './cwe-862-missing-auth.js';
export { cwe476NullDeref } from './cwe-476-null-deref.js';
export { cwe287ImproperAuth } from './cwe-287-improper-auth.js';

// CWE Top 25 (14-25)
export { cwe190IntegerOverflow } from './cwe-190-integer-overflow.js';
export { cwe502Deserialization } from './cwe-502-deserialization.js';
export { cwe77CommandInjection } from './cwe-77-command-injection.js';
export { cwe119BufferOverflow } from './cwe-119-buffer-overflow.js';
export { cwe798HardcodedCredentials } from './cwe-798-hardcoded-credentials.js';
export { cwe918SSRF } from './cwe-918-ssrf.js';
export { cwe306MissingAuthCritical } from './cwe-306-missing-auth-critical.js';
export { cwe362RaceCondition } from './cwe-362-race-condition.js';
export { cwe269ImproperPrivilege } from './cwe-269-improper-privilege.js';
export { cwe94CodeInjection } from './cwe-94-code-injection.js';
export { cwe863IncorrectAuth } from './cwe-863-incorrect-auth.js';
export { cwe276DefaultPermissions } from './cwe-276-default-permissions.js';

// Import for array exports (1-13)
import { cwe787OutOfBoundsWrite } from './cwe-787-oob-write.js';
import { cwe79XSS } from './cwe-79-xss.js';
import { cwe89SQLInjection } from './cwe-89-sql-injection.js';
import { cwe416UseAfterFree } from './cwe-416-use-after-free.js';
import { cwe78CommandInjection } from './cwe-78-command-injection.js';
import { cwe20InputValidation } from './cwe-20-input-validation.js';
import { cwe125OutOfBoundsRead } from './cwe-125-oob-read.js';
import { cwe22PathTraversal } from './cwe-22-path-traversal.js';
import { cwe352CSRF } from './cwe-352-csrf.js';
import { cwe434FileUpload } from './cwe-434-file-upload.js';
import { cwe862MissingAuth } from './cwe-862-missing-auth.js';
import { cwe476NullDeref } from './cwe-476-null-deref.js';
import { cwe287ImproperAuth } from './cwe-287-improper-auth.js';

// Import for array exports (14-25)
import { cwe190IntegerOverflow } from './cwe-190-integer-overflow.js';
import { cwe502Deserialization } from './cwe-502-deserialization.js';
import { cwe77CommandInjection } from './cwe-77-command-injection.js';
import { cwe119BufferOverflow } from './cwe-119-buffer-overflow.js';
import { cwe798HardcodedCredentials } from './cwe-798-hardcoded-credentials.js';
import { cwe918SSRF } from './cwe-918-ssrf.js';
import { cwe306MissingAuthCritical } from './cwe-306-missing-auth-critical.js';
import { cwe362RaceCondition } from './cwe-362-race-condition.js';
import { cwe269ImproperPrivilege } from './cwe-269-improper-privilege.js';
import { cwe94CodeInjection } from './cwe-94-code-injection.js';
import { cwe863IncorrectAuth } from './cwe-863-incorrect-auth.js';
import { cwe276DefaultPermissions } from './cwe-276-default-permissions.js';

/**
 * CWE Top 25 Rules (1-13)
 */
export const cweTop25Rules1to13 = [
  cwe787OutOfBoundsWrite,
  cwe79XSS,
  cwe89SQLInjection,
  cwe416UseAfterFree,
  cwe78CommandInjection,
  cwe20InputValidation,
  cwe125OutOfBoundsRead,
  cwe22PathTraversal,
  cwe352CSRF,
  cwe434FileUpload,
  cwe862MissingAuth,
  cwe476NullDeref,
  cwe287ImproperAuth,
];

/**
 * CWE Top 25 Rules (14-25)
 */
export const cweTop25Rules14to25 = [
  cwe190IntegerOverflow,
  cwe502Deserialization,
  cwe77CommandInjection,
  cwe119BufferOverflow,
  cwe798HardcodedCredentials,
  cwe918SSRF,
  cwe306MissingAuthCritical,
  cwe362RaceCondition,
  cwe269ImproperPrivilege,
  cwe94CodeInjection,
  cwe863IncorrectAuth,
  cwe276DefaultPermissions,
];

/**
 * All CWE Top 25 rules
 */
export const cweTop25Rules = [...cweTop25Rules1to13, ...cweTop25Rules14to25];
