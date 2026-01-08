/**
 * @fileoverview CWE-416: Use After Free
 * @module @nahisaho/musubix-security/rules/cwe/cwe-416-use-after-free
 * @trace TSK-RULE-005
 *
 * Detects:
 * - Resource usage after disposal (streams, handles)
 * - Promise race conditions
 * - Event listener memory leaks
 * - Timer cleanup issues
 * - Database connection pool misuse
 *
 * CWE-416 is #4 in CWE Top 25 2023.
 * Note: JavaScript has garbage collection, so traditional UAF is rare.
 * This rule focuses on logical "use after free" patterns.
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

/**
 * CWE-416 - Use After Free
 */
export const cwe416UseAfterFree: SecurityRule = {
  id: 'cwe-416-use-after-free',
  name: 'CWE-416: Use After Free',
  description:
    'Detects resource usage after disposal patterns including streams, connections, and event handlers',
  defaultSeverity: 'medium',
  category: 'memory-safety',
  tags: ['cwe', 'memory', 'resource', 'disposal', 'security'],
  cwe: ['416'],
  references: [
    {
      title: 'CWE-416: Use After Free',
      url: 'https://cwe.mitre.org/data/definitions/416.html',
    },
    {
      title: 'Node.js Stream Documentation',
      url: 'https://nodejs.org/api/stream.html',
    },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const sourceCode = context.sourceCode;

    checkStreamDisposal(context, sourceCode, findings);
    checkConnectionPoolIssues(context, sourceCode, findings);
    checkEventListenerLeaks(context, sourceCode, findings);
    checkTimerCleanup(context, sourceCode, findings);
    checkPromiseRaceConditions(context, sourceCode, findings);

    return findings;
  },
};

/**
 * Check for stream usage after close/destroy
 */
function checkStreamDisposal(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const streamPatterns = [
    {
      pattern: /\.destroy\s*\(\s*\)[^;]*;[^}]*\.write\s*\(/gi,
      type: 'Write after destroy',
      message: 'Writing to stream after destroy() was called',
      severity: 'high' as const,
    },
    {
      pattern: /\.end\s*\(\s*\)[^;]*;[^}]*\.write\s*\(/gi,
      type: 'Write after end',
      message: 'Writing to stream after end() was called',
      severity: 'medium' as const,
    },
    {
      pattern: /\.close\s*\(\s*\)[^;]*;[^}]*(?:\.read|\.write|\.pipe)\s*\(/gi,
      type: 'Operation after close',
      message: 'Stream operation after close() was called',
      severity: 'medium' as const,
    },
    {
      pattern: /stream\.(?:destroy|end|close)\s*\([^)]*\)\s*;[\s\S]{0,100}stream\./gi,
      type: 'Stream reuse after disposal',
      message: 'Potential stream usage after disposal',
      severity: 'medium' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of streamPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-416-stream-${findings.length + 1}`,
          ruleId: 'cwe-416-use-after-free',
          severity,
          message: `Use After Free - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['416'],
          suggestion: {
            description: 'Check stream state before operations',
            example: `// Check if stream is writable before writing
if (!stream.destroyed && stream.writable) {
  stream.write(data);
}

// Use proper event handlers
stream.on('close', () => {
  // Stream is now closed, don't use it
  stream = null;
});`,
          },
        });
      }
    }
  }
}

/**
 * Check for database connection pool issues
 */
function checkConnectionPoolIssues(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const connectionPatterns = [
    {
      pattern: /\.release\s*\(\s*\)[^;]*;[^}]*(?:\.query|\.execute)\s*\(/gi,
      type: 'Query after release',
      message: 'Database operation after connection release',
      severity: 'high' as const,
    },
    {
      pattern: /connection\.end\s*\(\s*\)[^;]*;[^}]*connection\./gi,
      type: 'Connection use after end',
      message: 'Connection used after end() was called',
      severity: 'high' as const,
    },
    {
      pattern: /pool\.end\s*\(\s*\)[^;]*;[^}]*pool\.(?:query|getConnection)/gi,
      type: 'Pool use after end',
      message: 'Connection pool used after being closed',
      severity: 'high' as const,
    },
    {
      pattern: /client\.close\s*\(\s*\)[^;]*;[^}]*client\./gi,
      type: 'Client use after close',
      message: 'Database client used after close()',
      severity: 'high' as const,
    },
    {
      pattern: /await\s+\w+\.release\s*\(\s*\)[\s\S]{0,50}await\s+\w+\.query/gi,
      type: 'Query after async release',
      message: 'Async query after connection release',
      severity: 'medium' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of connectionPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-416-conn-${findings.length + 1}`,
          ruleId: 'cwe-416-use-after-free',
          severity,
          message: `Use After Free - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['416'],
          suggestion: {
            description: 'Use connection within try-finally or use pooled queries',
            example: `// Use try-finally for proper cleanup
const connection = await pool.getConnection();
try {
  await connection.query('SELECT ...');
} finally {
  connection.release();
}

// Or use pool.query directly (auto-release)
const results = await pool.query('SELECT ...');`,
          },
        });
      }
    }
  }
}

/**
 * Check for event listener memory leaks
 */
function checkEventListenerLeaks(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const listenerPatterns = [
    {
      pattern: /\.on\s*\(\s*['"`]\w+['"`]\s*,\s*(?:function|\([^)]*\)\s*=>)/gi,
      type: 'Event listener without removal',
      message: 'Event listener added - ensure proper cleanup',
      severity: 'info' as const,
    },
    {
      pattern: /\.addListener\s*\(\s*['"`]\w+['"`]\s*,/gi,
      type: 'addListener without removal',
      message: 'addListener used - ensure corresponding removeListener',
      severity: 'info' as const,
    },
    {
      pattern: /setMaxListeners\s*\(\s*0\s*\)/gi,
      type: 'Unlimited listeners',
      message:
        'setMaxListeners(0) disables leak warning - may mask real leaks',
      severity: 'medium' as const,
    },
    {
      pattern:
        /setMaxListeners\s*\(\s*(?:Infinity|Number\.MAX_SAFE_INTEGER)\s*\)/gi,
      type: 'Infinite listeners',
      message:
        'Infinite max listeners disables leak detection',
      severity: 'medium' as const,
    },
    {
      pattern: /\.removeAllListeners\s*\(\s*\)/gi,
      type: 'Remove all listeners',
      message:
        'removeAllListeners() may remove listeners from other modules',
      severity: 'low' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of listenerPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-416-listener-${findings.length + 1}`,
          ruleId: 'cwe-416-use-after-free',
          severity,
          message: `Resource Leak - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['416'],
          suggestion: {
            description: 'Use once() or cleanup listeners properly',
            example: `// Use once() for one-time events
emitter.once('event', handler);

// Store reference for cleanup
const handler = () => { /* ... */ };
emitter.on('event', handler);
// Later:
emitter.off('event', handler);

// Use AbortController for cleanup
const controller = new AbortController();
element.addEventListener('click', handler, { signal: controller.signal });
// Cleanup:
controller.abort();`,
          },
        });
      }
    }
  }
}

/**
 * Check for timer cleanup issues
 */
function checkTimerCleanup(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const timerPatterns = [
    {
      pattern: /setInterval\s*\([^)]+\)/gi,
      type: 'setInterval without clearInterval',
      message:
        'setInterval may cause memory leaks if not cleared',
      severity: 'low' as const,
    },
    {
      pattern: /setTimeout\s*\([^)]+\)(?!\s*;?\s*(?:const|let|var)\s+\w+)/gi,
      type: 'setTimeout without reference',
      message:
        'setTimeout without storing reference cannot be cancelled',
      severity: 'info' as const,
    },
    {
      pattern: /clearTimeout\s*\(\s*\w+\s*\)\s*;[^}]*setTimeout/gi,
      type: 'Timeout cleared then reused',
      message:
        'Timer variable reused after clear - ensure proper assignment',
      severity: 'low' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of timerPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-416-timer-${findings.length + 1}`,
          ruleId: 'cwe-416-use-after-free',
          severity,
          message: `Resource Leak - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['416'],
          suggestion: {
            description: 'Store timer references and clean up properly',
            example: `// Store reference for cleanup
const timerId = setInterval(() => {
  // periodic work
}, 1000);

// Clean up when done
clearInterval(timerId);

// For React components
useEffect(() => {
  const id = setInterval(fn, 1000);
  return () => clearInterval(id);
}, []);`,
          },
        });
      }
    }
  }
}

/**
 * Check for promise race conditions that may cause UAF-like issues
 */
function checkPromiseRaceConditions(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const racePatterns = [
    {
      pattern: /Promise\.race\s*\(\s*\[/gi,
      type: 'Promise.race usage',
      message:
        'Promise.race may leave pending promises - ensure proper cleanup',
      severity: 'info' as const,
    },
    {
      pattern: /\.then\s*\([^)]+\)\s*;[^}]*=\s*null/gi,
      type: 'Nullify after async',
      message:
        'Variable nullified while async operation may still be pending',
      severity: 'medium' as const,
    },
    {
      pattern: /async\s+function[^{]*\{[^}]*this\.\w+\s*=[^}]*await/gi,
      type: 'This assignment after await',
      message:
        'Assignment to this after await may fail if object was disposed',
      severity: 'medium' as const,
    },
    {
      pattern: /unmount|destroy|dispose[^}]*await/gi,
      type: 'Await in cleanup',
      message:
        'Async operation in cleanup function may complete after disposal',
      severity: 'medium' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of racePatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-416-race-${findings.length + 1}`,
          ruleId: 'cwe-416-use-after-free',
          severity,
          message: `Race Condition - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['416'],
          suggestion: {
            description: 'Use cancellation tokens or check component state',
            example: `// Use AbortController for cancellation
const controller = new AbortController();
fetch(url, { signal: controller.signal });
// Cancel on cleanup:
controller.abort();

// Check mounted state in React
useEffect(() => {
  let mounted = true;
  fetchData().then(data => {
    if (mounted) setData(data);
  });
  return () => { mounted = false; };
}, []);`,
          },
        });
      }
    }
  }
}

export default cwe416UseAfterFree;
