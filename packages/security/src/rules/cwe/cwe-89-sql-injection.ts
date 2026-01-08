/**
 * @fileoverview CWE-89: Improper Neutralization of Special Elements used in an SQL Command (SQL Injection)
 * @module @nahisaho/musubix-security/rules/cwe/cwe-89-sql-injection
 * @trace TSK-RULE-005
 *
 * Detects:
 * - String concatenation in SQL queries
 * - Template literals with user input in SQL
 * - Raw/unsafe query methods
 * - ORM bypass patterns
 * - Stored procedure injection
 *
 * CWE-89 is #3 in CWE Top 25 2023.
 */

import type { SecurityRule, RuleContext, RuleFinding } from '../types.js';

/**
 * CWE-89 - SQL Injection
 */
export const cwe89SQLInjection: SecurityRule = {
  id: 'cwe-89-sql-injection',
  name: 'CWE-89: SQL Injection',
  description:
    'Detects SQL injection vulnerabilities from unsafe query construction',
  defaultSeverity: 'critical',
  category: 'injection',
  tags: ['cwe', 'sql', 'injection', 'database', 'security'],
  owasp: ['A03:2021'],
  cwe: ['89'],
  references: [
    {
      title: 'CWE-89: SQL Injection',
      url: 'https://cwe.mitre.org/data/definitions/89.html',
    },
    {
      title: 'OWASP SQL Injection Prevention',
      url: 'https://cheatsheetseries.owasp.org/cheatsheets/SQL_Injection_Prevention_Cheat_Sheet.html',
    },
  ],

  async analyze(context: RuleContext): Promise<RuleFinding[]> {
    const findings: RuleFinding[] = [];
    const sourceCode = context.sourceCode;

    checkStringConcatenation(context, sourceCode, findings);
    checkTemplateLiterals(context, sourceCode, findings);
    checkRawQueryMethods(context, sourceCode, findings);
    checkORMBypass(context, sourceCode, findings);
    checkDynamicTableColumn(context, sourceCode, findings);

    return findings;
  },
};

/**
 * Check for string concatenation in SQL queries
 */
function checkStringConcatenation(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const concatPatterns = [
    {
      pattern: /['"`]SELECT\s+.*\+\s*\w+/gi,
      type: 'SELECT with concatenation',
      message: 'SQL SELECT query built with string concatenation',
    },
    {
      pattern: /['"`]INSERT\s+INTO\s+.*\+\s*\w+/gi,
      type: 'INSERT with concatenation',
      message: 'SQL INSERT query built with string concatenation',
    },
    {
      pattern: /['"`]UPDATE\s+.*SET\s+.*\+\s*\w+/gi,
      type: 'UPDATE with concatenation',
      message: 'SQL UPDATE query built with string concatenation',
    },
    {
      pattern: /['"`]DELETE\s+FROM\s+.*\+\s*\w+/gi,
      type: 'DELETE with concatenation',
      message: 'SQL DELETE query built with string concatenation',
    },
    {
      pattern: /['"`]WHERE\s+.*\+\s*(?:req\.|params\.|query\.|body\.|user)/gi,
      type: 'WHERE clause with user input',
      message: 'SQL WHERE clause concatenated with user-controlled input',
    },
    {
      pattern: /['"`].*(?:AND|OR)\s+.*\+\s*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'Condition with user input',
      message: 'SQL condition concatenated with user-controlled input',
    },
    {
      pattern: /['"`]ORDER\s+BY\s+.*\+\s*\w+/gi,
      type: 'ORDER BY with concatenation',
      message: 'SQL ORDER BY clause built with string concatenation',
    },
    {
      pattern: /['"`]GROUP\s+BY\s+.*\+\s*\w+/gi,
      type: 'GROUP BY with concatenation',
      message: 'SQL GROUP BY clause built with string concatenation',
    },
    {
      pattern: /['"`]LIMIT\s+.*\+\s*\w+|['"`]OFFSET\s+.*\+\s*\w+/gi,
      type: 'LIMIT/OFFSET with concatenation',
      message: 'SQL LIMIT/OFFSET built with string concatenation',
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message } of concatPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-89-concat-${findings.length + 1}`,
          ruleId: 'cwe-89-sql-injection',
          severity: 'critical',
          message: `SQL Injection - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['89'],
          owasp: ['A03:2021'],
          suggestion: {
            description: 'Use parameterized queries',
            example: `// PostgreSQL with node-pg:
const result = await client.query(
  'SELECT * FROM users WHERE id = $1',
  [userId]
);

// MySQL with mysql2:
const [rows] = await connection.execute(
  'SELECT * FROM users WHERE id = ?',
  [userId]
);`,
          },
        });
      }
    }
  }
}

/**
 * Check for template literals in SQL queries
 */
function checkTemplateLiterals(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const templatePatterns = [
    {
      pattern: /`SELECT\s+[^`]*\$\{[^}]+\}/gi,
      type: 'SELECT with template literal',
      message: 'SQL SELECT query uses template literal interpolation',
    },
    {
      pattern: /`INSERT\s+INTO\s+[^`]*\$\{[^}]+\}/gi,
      type: 'INSERT with template literal',
      message: 'SQL INSERT query uses template literal interpolation',
    },
    {
      pattern: /`UPDATE\s+[^`]*SET[^`]*\$\{[^}]+\}/gi,
      type: 'UPDATE with template literal',
      message: 'SQL UPDATE query uses template literal interpolation',
    },
    {
      pattern: /`DELETE\s+FROM\s+[^`]*\$\{[^}]+\}/gi,
      type: 'DELETE with template literal',
      message: 'SQL DELETE query uses template literal interpolation',
    },
    {
      pattern: /`[^`]*WHERE[^`]*\$\{(?:req\.|params\.|query\.|body\.)[^}]+\}/gi,
      type: 'WHERE with user input interpolation',
      message: 'SQL WHERE clause interpolates user-controlled input',
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message } of templatePatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-89-template-${findings.length + 1}`,
          ruleId: 'cwe-89-sql-injection',
          severity: 'critical',
          message: `SQL Injection - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['89'],
          owasp: ['A03:2021'],
          suggestion: {
            description: 'Use tagged template literals or parameterized queries',
            example: `// Use sql-template-strings or similar:
import sql from 'sql-template-strings';
const query = sql\`SELECT * FROM users WHERE id = \${userId}\`;
// This creates a parameterized query automatically

// Or use ORM:
const user = await User.findOne({ where: { id: userId } });`,
          },
        });
      }
    }
  }
}

/**
 * Check for raw query methods that bypass parameterization
 */
function checkRawQueryMethods(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const rawPatterns = [
    {
      pattern: /\.raw\s*\(\s*['"`].*\+/gi,
      type: 'Raw query with concatenation',
      message: 'ORM raw query method with string concatenation',
      severity: 'critical' as const,
    },
    {
      pattern: /\.raw\s*\(\s*`[^`]*\$\{/gi,
      type: 'Raw query with interpolation',
      message: 'ORM raw query method with template literal interpolation',
      severity: 'critical' as const,
    },
    {
      pattern: /sequelize\.query\s*\(\s*['"`].*\+/gi,
      type: 'Sequelize query with concatenation',
      message: 'Sequelize raw query with string concatenation',
      severity: 'critical' as const,
    },
    {
      pattern: /knex\.raw\s*\(\s*['"`].*\+/gi,
      type: 'Knex raw with concatenation',
      message: 'Knex raw query with string concatenation',
      severity: 'critical' as const,
    },
    {
      pattern: /prisma\.\$executeRaw\s*`[^`]*\$\{/gi,
      type: 'Prisma executeRaw with interpolation',
      message:
        'Prisma $executeRaw with interpolation - use $executeRaw with Prisma.sql',
      severity: 'high' as const,
    },
    {
      pattern: /prisma\.\$queryRaw\s*`[^`]*\$\{/gi,
      type: 'Prisma queryRaw with interpolation',
      message:
        'Prisma $queryRaw with interpolation - ensure using tagged template',
      severity: 'medium' as const,
    },
    {
      pattern: /typeorm.*query\s*\(\s*['"`].*\+/gi,
      type: 'TypeORM query with concatenation',
      message: 'TypeORM query with string concatenation',
      severity: 'critical' as const,
    },
    {
      pattern: /\.exec\s*\(\s*['"`](?:SELECT|INSERT|UPDATE|DELETE).*\+/gi,
      type: 'Database exec with concatenation',
      message: 'Database exec method with string concatenation',
      severity: 'critical' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of rawPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-89-raw-${findings.length + 1}`,
          ruleId: 'cwe-89-sql-injection',
          severity,
          message: `SQL Injection - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['89'],
          owasp: ['A03:2021'],
          suggestion: {
            description: 'Use parameterized raw queries',
            example: `// Sequelize with replacements:
await sequelize.query(
  'SELECT * FROM users WHERE id = :userId',
  { replacements: { userId }, type: QueryTypes.SELECT }
);

// Knex with bindings:
await knex.raw('SELECT * FROM users WHERE id = ?', [userId]);

// Prisma with Prisma.sql:
await prisma.$queryRaw(Prisma.sql\`SELECT * FROM users WHERE id = \${userId}\`);`,
          },
        });
      }
    }
  }
}

/**
 * Check for ORM query builder bypass patterns
 */
function checkORMBypass(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const bypassPatterns = [
    {
      pattern: /\.where\s*\(\s*`[^`]*\$\{/gi,
      type: 'ORM where with interpolation',
      message: 'ORM where clause with template literal interpolation',
      severity: 'high' as const,
    },
    {
      pattern: /\.where\s*\(\s*['"`].*\+/gi,
      type: 'ORM where with concatenation',
      message: 'ORM where clause with string concatenation',
      severity: 'high' as const,
    },
    {
      pattern: /\.orderBy\s*\(\s*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'ORM orderBy with user input',
      message:
        'ORM orderBy with user-controlled input may allow injection',
      severity: 'medium' as const,
    },
    {
      pattern: /\.having\s*\(\s*['"`].*\+/gi,
      type: 'ORM having with concatenation',
      message: 'ORM having clause with string concatenation',
      severity: 'high' as const,
    },
    {
      pattern: /\.whereRaw\s*\(\s*['"`].*\+/gi,
      type: 'whereRaw with concatenation',
      message: 'whereRaw with string concatenation bypasses parameterization',
      severity: 'critical' as const,
    },
    {
      pattern: /Sequelize\.literal\s*\(\s*['"`].*\+/gi,
      type: 'Sequelize.literal with concatenation',
      message: 'Sequelize.literal with concatenation allows raw SQL',
      severity: 'critical' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of bypassPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-89-orm-${findings.length + 1}`,
          ruleId: 'cwe-89-sql-injection',
          severity,
          message: `SQL Injection - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['89'],
          owasp: ['A03:2021'],
          suggestion: {
            description: 'Use ORM query builder methods safely',
            example: `// Knex where with object:
await knex('users').where({ id: userId });

// Sequelize findOne:
await User.findOne({ where: { id: userId } });

// For dynamic columns, whitelist allowed values:
const allowedColumns = ['name', 'date', 'id'];
const column = allowedColumns.includes(sortBy) ? sortBy : 'id';
await knex('users').orderBy(column);`,
          },
        });
      }
    }
  }
}

/**
 * Check for dynamic table/column name injection
 */
function checkDynamicTableColumn(
  context: RuleContext,
  sourceCode: string,
  findings: RuleFinding[]
): void {
  const lines = sourceCode.split('\n');

  const dynamicPatterns = [
    {
      pattern: /['"`]SELECT\s+\*\s+FROM\s+['"`]\s*\+\s*\w+/gi,
      type: 'Dynamic table name',
      message: 'Table name built from variable may allow injection',
      severity: 'high' as const,
    },
    {
      pattern: /`SELECT\s+\*\s+FROM\s+\$\{/gi,
      type: 'Interpolated table name',
      message: 'Table name from template interpolation may allow injection',
      severity: 'high' as const,
    },
    {
      pattern: /['"`]SELECT\s+['"`]\s*\+\s*\w+\s*\+\s*['"`]\s+FROM/gi,
      type: 'Dynamic column selection',
      message: 'Column name built from variable may allow injection',
      severity: 'medium' as const,
    },
    {
      pattern: /\.from\s*\(\s*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'ORM from with user input',
      message: 'Table name from user input in ORM query',
      severity: 'critical' as const,
    },
    {
      pattern: /\.into\s*\(\s*(?:req\.|params\.|query\.|body\.)/gi,
      type: 'ORM into with user input',
      message: 'Table name from user input in ORM insert',
      severity: 'critical' as const,
    },
  ];

  for (let lineNum = 0; lineNum < lines.length; lineNum++) {
    const line = lines[lineNum];

    for (const { pattern, type, message, severity } of dynamicPatterns) {
      pattern.lastIndex = 0;
      if (pattern.test(line)) {
        findings.push({
          id: `cwe-89-dynamic-${findings.length + 1}`,
          ruleId: 'cwe-89-sql-injection',
          severity,
          message: `SQL Injection - ${type}: ${message}`,
          location: {
            file: context.filePath,
            startLine: lineNum + 1,
            endLine: lineNum + 1,
            startColumn: 0,
            endColumn: line.length,
          },
          cwe: ['89'],
          owasp: ['A03:2021'],
          suggestion: {
            description: 'Whitelist allowed table and column names',
            example: `// Whitelist allowed tables:
const allowedTables = ['users', 'products', 'orders'];
if (!allowedTables.includes(tableName)) {
  throw new Error('Invalid table name');
}

// Use identifier escaping:
const escapedTable = connection.escapeId(tableName);

// Or use ORM model mapping:
const models = { users: User, products: Product };
const Model = models[tableName];
if (!Model) throw new Error('Invalid model');
await Model.findAll();`,
          },
        });
      }
    }
  }
}

export default cwe89SQLInjection;
