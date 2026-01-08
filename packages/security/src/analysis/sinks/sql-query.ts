/**
 * @fileoverview SQL query sink definitions
 * @module @nahisaho/musubix-security/analysis/sinks/sql-query
 * @trace REQ-SEC-001
 */

import type { SinkDefinition } from './types.js';

/**
 * SQL injection sinks
 * @trace REQ-SEC-001
 */
export const SQL_QUERY_SINKS: readonly SinkDefinition[] = [
  // Generic SQL
  {
    id: 'SNK-SQL-001',
    name: 'Raw SQL Query',
    category: 'sql-query',
    severity: 'critical',
    patterns: [
      { method: 'query', vulnerableArg: 0 },
      { method: 'execute', vulnerableArg: 0 },
      { receiver: 'db', method: 'query', vulnerableArg: 0 },
      { receiver: 'connection', method: 'query', vulnerableArg: 0 },
      { receiver: 'pool', method: 'query', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escape', 'parameterize', 'prepare'],
    description: 'Raw SQL query execution - vulnerable to SQL injection',
    enabled: true,
    tags: ['sql', 'injection', 'database'],
    relatedCWE: ['CWE-89'],
    owaspCategory: 'A03:2021-Injection',
  },

  // MySQL
  {
    id: 'SNK-SQL-010',
    name: 'MySQL Query',
    category: 'sql-query',
    severity: 'critical',
    framework: 'mysql',
    patterns: [
      { receiver: 'mysql', method: 'query', vulnerableArg: 0 },
      { receiver: 'connection', method: 'query', vulnerableArg: 0 },
      { receiver: 'pool', method: 'query', vulnerableArg: 0 },
      {
        importPattern: { module: 'mysql', named: ['createConnection', 'createPool'] },
        method: 'query',
        vulnerableArg: 0,
      },
    ],
    expectedSanitizers: ['escape', 'format', 'escapeId'],
    description: 'MySQL query execution',
    enabled: true,
    tags: ['sql', 'mysql', 'injection'],
    relatedCWE: ['CWE-89'],
    owaspCategory: 'A03:2021-Injection',
  },

  // MySQL2
  {
    id: 'SNK-SQL-011',
    name: 'MySQL2 Query',
    category: 'sql-query',
    severity: 'critical',
    framework: 'mysql2',
    patterns: [
      { receiver: 'mysql', method: 'query', vulnerableArg: 0 },
      { receiver: 'connection', method: 'query', vulnerableArg: 0 },
      { receiver: 'connection', method: 'execute', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escape', 'format', 'prepare'],
    description: 'MySQL2 query execution',
    enabled: true,
    tags: ['sql', 'mysql2', 'injection'],
    relatedCWE: ['CWE-89'],
    owaspCategory: 'A03:2021-Injection',
  },

  // PostgreSQL (pg)
  {
    id: 'SNK-SQL-020',
    name: 'PostgreSQL Query',
    category: 'sql-query',
    severity: 'critical',
    framework: 'pg',
    patterns: [
      { receiver: 'client', method: 'query', vulnerableArg: 0 },
      { receiver: 'pool', method: 'query', vulnerableArg: 0 },
      { receiver: 'pg', method: 'query', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['escape', 'format', 'escapeLiteral', 'escapeIdentifier'],
    description: 'PostgreSQL query execution',
    enabled: true,
    tags: ['sql', 'postgresql', 'pg', 'injection'],
    relatedCWE: ['CWE-89'],
    owaspCategory: 'A03:2021-Injection',
  },

  // SQLite (better-sqlite3)
  {
    id: 'SNK-SQL-030',
    name: 'SQLite Query',
    category: 'sql-query',
    severity: 'critical',
    framework: 'better-sqlite3',
    patterns: [
      { receiver: 'db', method: 'prepare', vulnerableArg: 0 },
      { receiver: 'db', method: 'exec', vulnerableArg: 0 },
      { receiver: 'database', method: 'prepare', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['parameterize'],
    description: 'SQLite query execution',
    enabled: true,
    tags: ['sql', 'sqlite', 'injection'],
    relatedCWE: ['CWE-89'],
    owaspCategory: 'A03:2021-Injection',
  },

  // Knex.js Raw
  {
    id: 'SNK-SQL-040',
    name: 'Knex Raw Query',
    category: 'sql-query',
    severity: 'critical',
    framework: 'knex',
    patterns: [
      { receiver: 'knex', method: 'raw', vulnerableArg: 0 },
      { receiver: 'db', method: 'raw', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['parameterize', 'binding'],
    description: 'Knex.js raw query execution',
    enabled: true,
    tags: ['sql', 'knex', 'raw', 'injection'],
    relatedCWE: ['CWE-89'],
    owaspCategory: 'A03:2021-Injection',
  },

  // TypeORM Raw
  {
    id: 'SNK-SQL-050',
    name: 'TypeORM Raw Query',
    category: 'sql-query',
    severity: 'critical',
    framework: 'typeorm',
    patterns: [
      { method: 'query', vulnerableArg: 0 },
      { receiver: 'entityManager', method: 'query', vulnerableArg: 0 },
      { receiver: 'connection', method: 'query', vulnerableArg: 0 },
      { receiver: 'dataSource', method: 'query', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['parameterize'],
    description: 'TypeORM raw query execution',
    enabled: true,
    tags: ['sql', 'typeorm', 'raw', 'injection'],
    relatedCWE: ['CWE-89'],
    owaspCategory: 'A03:2021-Injection',
  },

  // Prisma Raw
  {
    id: 'SNK-SQL-060',
    name: 'Prisma Raw Query',
    category: 'sql-query',
    severity: 'critical',
    framework: 'prisma',
    patterns: [
      { receiver: 'prisma', method: '$queryRaw', vulnerableArg: 0 },
      { receiver: 'prisma', method: '$executeRaw', vulnerableArg: 0 },
      { receiver: 'prisma', method: '$queryRawUnsafe', vulnerableArg: 0 },
      { receiver: 'prisma', method: '$executeRawUnsafe', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['Prisma.sql', 'template literal'],
    description: 'Prisma raw query execution',
    enabled: true,
    tags: ['sql', 'prisma', 'raw', 'injection'],
    relatedCWE: ['CWE-89'],
    owaspCategory: 'A03:2021-Injection',
  },

  // Sequelize Raw
  {
    id: 'SNK-SQL-070',
    name: 'Sequelize Raw Query',
    category: 'sql-query',
    severity: 'critical',
    framework: 'sequelize',
    patterns: [
      { receiver: 'sequelize', method: 'query', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['parameterize', 'replacements', 'bind'],
    description: 'Sequelize raw query execution',
    enabled: true,
    tags: ['sql', 'sequelize', 'raw', 'injection'],
    relatedCWE: ['CWE-89'],
    owaspCategory: 'A03:2021-Injection',
  },

  // NoSQL Injection (MongoDB)
  {
    id: 'SNK-SQL-080',
    name: 'MongoDB Query Operator',
    category: 'nosql-query',
    severity: 'high',
    framework: 'mongodb',
    patterns: [
      { method: 'find', vulnerableArg: 0 },
      { method: 'findOne', vulnerableArg: 0 },
      { method: 'updateOne', vulnerableArg: 0 },
      { method: 'deleteOne', vulnerableArg: 0 },
      { method: 'aggregate', vulnerableArg: 0 },
    ],
    expectedSanitizers: ['sanitize', 'validateObjectId'],
    description: 'MongoDB query with potential NoSQL injection',
    enabled: true,
    tags: ['nosql', 'mongodb', 'injection'],
    relatedCWE: ['CWE-943'],
    owaspCategory: 'A03:2021-Injection',
  },
] as const;
