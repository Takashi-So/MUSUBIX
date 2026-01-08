/**
 * @fileoverview SQL sanitizer definitions
 * @module @nahisaho/musubix-security/analysis/sanitizers/sql-sanitizers
 * @trace REQ-SEC-001
 */

import type { SanitizerDefinition } from './types.js';

/**
 * SQL injection sanitizers
 * @trace REQ-SEC-001
 */
export const SQL_SANITIZERS: readonly SanitizerDefinition[] = [
  // MySQL escape
  {
    id: 'SAN-SQL-001',
    name: 'escape',
    package: 'mysql',
    protects: ['sql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'MySQL escape function - escapes special characters',
    enabled: true,
    tags: ['sql', 'mysql', 'escape'],
  },
  {
    id: 'SAN-SQL-002',
    name: 'escape',
    package: 'mysql2',
    protects: ['sql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'MySQL2 escape function',
    enabled: true,
    tags: ['sql', 'mysql2', 'escape'],
  },
  {
    id: 'SAN-SQL-003',
    name: 'escapeId',
    aliases: ['escapeIdentifier'],
    package: 'mysql',
    protects: ['sql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'MySQL identifier escape (for column/table names)',
    enabled: true,
    tags: ['sql', 'mysql', 'escape', 'identifier'],
  },
  {
    id: 'SAN-SQL-004',
    name: 'format',
    package: 'mysql',
    protects: ['sql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'MySQL format function - parameterized queries',
    enabled: true,
    tags: ['sql', 'mysql', 'format', 'parameterized'],
  },

  // PostgreSQL escape
  {
    id: 'SAN-SQL-010',
    name: 'escapeLiteral',
    package: 'pg',
    protects: ['sql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'PostgreSQL literal escape',
    enabled: true,
    tags: ['sql', 'postgresql', 'escape'],
  },
  {
    id: 'SAN-SQL-011',
    name: 'escapeIdentifier',
    package: 'pg',
    protects: ['sql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'PostgreSQL identifier escape',
    enabled: true,
    tags: ['sql', 'postgresql', 'escape', 'identifier'],
  },

  // Parameterized queries (generic)
  {
    id: 'SAN-SQL-020',
    name: 'parameterize',
    protects: ['sql-query', 'nosql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Generic parameterized query pattern',
    enabled: true,
    tags: ['sql', 'parameterized', 'generic'],
  },
  {
    id: 'SAN-SQL-021',
    name: 'prepare',
    aliases: ['prepareStatement', 'prepared'],
    protects: ['sql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Prepared statement pattern',
    enabled: true,
    tags: ['sql', 'prepared', 'statement'],
  },
  {
    id: 'SAN-SQL-022',
    name: 'bind',
    aliases: ['binding', 'bindings'],
    protects: ['sql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Parameter binding pattern',
    enabled: true,
    tags: ['sql', 'bind', 'parameterized'],
  },

  // Knex.js
  {
    id: 'SAN-SQL-030',
    name: 'raw',
    namePattern: '^knex\\.raw\\(.*\\?',
    package: 'knex',
    protects: ['sql-query'],
    completeness: 'conditional',
    returnsClean: true,
    description: 'Knex raw with placeholders - safe if placeholders used',
    caveats: 'Only safe when using ? placeholders for values',
    enabled: true,
    tags: ['sql', 'knex', 'raw'],
  },

  // Prisma
  {
    id: 'SAN-SQL-040',
    name: 'sql',
    aliases: ['Prisma.sql'],
    package: '@prisma/client',
    protects: ['sql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Prisma.sql template literal - safe parameterization',
    enabled: true,
    tags: ['sql', 'prisma', 'template'],
  },

  // Sequelize
  {
    id: 'SAN-SQL-050',
    name: 'literal',
    aliases: ['Sequelize.literal'],
    package: 'sequelize',
    protects: ['sql-query'],
    completeness: 'partial',
    returnsClean: true,
    description: 'Sequelize literal - should be used carefully',
    caveats: 'Does not escape, only marks as literal',
    enabled: true,
    tags: ['sql', 'sequelize', 'literal'],
  },
  {
    id: 'SAN-SQL-051',
    name: 'escape',
    package: 'sequelize',
    protects: ['sql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'Sequelize escape function',
    enabled: true,
    tags: ['sql', 'sequelize', 'escape'],
  },

  // SQLite
  {
    id: 'SAN-SQL-060',
    name: 'pluck',
    package: 'better-sqlite3',
    protects: ['sql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'better-sqlite3 pluck - uses prepared statements',
    enabled: true,
    tags: ['sql', 'sqlite', 'prepared'],
  },

  // Generic SQL escape
  {
    id: 'SAN-SQL-070',
    name: 'sqlstring',
    aliases: ['SqlString.escape'],
    package: 'sqlstring',
    protects: ['sql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'sqlstring escape function',
    enabled: true,
    tags: ['sql', 'escape', 'generic'],
  },

  // MongoDB sanitization
  {
    id: 'SAN-SQL-080',
    name: 'sanitize',
    aliases: ['mongo-sanitize'],
    package: 'mongo-sanitize',
    protects: ['nosql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'MongoDB query sanitization',
    enabled: true,
    tags: ['nosql', 'mongodb', 'sanitize'],
  },
  {
    id: 'SAN-SQL-081',
    name: 'ObjectId',
    aliases: ['mongoose.Types.ObjectId'],
    package: 'mongodb',
    protects: ['nosql-query'],
    completeness: 'complete',
    returnsClean: true,
    description: 'MongoDB ObjectId validation',
    enabled: true,
    tags: ['nosql', 'mongodb', 'objectid'],
  },
] as const;
