/**
 * @fileoverview Database source definitions
 * @module @nahisaho/musubix-security/analysis/sources/database
 * @trace REQ-SEC-001
 */

import type { SourceDefinition } from './types.js';

/**
 * Database sources - query results that may contain user-controlled data
 * @trace REQ-SEC-001
 */
export const DATABASE_SOURCES: readonly SourceDefinition[] = [
  // Prisma ORM
  {
    id: 'SRC-DB-001',
    name: 'Prisma Query Result',
    category: 'database',
    framework: 'prisma',
    patterns: [
      { receiver: 'prisma', method: 'findFirst', taintedReturn: true },
      { receiver: 'prisma', method: 'findUnique', taintedReturn: true },
      { receiver: 'prisma', method: 'findMany', taintedReturn: true },
      { receiver: 'prisma', method: 'findFirstOrThrow', taintedReturn: true },
      { receiver: 'prisma', method: 'findUniqueOrThrow', taintedReturn: true },
      { receiver: 'prisma', method: 'create', taintedReturn: true },
      { receiver: 'prisma', method: 'update', taintedReturn: true },
      { receiver: 'prisma', method: 'upsert', taintedReturn: true },
    ],
    description: 'Prisma ORM query results',
    confidence: 0.7,
    enabled: true,
    tags: ['database', 'prisma', 'orm'],
    relatedCWE: ['CWE-20', 'CWE-79'],
  },

  // TypeORM
  {
    id: 'SRC-DB-010',
    name: 'TypeORM Query Result',
    category: 'database',
    framework: 'typeorm',
    patterns: [
      { method: 'find', taintedReturn: true },
      { method: 'findOne', taintedReturn: true },
      { method: 'findOneBy', taintedReturn: true },
      { method: 'findBy', taintedReturn: true },
      { method: 'findAndCount', taintedReturn: true },
      { method: 'findOneOrFail', taintedReturn: true },
      { method: 'save', taintedReturn: true },
    ],
    description: 'TypeORM query results',
    confidence: 0.7,
    enabled: true,
    tags: ['database', 'typeorm', 'orm'],
    relatedCWE: ['CWE-20', 'CWE-79'],
  },

  // Sequelize
  {
    id: 'SRC-DB-020',
    name: 'Sequelize Query Result',
    category: 'database',
    framework: 'sequelize',
    patterns: [
      { method: 'findAll', taintedReturn: true },
      { method: 'findOne', taintedReturn: true },
      { method: 'findByPk', taintedReturn: true },
      { method: 'findOrCreate', taintedReturn: true },
      { method: 'findAndCountAll', taintedReturn: true },
      { method: 'create', taintedReturn: true },
      { method: 'update', taintedReturn: true },
    ],
    description: 'Sequelize query results',
    confidence: 0.7,
    enabled: true,
    tags: ['database', 'sequelize', 'orm'],
    relatedCWE: ['CWE-20', 'CWE-79'],
  },

  // Drizzle ORM
  {
    id: 'SRC-DB-030',
    name: 'Drizzle Query Result',
    category: 'database',
    framework: 'drizzle',
    patterns: [
      { receiver: 'db', method: 'select', taintedReturn: true },
      { receiver: 'db', method: 'query', taintedReturn: true },
    ],
    description: 'Drizzle ORM query results',
    confidence: 0.7,
    enabled: true,
    tags: ['database', 'drizzle', 'orm'],
    relatedCWE: ['CWE-20', 'CWE-79'],
  },

  // Knex.js
  {
    id: 'SRC-DB-040',
    name: 'Knex Query Result',
    category: 'database',
    framework: 'knex',
    patterns: [
      { receiver: 'knex', method: 'select', taintedReturn: true },
      { receiver: 'knex', method: 'where', taintedReturn: true },
      { receiver: 'knex', method: 'first', taintedReturn: true },
      { receiver: 'knex', method: 'raw', taintedReturn: true },
      { receiver: 'db', method: 'select', taintedReturn: true },
    ],
    description: 'Knex.js query results',
    confidence: 0.7,
    enabled: true,
    tags: ['database', 'knex', 'query-builder'],
    relatedCWE: ['CWE-20', 'CWE-79', 'CWE-89'],
  },

  // MongoDB (Native Driver)
  {
    id: 'SRC-DB-050',
    name: 'MongoDB Query Result',
    category: 'database',
    framework: 'mongodb',
    patterns: [
      { method: 'findOne', taintedReturn: true },
      { method: 'find', taintedReturn: true },
      { method: 'aggregate', taintedReturn: true },
      { method: 'insertOne', taintedReturn: true },
      { method: 'updateOne', taintedReturn: true },
      { method: 'findOneAndUpdate', taintedReturn: true },
      { method: 'findOneAndReplace', taintedReturn: true },
    ],
    description: 'MongoDB native driver query results',
    confidence: 0.7,
    enabled: true,
    tags: ['database', 'mongodb', 'nosql'],
    relatedCWE: ['CWE-20', 'CWE-79', 'CWE-943'],
  },

  // Mongoose
  {
    id: 'SRC-DB-060',
    name: 'Mongoose Query Result',
    category: 'database',
    framework: 'mongoose',
    patterns: [
      { method: 'findById', taintedReturn: true },
      { method: 'findOne', taintedReturn: true },
      { method: 'find', taintedReturn: true },
      { method: 'findByIdAndUpdate', taintedReturn: true },
      { method: 'findOneAndUpdate', taintedReturn: true },
      { method: 'exec', taintedReturn: true },
      { method: 'lean', taintedReturn: true },
    ],
    description: 'Mongoose ODM query results',
    confidence: 0.7,
    enabled: true,
    tags: ['database', 'mongoose', 'mongodb', 'odm'],
    relatedCWE: ['CWE-20', 'CWE-79', 'CWE-943'],
  },

  // Redis
  {
    id: 'SRC-DB-070',
    name: 'Redis Query Result',
    category: 'database',
    framework: 'redis',
    patterns: [
      { receiver: 'redis', method: 'get', taintedReturn: true },
      { receiver: 'redis', method: 'mget', taintedReturn: true },
      { receiver: 'redis', method: 'hget', taintedReturn: true },
      { receiver: 'redis', method: 'hgetall', taintedReturn: true },
      { receiver: 'redis', method: 'lrange', taintedReturn: true },
      { receiver: 'redis', method: 'smembers', taintedReturn: true },
      { receiver: 'client', method: 'get', taintedReturn: true },
    ],
    description: 'Redis cache/database results',
    confidence: 0.7,
    enabled: true,
    tags: ['database', 'redis', 'cache'],
    relatedCWE: ['CWE-20', 'CWE-79'],
  },

  // Raw SQL
  {
    id: 'SRC-DB-080',
    name: 'Raw SQL Query Result',
    category: 'database',
    framework: 'sql',
    patterns: [
      { method: 'query', taintedReturn: true },
      { method: 'execute', taintedReturn: true },
      { receiver: 'db', method: 'query', taintedReturn: true },
      { receiver: 'connection', method: 'query', taintedReturn: true },
      { receiver: 'pool', method: 'query', taintedReturn: true },
    ],
    description: 'Raw SQL query results',
    confidence: 0.7,
    enabled: true,
    tags: ['database', 'sql', 'raw'],
    relatedCWE: ['CWE-20', 'CWE-79', 'CWE-89'],
  },

  // Better-SQLite3
  {
    id: 'SRC-DB-090',
    name: 'Better-SQLite3 Query Result',
    category: 'database',
    framework: 'better-sqlite3',
    patterns: [
      { method: 'get', taintedReturn: true },
      { method: 'all', taintedReturn: true },
      { method: 'iterate', taintedReturn: true },
      { method: 'pluck', taintedReturn: true },
    ],
    description: 'Better-SQLite3 query results',
    confidence: 0.7,
    enabled: true,
    tags: ['database', 'sqlite', 'sql'],
    relatedCWE: ['CWE-20', 'CWE-79', 'CWE-89'],
  },
] as const;
