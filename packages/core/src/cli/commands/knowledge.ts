/**
 * Knowledge CLI Commands
 * 
 * CLI interface for Git-Native Knowledge Graph operations
 * 
 * @packageDocumentation
 * @module cli/commands/knowledge
 */

import type { Command } from 'commander';
import * as path from 'node:path';
import {
  createKnowledgeStore,
  KnowledgeStore,
  Entity,
  Relation,
  EntityType,
  RelationType,
} from '@musubix/knowledge';

// Store instance
let store: KnowledgeStore | null = null;

function getStore(): KnowledgeStore {
  if (!store) {
    const knowledgePath = path.join(process.cwd(), '.knowledge');
    store = createKnowledgeStore(knowledgePath);
  }
  return store;
}

/**
 * Register knowledge commands
 */
export function registerKnowledgeCommands(program: Command): void {
  const knowledge = program
    .command('knowledge')
    .description('Manage knowledge graph');

  knowledge
    .command('add <type> <id> <name>')
    .description('Add an entity to the knowledge graph')
    .option('--desc <description>', 'Entity description')
    .option('--tags <tags>', 'Comma-separated tags')
    .action(async (type: string, id: string, name: string, options: { desc?: string; tags?: string }) => {
      const validTypes: EntityType[] = ['requirement', 'design', 'task', 'code', 'pattern'];
      if (!validTypes.includes(type as EntityType)) {
        console.error(`❌ Invalid type: ${type}. Valid types: ${validTypes.join(', ')}`);
        process.exit(1);
      }
      
      const store = getStore();
      const now = new Date().toISOString();
      
      const entity: Entity = {
        id,
        type: type as EntityType,
        name,
        description: options.desc,
        properties: {},
        tags: options.tags ? options.tags.split(',') : [],
        createdAt: now,
        updatedAt: now,
      };
      
      await store.putEntity(entity);
      await store.save();
      
      console.log(`✅ Added entity: ${id} (${type})`);
    });

  knowledge
    .command('get <id>')
    .description('Get an entity from the knowledge graph')
    .action(async (id: string) => {
      const store = getStore();
      await store.load();
      
      const entity = await store.getEntity(id);
      
      if (!entity) {
        console.error(`❌ Entity not found: ${id}`);
        process.exit(1);
      }
      
      console.log(`📦 Entity: ${entity.id}`);
      console.log(`   Type: ${entity.type}`);
      console.log(`   Name: ${entity.name}`);
      if (entity.description) {
        console.log(`   Description: ${entity.description}`);
      }
      if (entity.tags?.length) {
        console.log(`   Tags: ${entity.tags.join(', ')}`);
      }
      console.log(`   Created: ${entity.createdAt}`);
    });

  knowledge
    .command('delete <id>')
    .description('Delete an entity from the knowledge graph')
    .action(async (id: string) => {
      const store = getStore();
      const success = await store.deleteEntity(id);
      
      if (success) {
        await store.save();
        console.log(`✅ Deleted entity: ${id}`);
      } else {
        console.error(`❌ Entity not found: ${id}`);
        process.exit(1);
      }
    });

  knowledge
    .command('link <source> <type> <target>')
    .description('Add a relation between entities')
    .action(async (source: string, type: string, target: string) => {
      const validTypes: RelationType[] = ['implements', 'depends_on', 'traces_to'];
      if (!validTypes.includes(type as RelationType)) {
        console.error(`❌ Invalid relation type: ${type}. Valid types: ${validTypes.join(', ')}`);
        process.exit(1);
      }
      
      const store = getStore();
      
      const relation: Relation = {
        id: `${source}-${type}-${target}`,
        source,
        target,
        type: type as RelationType,
      };
      
      try {
        await store.addRelation(relation);
        await store.save();
        console.log(`✅ Added relation: ${source} --[${type}]--> ${target}`);
      } catch (error) {
        console.error(`❌ Error: ${(error as Error).message}`);
        process.exit(1);
      }
    });

  knowledge
    .command('query')
    .description('Query entities from the knowledge graph')
    .option('--type <type>', 'Filter by entity type')
    .option('--tags <tags>', 'Filter by comma-separated tags')
    .option('--text <text>', 'Full-text search')
    .action(async (options: { type?: string; tags?: string; text?: string }) => {
      const store = getStore();
      await store.load();
      
      const entities = await store.query({
        type: options.type as EntityType | undefined,
        tags: options.tags ? options.tags.split(',') : undefined,
        text: options.text,
      });
      
      console.log(`📊 Found ${entities.length} entities:\n`);
      
      for (const entity of entities) {
        console.log(`  ${entity.id} (${entity.type})`);
        console.log(`    Name: ${entity.name}`);
        if (entity.tags?.length) {
          console.log(`    Tags: ${entity.tags.join(', ')}`);
        }
      }
    });

  knowledge
    .command('traverse <id>')
    .description('Traverse the knowledge graph from a starting entity')
    .option('--depth <n>', 'Maximum traversal depth', '3')
    .option('--direction <dir>', 'Traversal direction (in|out|both)', 'both')
    .action(async (startId: string, options: { depth: string; direction: string }) => {
      const store = getStore();
      await store.load();
      
      const depth = parseInt(options.depth, 10);
      const direction = options.direction as 'in' | 'out' | 'both';
      
      const entities = await store.traverse(startId, { depth, direction });
      
      console.log(`🔍 Traversing from ${startId} (depth=${depth}, direction=${direction}):\n`);
      
      for (const entity of entities) {
        console.log(`  ${entity.id} (${entity.type}) - ${entity.name}`);
      }
    });

  knowledge
    .command('stats')
    .description('Show knowledge graph statistics')
    .action(async () => {
      const store = getStore();
      await store.load();
      
      const stats = (store as { getStats: () => { entityCount: number; relationCount: number; types: Record<string, number> } }).getStats();
      
      console.log('📈 Knowledge Graph Statistics:\n');
      console.log(`  Total Entities: ${stats.entityCount}`);
      console.log(`  Total Relations: ${stats.relationCount}`);
      console.log('\n  By Type:');
      for (const [type, count] of Object.entries(stats.types)) {
        console.log(`    ${type}: ${count}`);
      }
    });
}
