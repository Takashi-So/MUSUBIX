/**
 * @fileoverview E2E tests for CLI commands
 * @traceability REQ-CLI-001
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { exec } from 'child_process';
import { promisify } from 'util';
import * as fs from 'fs';
import * as path from 'path';

const execAsync = promisify(exec);
const TEST_DIR = path.join(__dirname, '../../tmp/e2e-test');
const CLI_PATH = path.join(__dirname, '../../../../bin/musubix.js');

describe('CLI E2E Tests', () => {
  beforeAll(async () => {
    // Create test directory
    if (!fs.existsSync(TEST_DIR)) {
      fs.mkdirSync(TEST_DIR, { recursive: true });
    }
  });

  afterAll(async () => {
    // Cleanup test directory
    if (fs.existsSync(TEST_DIR)) {
      fs.rmSync(TEST_DIR, { recursive: true, force: true });
    }
  });

  describe('musubix --help', () => {
    it('should display help message', async () => {
      const { stdout } = await execAsync(`node ${CLI_PATH} --help`);
      expect(stdout).toContain('musubix');
      expect(stdout).toContain('requirements');
      expect(stdout).toContain('design');
      expect(stdout).toContain('learn');
    });

    it('should display version', async () => {
      const { stdout } = await execAsync(`node ${CLI_PATH} --version`);
      expect(stdout).toMatch(/\d+\.\d+\.\d+/);
    });
  });

  describe('musubix requirements', () => {
    it('should display requirements help', async () => {
      const { stdout } = await execAsync(`node ${CLI_PATH} requirements --help`);
      expect(stdout).toContain('analyze');
      expect(stdout).toContain('validate');
    });
  });

  describe('musubix design', () => {
    it('should display design help', async () => {
      const { stdout } = await execAsync(`node ${CLI_PATH} design --help`);
      expect(stdout).toContain('generate');
      expect(stdout).toContain('patterns');
    });
  });

  describe('musubix learn', () => {
    it('should display learn help', async () => {
      const { stdout } = await execAsync(`node ${CLI_PATH} learn --help`);
      expect(stdout).toContain('status');
      expect(stdout).toContain('feedback');
      expect(stdout).toContain('patterns');
    });

    it('should show learning status', async () => {
      const { stdout } = await execAsync(`node ${CLI_PATH} learn status`);
      expect(stdout).toContain('Learning');
    });

    it('should list best practices', async () => {
      const { stdout } = await execAsync(`node ${CLI_PATH} learn best-practices`);
      expect(stdout).toContain('Best Practice');
    });
  });

  describe('musubix ontology', () => {
    it('should display ontology help', async () => {
      const { stdout } = await execAsync(`node ${CLI_PATH} ontology --help`);
      expect(stdout).toContain('validate');
      expect(stdout).toContain('check-circular');
      expect(stdout).toContain('stats');
    });

    it('should validate triples from JSON file', async () => {
      const testFile = path.join(TEST_DIR, 'test-triples.json');
      const triples = [
        { subject: 'http://example.org/A', predicate: 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', object: 'http://example.org/Class' },
        { subject: 'http://example.org/B', predicate: 'http://www.w3.org/2000/01/rdf-schema#subClassOf', object: 'http://example.org/A' }
      ];
      fs.writeFileSync(testFile, JSON.stringify(triples));

      const { stdout } = await execAsync(`node ${CLI_PATH} ontology validate -f ${testFile}`);
      expect(stdout).toContain('Loaded 2 triples');
    });

    it('should check circular dependencies', async () => {
      const testFile = path.join(TEST_DIR, 'test-relationships.json');
      const relationships = [
        { subject: 'A', predicate: 'dependsOn', object: 'B' },
        { subject: 'B', predicate: 'dependsOn', object: 'C' }
      ];
      fs.writeFileSync(testFile, JSON.stringify(relationships));

      const { stdout } = await execAsync(`node ${CLI_PATH} ontology check-circular -f ${testFile}`);
      expect(stdout).toContain('No circular dependencies');
    });

    it('should detect circular dependencies', async () => {
      const testFile = path.join(TEST_DIR, 'test-circular.json');
      const relationships = [
        { subject: 'A', predicate: 'dependsOn', object: 'B' },
        { subject: 'B', predicate: 'dependsOn', object: 'C' },
        { subject: 'C', predicate: 'dependsOn', object: 'A' }
      ];
      fs.writeFileSync(testFile, JSON.stringify(relationships));

      try {
        await execAsync(`node ${CLI_PATH} ontology check-circular -f ${testFile}`);
      } catch (error: any) {
        expect(error.stdout).toContain('cycle');
      }
    });

    it('should show stats', async () => {
      const testFile = path.join(TEST_DIR, 'test-stats.json');
      const triples = [
        { subject: 'A', predicate: 'type', object: 'Class' },
        { subject: 'B', predicate: 'type', object: 'Class' },
        { subject: 'A', predicate: 'relatedTo', object: 'B' }
      ];
      fs.writeFileSync(testFile, JSON.stringify(triples));

      const { stdout } = await execAsync(`node ${CLI_PATH} ontology stats -f ${testFile}`);
      expect(stdout).toContain('Total Triples');
      expect(stdout).toContain('3');
    });
  });

  describe('musubix codegen', () => {
    it('should display codegen help', async () => {
      const { stdout } = await execAsync(`node ${CLI_PATH} codegen --help`);
      expect(stdout).toContain('generate');
      expect(stdout).toContain('analyze');
    });
  });

  describe('musubix trace', () => {
    it('should display trace help', async () => {
      const { stdout } = await execAsync(`node ${CLI_PATH} trace --help`);
      expect(stdout).toContain('matrix');
      expect(stdout).toContain('impact');
    });
  });

  describe('musubix explain', () => {
    it('should display explain help', async () => {
      const { stdout } = await execAsync(`node ${CLI_PATH} explain --help`);
      expect(stdout).toContain('why');
      expect(stdout).toContain('graph');
    });
  });
});
