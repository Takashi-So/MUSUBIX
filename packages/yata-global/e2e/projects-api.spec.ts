/**
 * E2E tests for YATA Global Projects API
 * 
 * @packageDocumentation
 */

import { test, expect } from '@playwright/test';

const BASE_URL = process.env.YATA_GLOBAL_URL || 'http://localhost:3000';

test.describe('YATA Global Projects API', () => {
  test.describe('Health Check', () => {
    test('GET /health returns healthy status', async ({ request }) => {
      const response = await request.get(`${BASE_URL}/health`);
      expect(response.ok()).toBe(true);
      
      const data = await response.json();
      expect(data.success).toBe(true);
      expect(data.data.status).toBe('healthy');
      expect(data.data.version).toBeDefined();
    });
  });

  test.describe('Projects API - /api/v1/projects', () => {
    test('GET /api/v1/projects returns list of projects', async ({ request }) => {
      const response = await request.get(`${BASE_URL}/api/v1/projects`);
      expect(response.ok()).toBe(true);
      
      const data = await response.json();
      expect(data.success).toBe(true);
      expect(data.data.items).toBeInstanceOf(Array);
      expect(data.data.total).toBeGreaterThanOrEqual(0);
    });

    test('GET /api/v1/projects/sample-project returns sample project', async ({ request }) => {
      const response = await request.get(`${BASE_URL}/api/v1/projects/sample-project`);
      expect(response.ok()).toBe(true);
      
      const data = await response.json();
      expect(data.success).toBe(true);
      expect(data.data.id).toBe('sample-project');
      expect(data.data.name).toBe('Sample Project');
      expect(data.data.namespace).toBe('sample.project');
      expect(data.data.entities).toBeInstanceOf(Array);
      expect(data.data.relationships).toBeInstanceOf(Array);
    });

    test('GET /projects/sample-project (legacy route) returns sample project', async ({ request }) => {
      const response = await request.get(`${BASE_URL}/projects/sample-project`);
      expect(response.ok()).toBe(true);
      
      const data = await response.json();
      expect(data.success).toBe(true);
      expect(data.data.id).toBe('sample-project');
    });

    test('GET /api/v1/projects/non-existent returns 404', async ({ request }) => {
      const response = await request.get(`${BASE_URL}/api/v1/projects/non-existent`);
      expect(response.status()).toBe(404);
      
      const data = await response.json();
      expect(data.success).toBe(false);
      expect(data.error).toContain('not found');
    });

    test('POST /api/v1/projects creates a new project', async ({ request }) => {
      const newProject = {
        name: 'Test Project',
        description: 'A test project for E2E testing',
        namespace: 'test.project',
        entities: [
          { id: 'test-entity-1', name: 'TestService', type: 'class' }
        ],
        relationships: []
      };

      const response = await request.post(`${BASE_URL}/api/v1/projects`, {
        data: newProject
      });
      expect(response.status()).toBe(201);
      
      const data = await response.json();
      expect(data.success).toBe(true);
      expect(data.data.name).toBe('Test Project');
      expect(data.data.namespace).toBe('test.project');
      expect(data.data.entities).toHaveLength(1);
    });

    test('PUT /api/v1/projects/:id updates a project', async ({ request }) => {
      // First create a project
      const createResponse = await request.post(`${BASE_URL}/api/v1/projects`, {
        data: {
          id: 'update-test-project',
          name: 'Original Name',
          description: 'Original description'
        }
      });
      expect(createResponse.status()).toBe(201);

      // Then update it
      const updateResponse = await request.put(`${BASE_URL}/api/v1/projects/update-test-project`, {
        data: {
          name: 'Updated Name',
          description: 'Updated description'
        }
      });
      expect(updateResponse.ok()).toBe(true);
      
      const data = await updateResponse.json();
      expect(data.success).toBe(true);
      expect(data.data.name).toBe('Updated Name');
      expect(data.data.description).toBe('Updated description');
    });

    test('DELETE /api/v1/projects/:id deletes a project', async ({ request }) => {
      // First create a project
      const createResponse = await request.post(`${BASE_URL}/api/v1/projects`, {
        data: {
          id: 'delete-test-project',
          name: 'To Be Deleted'
        }
      });
      expect(createResponse.status()).toBe(201);

      // Then delete it
      const deleteResponse = await request.delete(`${BASE_URL}/api/v1/projects/delete-test-project`);
      expect(deleteResponse.ok()).toBe(true);
      
      const data = await deleteResponse.json();
      expect(data.success).toBe(true);
      expect(data.data.deleted).toBe(true);

      // Verify it's deleted
      const getResponse = await request.get(`${BASE_URL}/api/v1/projects/delete-test-project`);
      expect(getResponse.status()).toBe(404);
    });
  });

  test.describe('Sample Project Entities', () => {
    test('sample-project has UserService entity', async ({ request }) => {
      const response = await request.get(`${BASE_URL}/api/v1/projects/sample-project`);
      const data = await response.json();
      
      const userService = data.data.entities.find((e: { name: string }) => e.name === 'UserService');
      expect(userService).toBeDefined();
      expect(userService.type).toBe('class');
      expect(userService.metadata?.pattern).toBe('Service');
    });

    test('sample-project has UserRepository entity', async ({ request }) => {
      const response = await request.get(`${BASE_URL}/api/v1/projects/sample-project`);
      const data = await response.json();
      
      const repo = data.data.entities.find((e: { name: string }) => e.name === 'UserRepository');
      expect(repo).toBeDefined();
      expect(repo.type).toBe('class');
      expect(repo.metadata?.pattern).toBe('Repository');
    });

    test('sample-project has relationships', async ({ request }) => {
      const response = await request.get(`${BASE_URL}/api/v1/projects/sample-project`);
      const data = await response.json();
      
      expect(data.data.relationships).toHaveLength(2);
      
      const usesRelation = data.data.relationships.find((r: { type: string }) => r.type === 'uses');
      expect(usesRelation).toBeDefined();
      
      const callsRelation = data.data.relationships.find((r: { type: string }) => r.type === 'calls');
      expect(callsRelation).toBeDefined();
    });
  });

  test.describe('KGPR Integration', () => {
    test('Create KGPR from project namespace', async ({ request }) => {
      const kgpr = {
        title: 'Export from sample-project',
        description: 'KGPR created from sample project',
        sourceNamespace: 'sample.project',
        diff: {
          entities: {
            added: [
              {
                changeType: 'add',
                localId: 'pattern-1',
                name: 'ServicePattern',
                entityType: 'pattern',
                namespace: 'sample.project'
              }
            ],
            updated: [],
            deleted: []
          },
          relationships: { added: [], updated: [], deleted: [] },
          stats: {
            entitiesAdded: 1,
            entitiesUpdated: 0,
            entitiesDeleted: 0,
            relationshipsAdded: 0,
            relationshipsUpdated: 0,
            relationshipsDeleted: 0,
            totalChanges: 1
          }
        }
      };

      const response = await request.post(`${BASE_URL}/api/v1/kgprs`, {
        data: kgpr
      });
      expect(response.status()).toBe(201);
      
      const data = await response.json();
      expect(data.success).toBe(true);
      expect(data.data.title).toBe('Export from sample-project');
      expect(data.data.sourceNamespace).toBe('sample.project');
      expect(data.data.status).toBe('open');
    });
  });
});
