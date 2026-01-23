/**
 * @musubix/mcp-server - Basic Tests
 */
import { describe, it, expect } from 'vitest';

describe('@musubix/mcp-server', () => {
  describe('Package Export', () => {
    it('should export MCPServer', async () => {
      const { MCPServer } = await import('../index.js');
      expect(MCPServer).toBeDefined();
    }, 30000); // Extended timeout for parallel test runs

    it('should export sddTools', async () => {
      const { sddTools } = await import('../index.js');
      expect(sddTools).toBeDefined();
      expect(Array.isArray(sddTools)).toBe(true);
    });

    it('should export sddPrompts', async () => {
      const { sddPrompts } = await import('../index.js');
      expect(sddPrompts).toBeDefined();
      expect(Array.isArray(sddPrompts)).toBe(true);
    });
  });

  describe('Tools', () => {
    it('should have tools defined', async () => {
      const { sddTools } = await import('../index.js');
      expect(sddTools.length).toBeGreaterThan(0);
    });

    it('should have valid tool structure', async () => {
      const { sddTools } = await import('../index.js');
      
      sddTools.forEach((tool: any) => {
        expect(tool).toHaveProperty('name');
        expect(tool).toHaveProperty('description');
        expect(typeof tool.name).toBe('string');
        expect(typeof tool.description).toBe('string');
      });
    });
  });

  describe('Prompts', () => {
    it('should have prompts defined', async () => {
      const { sddPrompts } = await import('../index.js');
      expect(sddPrompts.length).toBeGreaterThan(0);
    });
  });
});
