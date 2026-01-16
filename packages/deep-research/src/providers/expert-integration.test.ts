// Expert Integration Tests
// TSK-DR-012

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { ExpertIntegration } from './expert-integration.js';

describe('ExpertIntegration', () => {
  let integration: ExpertIntegration;

  beforeEach(() => {
    integration = new ExpertIntegration(5000);
  });

  describe('defaultExpertSelector', () => {
    it('should select security analyst for security queries', async () => {
      const mockExpertDelegation = {
        consult: vi.fn().mockResolvedValue({
          response: 'Security analysis result',
          confidence: 0.9,
        }),
      };

      // Mock the dynamic import
      vi.spyOn(integration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);

      await integration.generate('How to implement authentication?');

      expect(mockExpertDelegation.consult).toHaveBeenCalledWith(
        expect.objectContaining({
          expertType: ExpertIntegration.EXPERTS.SECURITY_ANALYST,
        })
      );
    });

    it('should select performance engineer for performance queries', async () => {
      const mockExpertDelegation = {
        consult: vi.fn().mockResolvedValue({
          response: 'Performance optimization result',
          confidence: 0.85,
        }),
      };

      vi.spyOn(integration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);

      await integration.generate('How to optimize database queries?');

      expect(mockExpertDelegation.consult).toHaveBeenCalledWith(
        expect.objectContaining({
          expertType: ExpertIntegration.EXPERTS.PERFORMANCE_ENGINEER,
        })
      );
    });

    it('should select database specialist for database queries', async () => {
      const mockExpertDelegation = {
        consult: vi.fn().mockResolvedValue({
          response: 'Database design result',
          confidence: 0.88,
        }),
      };

      vi.spyOn(integration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);

      await integration.generate('What is the best database schema?');

      expect(mockExpertDelegation.consult).toHaveBeenCalledWith(
        expect.objectContaining({
          expertType: ExpertIntegration.EXPERTS.DATABASE_SPECIALIST,
        })
      );
    });

    it('should select DevOps engineer for deployment queries', async () => {
      const mockExpertDelegation = {
        consult: vi.fn().mockResolvedValue({
          response: 'Deployment strategy result',
          confidence: 0.87,
        }),
      };

      vi.spyOn(integration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);

      await integration.generate('How to set up CI/CD pipeline?');

      expect(mockExpertDelegation.consult).toHaveBeenCalledWith(
        expect.objectContaining({
          expertType: ExpertIntegration.EXPERTS.DEVOPS_ENGINEER,
        })
      );
    });

    it('should select code reviewer for review queries', async () => {
      const mockExpertDelegation = {
        consult: vi.fn().mockResolvedValue({
          response: 'Code review result',
          confidence: 0.9,
        }),
      };

      vi.spyOn(integration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);

      await integration.generate('Review this code for best practices');

      expect(mockExpertDelegation.consult).toHaveBeenCalledWith(
        expect.objectContaining({
          expertType: ExpertIntegration.EXPERTS.CODE_REVIEWER,
        })
      );
    });

    it('should select technical writer for documentation queries', async () => {
      const mockExpertDelegation = {
        consult: vi.fn().mockResolvedValue({
          response: 'Documentation result',
          confidence: 0.92,
        }),
      };

      vi.spyOn(integration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);

      await integration.generate('Explain how this API works');

      expect(mockExpertDelegation.consult).toHaveBeenCalledWith(
        expect.objectContaining({
          expertType: ExpertIntegration.EXPERTS.TECHNICAL_WRITER,
        })
      );
    });

    it('should default to software architect for general queries', async () => {
      const mockExpertDelegation = {
        consult: vi.fn().mockResolvedValue({
          response: 'Architecture design result',
          confidence: 0.85,
        }),
      };

      vi.spyOn(integration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);

      await integration.generate('How to design a microservices architecture?');

      expect(mockExpertDelegation.consult).toHaveBeenCalledWith(
        expect.objectContaining({
          expertType: ExpertIntegration.EXPERTS.SOFTWARE_ARCHITECT,
        })
      );
    });
  });

  describe('generate', () => {
    it('should generate response using expert delegation', async () => {
      const mockExpertDelegation = {
        consult: vi.fn().mockResolvedValue({
          response: 'Expert response',
          confidence: 0.9,
        }),
      };

      vi.spyOn(integration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);

      const result = await integration.generate('Test query', {
        maxTokens: 500,
        temperature: 0.8,
        systemPrompt: 'You are an expert',
      });

      expect(result).toBe('Expert response');
      expect(mockExpertDelegation.consult).toHaveBeenCalledWith(
        expect.objectContaining({
          query: 'Test query',
          systemPrompt: 'You are an expert',
          maxTokens: 500,
          temperature: 0.8,
        })
      );
    });

    it('should throw error if expert delegation not available', async () => {
      vi.spyOn(integration as any, 'loadExpertDelegation').mockResolvedValue(null);

      await expect(integration.generate('Test')).rejects.toThrow(
        'Expert delegation package not available'
      );
    });
  });

  describe('isAvailable', () => {
    it('should return true when expert delegation is available', async () => {
      vi.spyOn(integration as any, 'loadExpertDelegation').mockResolvedValue({});

      const available = await integration.isAvailable();

      expect(available).toBe(true);
    });

    it('should return false when expert delegation is not available', async () => {
      vi.spyOn(integration as any, 'loadExpertDelegation').mockResolvedValue(null);

      const available = await integration.isAvailable();

      expect(available).toBe(false);
    });

    it('should return false on error', async () => {
      vi.spyOn(integration as any, 'loadExpertDelegation').mockRejectedValue(
        new Error('Load error')
      );

      const available = await integration.isAvailable();

      expect(available).toBe(false);
    });
  });

  describe('custom expert selector', () => {
    it('should use custom expert selector', async () => {
      const customSelector = vi.fn().mockReturnValue('custom-expert');
      const customIntegration = new ExpertIntegration(5000, customSelector);

      const mockExpertDelegation = {
        consult: vi.fn().mockResolvedValue({
          response: 'Custom expert response',
          confidence: 0.95,
        }),
      };

      vi.spyOn(customIntegration as any, 'loadExpertDelegation').mockResolvedValue(
        mockExpertDelegation
      );

      await customIntegration.generate('Test query');

      expect(customSelector).toHaveBeenCalledWith('Test query');
      expect(mockExpertDelegation.consult).toHaveBeenCalledWith(
        expect.objectContaining({
          expertType: 'custom-expert',
        })
      );
    });
  });
});
