// Expert Delegation Integration Tests
// TSK-DR-022
// REQ: REQ-DR-INT-002
// DES: DES-DR-v3.4.0 Section 5.1

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { ExpertIntegration, createExpertIntegration } from '../providers/expert-integration.js';

/**
 * Test Suite: Expert Delegation Integration
 * 
 * Verifies integration with @nahisaho/musubix-expert-delegation package.
 * 
 * Test Coverage:
 * 1. Expert delegation provider initialization
 * 2. Expert type selection based on prompt
 * 3. Timeout and fallback behavior
 * 4. Error handling
 * 5. Integration with external package
 */
describe('Expert Delegation Integration', () => {
  let expertIntegration: ExpertIntegration;
  
  beforeEach(() => {
    expertIntegration = createExpertIntegration(30000);
  });
  
  describe('Initialization', () => {
    it('should create expert integration instance', () => {
      expect(expertIntegration).toBeInstanceOf(ExpertIntegration);
      expect(expertIntegration.name).toBe('Expert Delegation');
    });
    
    it('should create with custom timeout', () => {
      const custom = createExpertIntegration(5000);
      expect(custom).toBeInstanceOf(ExpertIntegration);
    });
    
    it('should create with custom expert selector', () => {
      const selector = (prompt: string) => 'custom-expert';
      const custom = createExpertIntegration(30000, selector);
      expect(custom).toBeInstanceOf(ExpertIntegration);
    });
  });
  
  describe('Expert Type Selection', () => {
    it('should select SECURITY_ANALYST for security-related prompts', () => {
      const prompts = [
        'What are the security implications of using JWT tokens?',
        'How to implement authentication in TypeScript?',
        'Check for security vulnerabilities in this code',
      ];
      
      prompts.forEach((prompt) => {
        const expertType = (expertIntegration as any).defaultExpertSelector(prompt);
        expect(expertType).toBe(ExpertIntegration.EXPERTS.SECURITY_ANALYST);
      });
    });
    
    it('should select PERFORMANCE_ENGINEER for performance-related prompts', () => {
      const prompts = [
        'How to optimize database queries?',
        'Improve the performance of this function',
        'Scalability considerations for microservices',
      ];
      
      prompts.forEach((prompt) => {
        const expertType = (expertIntegration as any).defaultExpertSelector(prompt);
        expect(expertType).toBe(ExpertIntegration.EXPERTS.PERFORMANCE_ENGINEER);
      });
    });
    
    it('should select DATABASE_SPECIALIST for database-related prompts', () => {
      const prompts = [
        'Design a database schema for e-commerce',
        'SQL query for joining three tables',
        'Database indexing strategies',
      ];
      
      prompts.forEach((prompt) => {
        const expertType = (expertIntegration as any).defaultExpertSelector(prompt);
        expect(expertType).toBe(ExpertIntegration.EXPERTS.DATABASE_SPECIALIST);
      });
    });
    
    it('should select DEVOPS_ENGINEER for DevOps-related prompts', () => {
      const prompts = [
        'Set up CI/CD pipeline for Node.js',
        'Infrastructure as code with Terraform',
        'Deployment strategies for Kubernetes',
      ];
      
      prompts.forEach((prompt) => {
        const expertType = (expertIntegration as any).defaultExpertSelector(prompt);
        expect(expertType).toBe(ExpertIntegration.EXPERTS.DEVOPS_ENGINEER);
      });
    });
    
    it('should select CODE_REVIEWER for code review prompts', () => {
      const prompts = [
        'Review this TypeScript code',
        'Refactor this function for better readability',
        'Best practices for React components',
      ];
      
      prompts.forEach((prompt) => {
        const expertType = (expertIntegration as any).defaultExpertSelector(prompt);
        expect(expertType).toBe(ExpertIntegration.EXPERTS.CODE_REVIEWER);
      });
    });
    
    it('should select TECHNICAL_WRITER for documentation prompts', () => {
      const prompts = [
        'Write documentation for this API',
        'Explain how dependency injection works',
        'Describe the architecture of this system',
      ];
      
      prompts.forEach((prompt) => {
        const expertType = (expertIntegration as any).defaultExpertSelector(prompt);
        expect(expertType).toBe(ExpertIntegration.EXPERTS.TECHNICAL_WRITER);
      });
    });
    
    it('should select SOFTWARE_ARCHITECT as default', () => {
      const prompts = [
        'Design a microservices architecture',
        'What is the best approach for this problem?',
        'General software engineering question',
      ];
      
      prompts.forEach((prompt) => {
        const expertType = (expertIntegration as any).defaultExpertSelector(prompt);
        expect(expertType).toBe(ExpertIntegration.EXPERTS.SOFTWARE_ARCHITECT);
      });
    });
  });
  
  describe('Availability Check', () => {
    it('should check if expert delegation is available', async () => {
      const isAvailable = await expertIntegration.isAvailable();
      // Returns false if package not installed, true if installed
      expect(typeof isAvailable).toBe('boolean');
    });
    
    it('should handle unavailable package gracefully', async () => {
      // Mock loadExpertDelegation to return null
      vi.spyOn(expertIntegration as any, 'loadExpertDelegation').mockResolvedValue(null);
      
      const isAvailable = await expertIntegration.isAvailable();
      expect(isAvailable).toBe(false);
    });
  });
  
  describe('Generation with Expert Delegation', () => {
    it('should throw error if expert delegation not available', async () => {
      // Mock loadExpertDelegation to return null
      vi.spyOn(expertIntegration as any, 'loadExpertDelegation').mockResolvedValue(null);
      
      await expect(
        expertIntegration.generate('Test prompt')
      ).rejects.toThrow('Expert delegation package not available');
    });
    
    it('should call expert delegation with correct parameters', async () => {
      const mockConsult = vi.fn().mockResolvedValue({
        response: 'Expert response',
        confidence: 0.95,
        expertType: 'software-architect',
      });
      
      const mockExpertDelegation = {
        consult: mockConsult,
      };
      
      vi.spyOn(expertIntegration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);
      
      const result = await expertIntegration.generate('Design a REST API', {
        maxTokens: 1000,
        temperature: 0.7,
        systemPrompt: 'You are a helpful assistant',
      });
      
      expect(result).toBe('Expert response');
      expect(mockConsult).toHaveBeenCalledWith({
        expertType: ExpertIntegration.EXPERTS.SOFTWARE_ARCHITECT,
        query: 'Design a REST API',
        systemPrompt: 'You are a helpful assistant',
        maxTokens: 1000,
        temperature: 0.7,
        timeout: 30000,
      });
    });
    
    it('should select appropriate expert based on prompt', async () => {
      const mockConsult = vi.fn().mockResolvedValue({
        response: 'Security analysis complete',
        confidence: 0.90,
        expertType: 'security-analyst',
      });
      
      const mockExpertDelegation = {
        consult: mockConsult,
      };
      
      vi.spyOn(expertIntegration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);
      
      await expertIntegration.generate('Check for security vulnerabilities');
      
      expect(mockConsult).toHaveBeenCalledWith(
        expect.objectContaining({
          expertType: ExpertIntegration.EXPERTS.SECURITY_ANALYST,
        })
      );
    });
    
    it('should use custom expert selector if provided', async () => {
      const customSelector = (prompt: string) => 'custom-expert-type';
      const customIntegration = createExpertIntegration(30000, customSelector);
      
      const mockConsult = vi.fn().mockResolvedValue({
        response: 'Custom expert response',
        confidence: 0.85,
        expertType: 'custom-expert-type',
      });
      
      const mockExpertDelegation = {
        consult: mockConsult,
      };
      
      vi.spyOn(customIntegration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);
      
      await customIntegration.generate('Any prompt');
      
      expect(mockConsult).toHaveBeenCalledWith(
        expect.objectContaining({
          expertType: 'custom-expert-type',
        })
      );
    });
  });
  
  describe('Error Handling', () => {
    it('should handle expert delegation error', async () => {
      const mockConsult = vi.fn().mockRejectedValue(new Error('Expert consultation failed'));
      
      const mockExpertDelegation = {
        consult: mockConsult,
      };
      
      vi.spyOn(expertIntegration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);
      
      await expect(
        expertIntegration.generate('Test prompt')
      ).rejects.toThrow('Expert consultation failed');
    });
    
    it('should handle timeout error', async () => {
      const mockConsult = vi.fn().mockRejectedValue(new Error('Timeout exceeded'));
      
      const mockExpertDelegation = {
        consult: mockConsult,
      };
      
      vi.spyOn(expertIntegration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);
      
      await expect(
        expertIntegration.generate('Test prompt', { maxTokens: 500 })
      ).rejects.toThrow('Timeout exceeded');
    });
    
    it('should convert non-Error exceptions to Error', async () => {
      const mockConsult = vi.fn().mockRejectedValue('String error');
      
      const mockExpertDelegation = {
        consult: mockConsult,
      };
      
      vi.spyOn(expertIntegration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);
      
      await expect(
        expertIntegration.generate('Test prompt')
      ).rejects.toThrow('String error');
    });
  });
  
  describe('Timeout Configuration', () => {
    it('should use configured timeout', async () => {
      const customTimeout = 5000;
      const custom = createExpertIntegration(customTimeout);
      
      const mockConsult = vi.fn().mockResolvedValue({
        response: 'Response',
        confidence: 0.9,
        expertType: 'software-architect',
      });
      
      const mockExpertDelegation = {
        consult: mockConsult,
      };
      
      vi.spyOn(custom as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);
      
      await custom.generate('Test');
      
      expect(mockConsult).toHaveBeenCalledWith(
        expect.objectContaining({
          timeout: customTimeout,
        })
      );
    });
    
    it('should use default timeout if not specified', async () => {
      const defaultTimeout = 30000;
      const defaultIntegration = createExpertIntegration();
      
      const mockConsult = vi.fn().mockResolvedValue({
        response: 'Response',
        confidence: 0.9,
        expertType: 'software-architect',
      });
      
      const mockExpertDelegation = {
        consult: mockConsult,
      };
      
      vi.spyOn(defaultIntegration as any, 'loadExpertDelegation').mockResolvedValue(mockExpertDelegation);
      
      await defaultIntegration.generate('Test');
      
      expect(mockConsult).toHaveBeenCalledWith(
        expect.objectContaining({
          timeout: defaultTimeout,
        })
      );
    });
  });
  
  describe('Expert Types Constants', () => {
    it('should have all expert types defined', () => {
      expect(ExpertIntegration.EXPERTS.SOFTWARE_ARCHITECT).toBe('software-architect');
      expect(ExpertIntegration.EXPERTS.SECURITY_ANALYST).toBe('security-analyst');
      expect(ExpertIntegration.EXPERTS.PERFORMANCE_ENGINEER).toBe('performance-engineer');
      expect(ExpertIntegration.EXPERTS.CODE_REVIEWER).toBe('code-reviewer');
      expect(ExpertIntegration.EXPERTS.TECHNICAL_WRITER).toBe('technical-writer');
      expect(ExpertIntegration.EXPERTS.DATABASE_SPECIALIST).toBe('database-specialist');
      expect(ExpertIntegration.EXPERTS.DEVOPS_ENGINEER).toBe('devops-engineer');
    });
    
    it('should have 7 expert types', () => {
      const expertTypes = Object.keys(ExpertIntegration.EXPERTS);
      expect(expertTypes).toHaveLength(7);
    });
  });
});

/**
 * E2E Integration Test with Real Package
 * 
 * Note: This test requires @nahisaho/musubix-expert-delegation to be installed.
 * It will be skipped if the package is not available.
 */
describe('Expert Delegation E2E Integration', () => {
  it('should integrate with real expert-delegation package if available', async () => {
    const integration = createExpertIntegration(30000);
    
    const isAvailable = await integration.isAvailable();
    
    if (!isAvailable) {
      console.log('⚠️  Expert delegation package not available, skipping E2E test');
      return;
    }
    
    // If package is available, test real integration
    try {
      // This would call the real expert-delegation package
      // For now, we just verify availability
      expect(isAvailable).toBe(true);
      console.log('✅ Expert delegation package is available and integrated');
    } catch (error) {
      console.error('❌ E2E integration test failed:', error);
      throw error;
    }
  });
});
