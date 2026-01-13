/**
 * Actionable Error Tests
 *
 * @module error/actionable-error.test
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  ActionableError,
  ErrorFormatter,
  ErrorCodes,
  CommonErrors,
  type ErrorSuggestion,
} from './actionable-error.js';

describe('ActionableError', () => {
  describe('constructor', () => {
    it('should create error with code and message', () => {
      const error = new ActionableError('Test error', {
        code: 'TEST_ERROR',
      });

      expect(error.message).toBe('Test error');
      expect(error.code).toBe('TEST_ERROR');
      expect(error.severity).toBe('error');
      expect(error.suggestions).toHaveLength(0);
    });

    it('should set severity', () => {
      const error = new ActionableError('Warning message', {
        code: 'TEST_WARN',
        severity: 'warning',
      });

      expect(error.severity).toBe('warning');
    });

    it('should include context', () => {
      const error = new ActionableError('File error', {
        code: 'FILE_ERROR',
        context: {
          file: '/path/to/file.ts',
          line: 42,
          column: 10,
          artifactId: 'REQ-001',
        },
      });

      expect(error.context.file).toBe('/path/to/file.ts');
      expect(error.context.line).toBe(42);
      expect(error.context.column).toBe(10);
      expect(error.context.artifactId).toBe('REQ-001');
    });

    it('should include suggestions', () => {
      const suggestions: ErrorSuggestion[] = [
        { action: 'Fix it', description: 'Do the thing' },
        { action: 'Try again', description: 'Retry the operation', command: 'npm run retry' },
      ];

      const error = new ActionableError('Action needed', {
        code: 'ACTION_NEEDED',
        suggestions,
      });

      expect(error.suggestions).toHaveLength(2);
      expect(error.suggestions[0].action).toBe('Fix it');
      expect(error.suggestions[1].command).toBe('npm run retry');
    });

    it('should preserve cause', () => {
      const cause = new Error('Original error');
      const error = new ActionableError('Wrapped error', {
        code: 'WRAPPED',
        cause,
      });

      expect(error.cause).toBe(cause);
    });
  });

  describe('withSuggestion', () => {
    it('should create error with single suggestion', () => {
      const error = ActionableError.withSuggestion(
        'Single suggestion error',
        'SINGLE_SUGGEST',
        { action: 'Do this', description: 'This is what to do' }
      );

      expect(error.suggestions).toHaveLength(1);
      expect(error.suggestions[0].action).toBe('Do this');
    });
  });

  describe('fromError', () => {
    it('should wrap standard Error', () => {
      const original = new Error('Original message');
      const error = ActionableError.fromError(original, 'WRAPPED_ERROR');

      expect(error.message).toBe('Original message');
      expect(error.code).toBe('WRAPPED_ERROR');
      expect(error.cause).toBe(original);
    });

    it('should include suggestions when wrapping', () => {
      const original = new Error('Original');
      const error = ActionableError.fromError(original, 'WRAPPED', [
        { action: 'Suggestion', description: 'A suggestion' },
      ]);

      expect(error.suggestions).toHaveLength(1);
    });
  });

  describe('isActionableError', () => {
    it('should return true for ActionableError', () => {
      const error = new ActionableError('Test', { code: 'TEST' });
      expect(ActionableError.isActionableError(error)).toBe(true);
    });

    it('should return false for standard Error', () => {
      const error = new Error('Test');
      expect(ActionableError.isActionableError(error)).toBe(false);
    });

    it('should return false for non-errors', () => {
      expect(ActionableError.isActionableError('string')).toBe(false);
      expect(ActionableError.isActionableError(null)).toBe(false);
      expect(ActionableError.isActionableError(undefined)).toBe(false);
    });
  });

  describe('addSuggestion', () => {
    it('should add suggestion and return this', () => {
      const error = new ActionableError('Test', { code: 'TEST' });
      const result = error.addSuggestion({ action: 'New', description: 'New suggestion' });

      expect(result).toBe(error);
      expect(error.suggestions).toHaveLength(1);
    });
  });

  describe('toFormattedString', () => {
    it('should return formatted output', () => {
      const error = new ActionableError('Test error', {
        code: 'TEST',
        context: { file: '/test.ts', line: 10 },
        suggestions: [{ action: 'Fix', description: 'Fix the thing' }],
      });

      const formatted = error.toFormattedString();

      expect(formatted).toContain('[TEST]');
      expect(formatted).toContain('Test error');
      expect(formatted).toContain('/test.ts:10');
      expect(formatted).toContain('Fix');
    });
  });
});

describe('ErrorFormatter', () => {
  beforeEach(() => {
    ErrorFormatter.setColorOutput(false);
  });

  describe('format', () => {
    it('should format basic error', () => {
      const error = new ActionableError('Simple error', {
        code: 'SIMPLE',
      });

      const formatted = ErrorFormatter.format(error);

      expect(formatted).toContain('❌');
      expect(formatted).toContain('[SIMPLE]');
      expect(formatted).toContain('Simple error');
    });

    it('should format warning', () => {
      const error = new ActionableError('Warning message', {
        code: 'WARN',
        severity: 'warning',
      });

      const formatted = ErrorFormatter.format(error);

      expect(formatted).toContain('⚠️');
    });

    it('should format info', () => {
      const error = new ActionableError('Info message', {
        code: 'INFO',
        severity: 'info',
      });

      const formatted = ErrorFormatter.format(error);

      expect(formatted).toContain('ℹ️');
    });

    it('should include file location', () => {
      const error = new ActionableError('Error', {
        code: 'LOC',
        context: { file: '/path/file.ts', line: 42, column: 5 },
      });

      const formatted = ErrorFormatter.format(error);

      expect(formatted).toContain('📍');
      expect(formatted).toContain('/path/file.ts:42:5');
    });

    it('should include artifact ID', () => {
      const error = new ActionableError('Error', {
        code: 'ART',
        context: { artifactId: 'REQ-PROJ-001' },
      });

      const formatted = ErrorFormatter.format(error);

      expect(formatted).toContain('📎');
      expect(formatted).toContain('REQ-PROJ-001');
    });

    it('should include suggestions', () => {
      const error = new ActionableError('Error', {
        code: 'SUG',
        suggestions: [
          { action: 'Action 1', description: 'Description 1' },
          { action: 'Action 2', description: 'Description 2', command: 'npm run fix' },
        ],
      });

      const formatted = ErrorFormatter.format(error);

      expect(formatted).toContain('💡 Suggestions');
      expect(formatted).toContain('Action 1');
      expect(formatted).toContain('Description 1');
      expect(formatted).toContain('$ npm run fix');
    });

    it('should include doc link', () => {
      const error = new ActionableError('Error', {
        code: 'DOC',
        suggestions: [
          { action: 'Read docs', description: 'See documentation', docLink: 'docs/guide.md' },
        ],
      });

      const formatted = ErrorFormatter.format(error);

      expect(formatted).toContain('📖 docs/guide.md');
    });
  });

  describe('formatAll', () => {
    it('should format multiple errors', () => {
      const errors = [
        new ActionableError('Error 1', { code: 'E1' }),
        new ActionableError('Error 2', { code: 'E2', severity: 'warning' }),
      ];

      const formatted = ErrorFormatter.formatAll(errors);

      expect(formatted).toContain('Found 2 issue(s)');
      expect(formatted).toContain('1 errors');
      expect(formatted).toContain('1 warnings');
      expect(formatted).toContain('[E1]');
      expect(formatted).toContain('[E2]');
    });

    it('should handle empty array', () => {
      const formatted = ErrorFormatter.formatAll([]);

      expect(formatted).toContain('✅ No errors');
    });
  });

  describe('formatAsJson', () => {
    it('should format as JSON', () => {
      const error = new ActionableError('JSON test', {
        code: 'JSON',
        severity: 'warning',
        context: { file: 'test.ts' },
        suggestions: [{ action: 'Test', description: 'Description' }],
      });

      const json = ErrorFormatter.formatAsJson(error);
      const parsed = JSON.parse(json);

      expect(parsed.code).toBe('JSON');
      expect(parsed.severity).toBe('warning');
      expect(parsed.message).toBe('JSON test');
      expect(parsed.context.file).toBe('test.ts');
      expect(parsed.suggestions).toHaveLength(1);
    });
  });
});

describe('CommonErrors', () => {
  describe('fileNotFound', () => {
    it('should create file not found error', () => {
      const error = CommonErrors.fileNotFound('/missing/file.ts');

      expect(error.code).toBe(ErrorCodes.FILE_NOT_FOUND);
      expect(error.message).toContain('File not found');
      expect(error.context.file).toBe('/missing/file.ts');
      expect(error.suggestions.length).toBeGreaterThan(0);
    });
  });

  describe('earsValidationFailed', () => {
    it('should create EARS validation error', () => {
      const error = CommonErrors.earsValidationFailed('req.md', ['Issue 1', 'Issue 2']);

      expect(error.code).toBe(ErrorCodes.EARS_VALIDATION_FAILED);
      expect(error.message).toContain('2 issue(s)');
      expect(error.context.file).toBe('req.md');
    });
  });

  describe('traceabilityMissing', () => {
    it('should create traceability error', () => {
      const error = CommonErrors.traceabilityMissing('REQ-001', 'DES-001');

      expect(error.code).toBe(ErrorCodes.TRACEABILITY_MISSING);
      expect(error.severity).toBe('warning');
      expect(error.message).toContain('REQ-001');
      expect(error.message).toContain('DES-001');
    });
  });

  describe('phaseTransitionBlocked', () => {
    it('should create phase transition error', () => {
      const error = CommonErrors.phaseTransitionBlocked('design', 'implementation', 'Tasks not defined');

      expect(error.code).toBe(ErrorCodes.PHASE_TRANSITION_BLOCKED);
      expect(error.message).toContain('design');
      expect(error.message).toContain('implementation');
      expect(error.message).toContain('Tasks not defined');
    });
  });

  describe('qualityGateFailed', () => {
    it('should create quality gate error', () => {
      const error = CommonErrors.qualityGateFailed('Test Coverage', 'Coverage is 60%, required 80%');

      expect(error.code).toBe(ErrorCodes.QUALITY_GATE_FAILED);
      expect(error.message).toContain('Test Coverage');
      expect(error.suggestions.some((s) => s.description.includes('60%'))).toBe(true);
    });
  });
});

describe('ErrorCodes', () => {
  it('should have all required error codes', () => {
    expect(ErrorCodes.EARS_VALIDATION_FAILED).toBeDefined();
    expect(ErrorCodes.TRACEABILITY_MISSING).toBeDefined();
    expect(ErrorCodes.FILE_NOT_FOUND).toBeDefined();
    expect(ErrorCodes.PHASE_TRANSITION_BLOCKED).toBeDefined();
    expect(ErrorCodes.QUALITY_GATE_FAILED).toBeDefined();
  });
});
