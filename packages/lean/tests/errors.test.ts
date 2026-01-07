/**
 * @fileoverview Unit tests for error classes
 * @module @nahisaho/musubix-lean/tests/errors
 * @traceability REQ-LEAN-001
 */

import { describe, it, expect } from 'vitest';
import {
  LeanError,
  LeanEnvironmentError,
  LeanConversionError,
  LeanVerificationError,
  LeanProofError,
  LeanExecutionError,
  LeanIntegrationError,
  ReProverError,
  LeanNotFoundError,
  LeanVersionError,
  EarsConversionError,
  EarsParseError,
} from '../src/errors.ts';

describe('Errors', () => {
  describe('LeanError', () => {
    it('should create base error with message', () => {
      const error = new LeanError('Base error', 'TEST_CODE');
      expect(error.message).toBe('Base error');
      expect(error.name).toBe('LeanError');
      expect(error.code).toBe('TEST_CODE');
    });

    it('should maintain error chain with cause', () => {
      const cause = new Error('Original error');
      const error = new LeanError('Wrapped error', 'TEST_CODE', cause);
      expect(error.cause).toBe(cause);
    });
  });

  describe('LeanNotFoundError', () => {
    it('should create not found error with install instructions', () => {
      const error = new LeanNotFoundError('linux');
      expect(error.message).toContain('Lean 4 is not installed');
      expect(error.message).toContain('elan');
      expect(error.name).toBe('LeanNotFoundError');
    });
  });

  describe('LeanVersionError', () => {
    it('should create version error', () => {
      const error = new LeanVersionError('4.0.0', '3.9.0');
      expect(error.message).toContain('4.0.0');
      expect(error.message).toContain('3.9.0');
      expect(error.required).toBe('4.0.0');
      expect(error.actual).toBe('3.9.0');
    });
  });

  describe('LeanEnvironmentError', () => {
    it('should create environment error', () => {
      const error = new LeanEnvironmentError('Lean not installed');
      expect(error.message).toBe('Lean not installed');
      expect(error.name).toBe('LeanEnvironmentError');
      expect(error).toBeInstanceOf(LeanError);
    });
  });

  describe('LeanConversionError', () => {
    it('should create conversion error', () => {
      const error = new LeanConversionError('Invalid EARS format');
      expect(error.message).toBe('Invalid EARS format');
      expect(error.name).toBe('LeanConversionError');
      expect(error).toBeInstanceOf(LeanError);
    });
  });

  describe('EarsConversionError', () => {
    it('should create EARS conversion error', () => {
      const error = new EarsConversionError('REQ-001', 'Invalid pattern');
      expect(error.message).toContain('REQ-001');
      expect(error.requirementId).toBe('REQ-001');
      expect(error.reason).toBe('Invalid pattern');
    });
  });

  describe('EarsParseError', () => {
    it('should create EARS parse error', () => {
      const error = new EarsParseError('invalid text', 'No pattern match');
      expect(error.text).toBe('invalid text');
      expect(error.reason).toBe('No pattern match');
    });
  });

  describe('LeanVerificationError', () => {
    it('should create verification error with errors array', () => {
      const error = new LeanVerificationError('Verification failed', [
        'Tactic failed',
        'Type mismatch',
      ]);
      expect(error.message).toBe('Verification failed');
      expect(error.name).toBe('LeanVerificationError');
      expect(error.errors).toEqual(['Tactic failed', 'Type mismatch']);
    });

    it('should create verification error without errors array', () => {
      const error = new LeanVerificationError('Simple failure');
      expect(error.errors).toEqual([]);
    });
  });

  describe('LeanProofError', () => {
    it('should create proof error', () => {
      const error = new LeanProofError('Proof incomplete');
      expect(error.message).toBe('Proof incomplete');
      expect(error.name).toBe('LeanProofError');
      expect(error).toBeInstanceOf(LeanError);
    });
  });

  describe('LeanExecutionError', () => {
    it('should create execution error with exit code', () => {
      const error = new LeanExecutionError('lean', 1, 'Error output');
      expect(error.message).toContain('lean');
      expect(error.name).toBe('LeanExecutionError');
      expect(error.command).toBe('lean');
      expect(error.exitCodeOrMessage).toBe(1);
      expect(error.stderr).toBe('Error output');
    });

    it('should handle string exit code', () => {
      const error = new LeanExecutionError('lean', 'SIGTERM', '');
      expect(error.exitCodeOrMessage).toBe('SIGTERM');
    });
  });

  describe('LeanIntegrationError', () => {
    it('should create integration error', () => {
      const error = new LeanIntegrationError('Integration failed');
      expect(error.message).toBe('Integration failed');
      expect(error.name).toBe('LeanIntegrationError');
      expect(error).toBeInstanceOf(LeanError);
    });
  });

  describe('ReProverError', () => {
    it('should create ReProver error', () => {
      const error = new ReProverError('ReProver service unavailable');
      expect(error.message).toBe('ReProver service unavailable');
      expect(error.name).toBe('ReProverError');
      expect(error).toBeInstanceOf(LeanError);
    });
  });

  describe('Error hierarchy', () => {
    it('should maintain instanceof relationships', () => {
      const errors = [
        new LeanEnvironmentError('test'),
        new LeanConversionError('test'),
        new LeanVerificationError('test'),
        new LeanProofError('test'),
        new LeanExecutionError('cmd', 1, 'err'),
        new LeanIntegrationError('test'),
        new ReProverError('test'),
      ];

      for (const error of errors) {
        expect(error).toBeInstanceOf(LeanError);
        expect(error).toBeInstanceOf(Error);
      }
    });

    it('should be catchable as LeanError', () => {
      const throwError = () => {
        throw new LeanVerificationError('Test error');
      };

      expect(throwError).toThrow(LeanError);
    });
  });
});
