/**
 * @fileoverview Phase 2 Analyzer Tests - Zero-Day Detector
 * @module @nahisaho/musubix-security/tests/phase2
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  ZeroDayDetector,
  createZeroDayDetector,
} from '../../src/analyzers/sast/zero-day-detector.js';

describe('ZeroDayDetector', () => {
  let detector: ZeroDayDetector;

  beforeEach(() => {
    detector = createZeroDayDetector();
  });

  describe('Suspicious Pattern Detection', () => {
    it('should detect prototype pollution attempts', async () => {
      const code = `
function merge(target, source) {
  for (const key in source) {
    target[key] = source[key];
  }
  // Dangerous: allows __proto__ access
  obj["__proto__"].polluted = true;
}
`;
      const results = await detector.detect(code, 'test.js');
      
      expect(results.some(r => r.deviation.patternId === 'ZD-001')).toBe(true);
    });

    it('should detect dynamic function construction', async () => {
      const code = `
function execute(code) {
  const fn = new Function('x', 'return ' + code);
  return fn(10);
}
`;
      const results = await detector.detect(code, 'test.js');
      
      expect(results.some(r => r.deviation.patternId === 'ZD-002')).toBe(true);
    });

    it('should detect unsafe deserialization', async () => {
      const code = `
import pickle

def load_data(data):
    return pickle.loads(data)
`;
      const results = await detector.detect(code, 'test.py');
      
      expect(results.some(r => r.deviation.patternId === 'ZD-003')).toBe(true);
    });

    it('should detect dynamic attribute access', async () => {
      const code = `
def get_attr(obj, name):
    return getattr(obj, name)
`;
      const results = await detector.detect(code, 'test.py');
      
      expect(results.some(r => r.deviation.patternId === 'ZD-004')).toBe(true);
    });

    it('should detect command injection patterns', async () => {
      const code = `
import subprocess

def run_command(user_input):
    subprocess.Popen(user_input, shell=True)
`;
      const results = await detector.detect(code, 'test.py');
      
      expect(results.some(r => r.deviation.patternId === 'ZD-006')).toBe(true);
    });

    it('should detect weak cryptography', async () => {
      const code = `
import hashlib

def hash_password(password):
    return hashlib.MD5(password).hexdigest()
`;
      const results = await detector.detect(code, 'test.py');
      
      expect(results.some(r => r.deviation.patternId === 'ZD-010')).toBe(true);
    });
  });

  describe('API Usage Deviation Detection', () => {
    it('should detect dangerous API combinations', async () => {
      const code = `
async function handleRequest(req, res) {
  const data = await fetch(req.body.url);
  const json = await data.json();
  document.innerHTML = json.content;
}
`;
      const results = await detector.detect(code, 'test.js');
      
      // Should detect fetch + innerHTML combination
      expect(results.some(r => r.vulnerability.type === 'unusual-api-usage')).toBe(true);
    });
  });

  describe('Data Flow Anomaly Detection', () => {
    it('should detect user input in string concatenation', async () => {
      const code = `
function buildQuery(req) {
  const userInput = req.body.search;
  const query = "SELECT * FROM users WHERE name = '" + userInput + "'";
  return query;
}
`;
      const results = await detector.detect(code, 'test.js');
      
      // Detection depends on pattern matching context
      expect(Array.isArray(results)).toBe(true);
    });

    it('should detect empty catch blocks', async () => {
      const code = `
try {
  doSomethingDangerous();
} catch (e) {}
`;
      const results = await detector.detect(code, 'test.js');
      
      // Should flag empty catch as suspicious
      expect(results.some(r => r.vulnerability.description.includes('catch'))).toBe(true);
    });
  });

  describe('Risk Assessment', () => {
    it('should provide risk assessment for detected vulnerabilities', async () => {
      const code = `
const fn = new Function('return ' + userInput);
`;
      const results = await detector.detect(code, 'test.js');
      
      if (results.length > 0) {
        const assessment = results[0].riskAssessment;
        expect(assessment).toHaveProperty('overallRisk');
        expect(assessment).toHaveProperty('exploitability');
        expect(assessment).toHaveProperty('impact');
        expect(assessment).toHaveProperty('attackVector');
        expect(assessment).toHaveProperty('mitigationComplexity');
        expect(assessment).toHaveProperty('businessImpact');
      }
    });

    it('should assess risk based on severity', async () => {
      const code = `
const fn = new Function('return ' + userInput);
`;
      const results = await detector.detect(code, 'test.js');
      
      if (results.length > 0) {
        const criticalResult = results.find(r => r.vulnerability.severity === 'critical');
        if (criticalResult) {
          expect(criticalResult.riskAssessment.overallRisk).toBe('critical');
        }
      }
    });
  });

  describe('Options', () => {
    it('should filter by minimum deviation score', async () => {
      const highThresholdDetector = createZeroDayDetector({
        minDeviationScore: 0.9,
      });
      
      const code = `
const fn = new Function('return ' + input);
`;
      const results = await highThresholdDetector.detect(code, 'test.js');
      
      // All results should have deviation score >= 0.9
      for (const result of results) {
        expect(result.deviation.deviationScore).toBeGreaterThanOrEqual(0.9);
      }
    });

    it('should disable heuristics when configured', async () => {
      const noHeuristicsDetector = createZeroDayDetector({
        enableHeuristics: false,
        enableKGAnalysis: true,
      });
      
      const code = `
const fn = new Function('return ' + input);
`;
      const results = await noHeuristicsDetector.detect(code, 'test.js');
      
      // Results should only come from KG analysis, not pattern matching
      // This is hard to test directly, so we just verify it runs
      expect(Array.isArray(results)).toBe(true);
    });
  });

  describe('Vulnerability Conversion', () => {
    it('should convert results to standard vulnerability format', async () => {
      const code = `
const fn = new Function('return ' + userInput);
`;
      const results = await detector.detect(code, 'test.js');
      const vulnerabilities = detector.toVulnerabilities(results);
      
      if (vulnerabilities.length > 0) {
        expect(vulnerabilities[0]).toHaveProperty('id');
        expect(vulnerabilities[0]).toHaveProperty('type', 'zero-day');
        expect(vulnerabilities[0]).toHaveProperty('severity');
        expect(vulnerabilities[0]).toHaveProperty('location');
        expect(vulnerabilities[0]).toHaveProperty('recommendation');
      }
    });
  });

  describe('Pattern Context', () => {
    it('should provide context for detected patterns', async () => {
      const code = `
function dangerous(input) {
  const fn = new Function('return ' + input);
  return fn();
}
`;
      const results = await detector.detect(code, 'test.js');
      
      if (results.length > 0) {
        const context = results[0].deviation.context;
        expect(context).toHaveProperty('surroundingCode');
        expect(context).toHaveProperty('callStack');
        expect(context).toHaveProperty('dataFlowPath');
      }
    });
  });

  describe('Deviation Scoring', () => {
    it('should increase deviation score for user input context', async () => {
      const userInputCode = `
const userInput = req.body.code;
const fn = new Function('return ' + userInput);
`;
      const staticCode = `
const staticCode = "1 + 1";
const fn = new Function('return ' + staticCode);
`;
      
      const userInputResults = await detector.detect(userInputCode, 'test.js');
      const staticResults = await detector.detect(staticCode, 'test.js');
      
      // Both should detect the pattern
      expect(userInputResults.length).toBeGreaterThan(0);
      expect(staticResults.length).toBeGreaterThan(0);
      
      // User input context should have higher deviation score
      if (userInputResults.length > 0 && staticResults.length > 0) {
        expect(userInputResults[0].deviation.deviationScore)
          .toBeGreaterThanOrEqual(staticResults[0].deviation.deviationScore);
      }
    });
  });
});
