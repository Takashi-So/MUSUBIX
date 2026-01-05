/**
 * @fileoverview Ontology MCP tests
 * @traceability TSK-ONTO-001, TSK-ONTO-008
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { OntologyStore } from '../store/ontology-store.js';
import { OntologyPrivacyGuard } from '../privacy/privacy-guard.js';

describe('OntologyStore', () => {
  let store: OntologyStore;

  beforeEach(() => {
    store = new OntologyStore({
      storagePath: '/tmp/test-ontology.json',
    });
  });

  it('should start with empty store', () => {
    expect(store.size).toBe(0);
  });

  it('should create ontology', () => {
    const onto = store.create('test-onto', 'http://example.org/');
    expect(onto.id).toBe('test-onto');
    expect(onto.namespace).toBe('http://example.org/');
    expect(store.size).toBe(1);
  });

  it('should add and retrieve triples', () => {
    store.create('test-onto', 'http://example.org/');
    
    const triple = {
      subject: 'http://example.org/Alice',
      predicate: 'http://example.org/knows',
      object: 'http://example.org/Bob',
    };

    expect(store.addTriple('test-onto', triple)).toBe(true);
    expect(store.getTriples('test-onto')).toHaveLength(1);
  });

  it('should delete ontology', () => {
    store.create('test-onto', 'http://example.org/');
    expect(store.delete('test-onto')).toBe(true);
    expect(store.size).toBe(0);
  });
});

describe('OntologyPrivacyGuard', () => {
  let guard: OntologyPrivacyGuard;

  beforeEach(() => {
    guard = new OntologyPrivacyGuard();
  });

  it('should block external communication by default', () => {
    expect(guard.isExternalCommunicationBlocked()).toBe(true);
  });

  it('should enforce local storage only', () => {
    expect(guard.isLocalStorageOnly()).toBe(true);
  });

  it('should validate local paths', () => {
    expect(guard.validateStoragePath('./storage/data.json')).toBe(true);
    expect(guard.validateStoragePath('/tmp/data.json')).toBe(true);
  });

  it('should reject remote paths', () => {
    expect(guard.validateStoragePath('https://example.com/data.json')).toBe(false);
    expect(guard.validateStoragePath('s3://bucket/data.json')).toBe(false);
  });

  it('should throw on privacy violation', () => {
    expect(() => {
      guard.assertPrivacyConstraints('https://remote.com/data.json');
    }).toThrow('Privacy violation');
  });
});
