import { describe, it, expect } from 'vitest';
import {
  toPascalCase,
  toCamelCase,
  toSnakeCase,
  toKebabCase,
} from '../string-casing.js';

describe('toPascalCase', () => {
  it('should convert snake_case', () => {
    expect(toPascalCase('blog_platform')).toBe('BlogPlatform');
  });

  it('should convert UPPER_CASE', () => {
    expect(toPascalCase('BLOG_PLATFORM')).toBe('BlogPlatform');
  });

  it('should convert kebab-case', () => {
    expect(toPascalCase('blog-platform')).toBe('BlogPlatform');
  });

  it('should preserve already PascalCase strings', () => {
    expect(toPascalCase('BlogPlatform')).toBe('BlogPlatform');
    expect(toPascalCase('UserAccountEntity')).toBe('UserAccountEntity');
  });

  it('should preserve known suffixes', () => {
    expect(toPascalCase('BLOG_PLATFORMService')).toBe('BlogPlatformService');
    expect(toPascalCase('user_accountRepository')).toBe(
      'UserAccountRepository'
    );
  });

  it('should convert camelCase', () => {
    expect(toPascalCase('blogPlatform')).toBe('BlogPlatform');
  });

  it('should handle single word', () => {
    expect(toPascalCase('blog')).toBe('Blog');
    expect(toPascalCase('BLOG')).toBe('Blog');
  });

  it('should handle empty string', () => {
    expect(toPascalCase('')).toBe('');
  });

  it('should handle space-separated words', () => {
    expect(toPascalCase('blog platform')).toBe('BlogPlatform');
  });
});

describe('toCamelCase', () => {
  it('should convert snake_case', () => {
    expect(toCamelCase('blog_platform')).toBe('blogPlatform');
  });

  it('should convert UPPER_CASE', () => {
    expect(toCamelCase('BLOG_PLATFORM')).toBe('blogPlatform');
  });

  it('should convert kebab-case', () => {
    expect(toCamelCase('blog-platform')).toBe('blogPlatform');
  });

  it('should convert PascalCase', () => {
    expect(toCamelCase('BlogPlatform')).toBe('blogPlatform');
  });

  it('should handle single word', () => {
    expect(toCamelCase('blog')).toBe('blog');
    expect(toCamelCase('BLOG')).toBe('blog');
  });

  it('should handle empty string', () => {
    expect(toCamelCase('')).toBe('');
  });

  it('should handle space-separated words', () => {
    expect(toCamelCase('blog platform')).toBe('blogPlatform');
  });
});

describe('toSnakeCase', () => {
  it('should convert PascalCase', () => {
    expect(toSnakeCase('BlogPlatform')).toBe('blog_platform');
  });

  it('should convert camelCase', () => {
    expect(toSnakeCase('blogPlatform')).toBe('blog_platform');
  });

  it('should convert kebab-case', () => {
    expect(toSnakeCase('blog-platform')).toBe('blog_platform');
  });

  it('should convert space-separated', () => {
    expect(toSnakeCase('blog platform')).toBe('blog_platform');
  });

  it('should handle single word', () => {
    expect(toSnakeCase('blog')).toBe('blog');
  });

  it('should handle empty string', () => {
    expect(toSnakeCase('')).toBe('');
  });

  it('should handle already snake_case', () => {
    expect(toSnakeCase('blog_platform')).toBe('blog_platform');
  });
});

describe('toKebabCase', () => {
  it('should convert PascalCase', () => {
    expect(toKebabCase('BlogPlatform')).toBe('blog-platform');
  });

  it('should convert camelCase', () => {
    expect(toKebabCase('blogPlatform')).toBe('blog-platform');
  });

  it('should handle consecutive uppercase (acronyms)', () => {
    expect(toKebabCase('XMLParser')).toBe('xml-parser');
    expect(toKebabCase('HTMLElement')).toBe('html-element');
  });

  it('should convert snake_case', () => {
    expect(toKebabCase('blog_platform')).toBe('blog-platform');
  });

  it('should convert space-separated', () => {
    expect(toKebabCase('blog platform')).toBe('blog-platform');
  });

  it('should handle single word', () => {
    expect(toKebabCase('blog')).toBe('blog');
  });

  it('should handle empty string', () => {
    expect(toKebabCase('')).toBe('');
  });

  it('should handle already kebab-case', () => {
    expect(toKebabCase('blog-platform')).toBe('blog-platform');
  });

  it('should handle UPPER_CASE', () => {
    expect(toKebabCase('BLOG_PLATFORM')).toBe('blog-platform');
  });
});
