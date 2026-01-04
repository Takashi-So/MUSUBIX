/**
 * Budget Tracker - Main Entry Point
 */

// Shared
export * from './shared/result.js';

// Domain - Value Objects
export * from './domain/value-objects/index.js';

// Domain - Entities
export * from './domain/entities/index.js';

// Domain - Repositories
export * from './domain/repositories/interfaces.js';

// Application Services
export { CategoryService, CreateCategoryInput, CategoryWithSpending } from './application/category-service.js';
