/**
 * EventService Unit Tests
 *
 * @module __tests__/event-service.test
 * @traces REQ-EVENT-001, REQ-EVENT-002, REQ-EVENT-003, REQ-EVENT-004
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  EventService,
  type Event,
  type EventCategory,
  type Venue,
  type IEventRepository,
  type EventSearchOptions,
} from '../src/event-service';

// ============================================================
// Mock Implementation
// ============================================================

function createMockEventRepository(): IEventRepository {
  const events = new Map<string, Event>();

  return {
    save: vi.fn(async (event: Event) => {
      events.set(event.id, { ...event });
      return event;
    }),
    findById: vi.fn(async (id: string) => {
      const event = events.get(id);
      return event ? { ...event } : null;
    }),
    findByOrganizer: vi.fn(async (organizerId: string) => {
      return Array.from(events.values()).filter((e) => e.organizerId === organizerId);
    }),
    search: vi.fn(async (options: EventSearchOptions) => {
      let results = Array.from(events.values());

      if (options.category) {
        results = results.filter((e) => e.category === options.category);
      }
      if (options.keyword) {
        const kw = options.keyword.toLowerCase();
        results = results.filter(
          (e) =>
            e.title.toLowerCase().includes(kw) ||
            e.description.toLowerCase().includes(kw)
        );
      }
      if (options.dateFrom) {
        results = results.filter((e) => e.startDate >= options.dateFrom!);
      }
      if (options.dateTo) {
        results = results.filter((e) => e.startDate <= options.dateTo!);
      }

      return {
        events: results.slice(options.offset || 0, (options.offset || 0) + (options.limit || 20)),
        total: results.length,
      };
    }),
    update: vi.fn(async (id: string, data: Partial<Event>) => {
      const event = events.get(id);
      if (!event) throw new Error('Event not found');
      const updated = { ...event, ...data, updatedAt: new Date() };
      events.set(id, updated);
      return updated;
    }),
    delete: vi.fn(async (id: string) => {
      events.delete(id);
      return true;
    }),
  };
}

function createTestVenue(): Venue {
  return {
    name: 'Test Venue',
    address: '123 Test St',
    city: 'Tokyo',
    country: 'Japan',
    postalCode: '100-0001',
    coordinates: { lat: 35.6762, lng: 139.6503 },
    capacity: 1000,
  };
}

// ============================================================
// Test Suites
// ============================================================

describe('EventService', () => {
  let service: EventService;
  let repository: IEventRepository;

  beforeEach(() => {
    repository = createMockEventRepository();
    service = new EventService(repository);
  });

  // ==========================================================
  // REQ-EVENT-001: イベント作成
  // ==========================================================
  describe('REQ-EVENT-001: Event Creation', () => {
    it('should create a new event with valid input', async () => {
      const input = {
        title: 'Summer Music Festival',
        description: 'Annual outdoor music festival',
        category: 'concert' as EventCategory,
        venue: createTestVenue(),
        startDate: new Date('2025-07-15T18:00:00Z'),
        endDate: new Date('2025-07-15T23:00:00Z'),
        organizerId: 'org-1',
        capacity: 1000,
        ticketTypes: [
          {
            name: 'General Admission',
            description: 'Standard entry',
            price: 50,
            quantity: 800,
            maxPerOrder: 10,
            salesStart: new Date('2025-01-01'),
            salesEnd: new Date('2025-07-14'),
            isActive: true,
          },
        ],
      };

      const result = await service.createEvent(input);

      expect(result).toBeDefined();
      expect(result.id).toMatch(/^EVT-/);
      expect(result.title).toBe('Summer Music Festival');
      expect(result.status).toBe('draft');
      expect(repository.save).toHaveBeenCalledTimes(1);
    });

    it('should generate unique event IDs', async () => {
      const input = {
        title: 'Test Event',
        description: 'Test',
        category: 'conference' as EventCategory,
        venue: createTestVenue(),
        startDate: new Date('2025-08-01'),
        endDate: new Date('2025-08-02'),
        organizerId: 'org-1',
        capacity: 100,
        ticketTypes: [],
      };

      const event1 = await service.createEvent(input);
      const event2 = await service.createEvent(input);

      expect(event1.id).not.toBe(event2.id);
    });

    it('should initialize event with draft status', async () => {
      const input = {
        title: 'Draft Event',
        description: 'New event',
        category: 'workshop' as EventCategory,
        venue: createTestVenue(),
        startDate: new Date('2025-09-01'),
        endDate: new Date('2025-09-01'),
        organizerId: 'org-1',
        capacity: 50,
        ticketTypes: [],
      };

      const result = await service.createEvent(input);

      expect(result.status).toBe('draft');
      expect(result.ticketsSold).toBe(0);
    });

    it('should assign ticket type IDs automatically', async () => {
      const input = {
        title: 'Event With Tickets',
        description: 'Has ticket types',
        category: 'seminar' as EventCategory,
        venue: createTestVenue(),
        startDate: new Date('2025-10-01'),
        endDate: new Date('2025-10-01'),
        organizerId: 'org-1',
        capacity: 200,
        ticketTypes: [
          {
            name: 'Standard',
            description: 'Standard ticket',
            price: 30,
            quantity: 150,
            maxPerOrder: 5,
            salesStart: new Date('2025-01-01'),
            salesEnd: new Date('2025-09-30'),
            isActive: true,
          },
          {
            name: 'VIP',
            description: 'VIP access',
            price: 100,
            quantity: 50,
            maxPerOrder: 2,
            salesStart: new Date('2025-01-01'),
            salesEnd: new Date('2025-09-30'),
            isActive: true,
          },
        ],
      };

      const result = await service.createEvent(input);

      expect(result.ticketTypes.length).toBe(2);
      expect(result.ticketTypes[0].id).toMatch(/^TT-/);
      expect(result.ticketTypes[1].id).toMatch(/^TT-/);
    });
  });

  // ==========================================================
  // REQ-EVENT-002: イベント検索
  // ==========================================================
  describe('REQ-EVENT-002: Event Search', () => {
    beforeEach(async () => {
      await service.createEvent({
        title: 'Rock Concert',
        description: 'Amazing rock show',
        category: 'concert',
        venue: createTestVenue(),
        startDate: new Date('2025-06-01'),
        endDate: new Date('2025-06-01'),
        organizerId: 'org-1',
        capacity: 5000,
        ticketTypes: [],
      });
      await service.createEvent({
        title: 'Tech Conference',
        description: 'Latest technology trends',
        category: 'conference',
        venue: createTestVenue(),
        startDate: new Date('2025-07-15'),
        endDate: new Date('2025-07-17'),
        organizerId: 'org-2',
        capacity: 2000,
        ticketTypes: [],
      });
      await service.createEvent({
        title: 'Jazz Night',
        description: 'Smooth jazz evening',
        category: 'concert',
        venue: createTestVenue(),
        startDate: new Date('2025-08-01'),
        endDate: new Date('2025-08-01'),
        organizerId: 'org-1',
        capacity: 200,
        ticketTypes: [],
      });
    });

    it('should search events by category', async () => {
      const result = await service.searchEvents({ category: 'concert' });

      expect(result.events.length).toBe(2);
      expect(result.events.every((e) => e.category === 'concert')).toBe(true);
    });

    it('should search events by keyword', async () => {
      const result = await service.searchEvents({ keyword: 'Tech' });

      expect(result.events.length).toBe(1);
      expect(result.events[0].title).toBe('Tech Conference');
    });

    it('should search events by date range', async () => {
      const result = await service.searchEvents({
        dateFrom: new Date('2025-07-01'),
        dateTo: new Date('2025-07-31'),
      });

      expect(result.events.length).toBe(1);
      expect(result.events[0].title).toBe('Tech Conference');
    });

    it('should return results with total count', async () => {
      const result = await service.searchEvents({});

      expect(result.total).toBe(3);
    });
  });

  // ==========================================================
  // REQ-EVENT-003: イベント公開
  // ==========================================================
  describe('REQ-EVENT-003: Event Publishing', () => {
    it('should publish a draft event with ticket types', async () => {
      const event = await service.createEvent({
        title: 'Publishable Event',
        description: 'Ready to publish',
        category: 'workshop',
        venue: createTestVenue(),
        startDate: new Date('2025-09-01'),
        endDate: new Date('2025-09-01'),
        organizerId: 'org-1',
        capacity: 50,
        ticketTypes: [
          {
            name: 'Standard',
            description: 'Standard entry',
            price: 100,
            quantity: 50,
            maxPerOrder: 5,
            salesStart: new Date('2025-01-01'),
            salesEnd: new Date('2025-08-31'),
            isActive: true,
          },
        ],
      });

      const published = await service.publishEvent(event.id);

      expect(published.status).toBe('published');
    });

    it('should reject publishing event without ticket types', async () => {
      const event = await service.createEvent({
        title: 'No Tickets Event',
        description: 'Missing tickets',
        category: 'seminar',
        venue: createTestVenue(),
        startDate: new Date('2025-11-01'),
        endDate: new Date('2025-11-01'),
        organizerId: 'org-1',
        capacity: 100,
        ticketTypes: [],
      });

      await expect(service.publishEvent(event.id)).rejects.toThrow();
    });
  });

  // ==========================================================
  // REQ-EVENT-004: イベントキャンセル
  // ==========================================================
  describe('REQ-EVENT-004: Event Cancellation', () => {
    it('should cancel a published event', async () => {
      const event = await service.createEvent({
        title: 'Cancelable Event',
        description: 'May be cancelled',
        category: 'festival',
        venue: createTestVenue(),
        startDate: new Date('2025-12-01'),
        endDate: new Date('2025-12-03'),
        organizerId: 'org-1',
        capacity: 200,
        ticketTypes: [
          {
            name: 'Entry',
            description: 'General entry',
            price: 25,
            quantity: 200,
            maxPerOrder: 10,
            salesStart: new Date('2025-01-01'),
            salesEnd: new Date('2025-11-30'),
            isActive: true,
          },
        ],
      });

      await service.publishEvent(event.id);
      const cancelled = await service.cancelEvent(event.id, 'Venue unavailable');

      expect(cancelled.status).toBe('cancelled');
    });

    it('should reject cancelling non-existent event', async () => {
      await expect(
        service.cancelEvent('non-existent-id', 'Reason')
      ).rejects.toThrow('Event not found');
    });
  });

  // ==========================================================
  // Event Update & Retrieval Tests
  // ==========================================================
  describe('Event Update & Retrieval', () => {
    it('should update event details', async () => {
      const event = await service.createEvent({
        title: 'Original Title',
        description: 'Original description',
        category: 'seminar',
        venue: createTestVenue(),
        startDate: new Date('2025-06-01'),
        endDate: new Date('2025-06-01'),
        organizerId: 'org-1',
        capacity: 100,
        ticketTypes: [],
      });

      const updated = await service.updateEvent(event.id, {
        title: 'Updated Title',
        description: 'New description',
      });

      expect(updated.title).toBe('Updated Title');
      expect(updated.description).toBe('New description');
    });

    it('should get event by ID', async () => {
      const created = await service.createEvent({
        title: 'Retrievable Event',
        description: 'Can be retrieved',
        category: 'other',
        venue: createTestVenue(),
        startDate: new Date('2025-07-01'),
        endDate: new Date('2025-07-01'),
        organizerId: 'org-1',
        capacity: 100,
        ticketTypes: [],
      });

      const retrieved = await service.getEvent(created.id);

      expect(retrieved).toBeDefined();
      expect(retrieved?.id).toBe(created.id);
    });

    it('should return null for non-existent event', async () => {
      const result = await service.getEvent('non-existent-id');

      expect(result).toBeNull();
    });

    it('should get events by organizer', async () => {
      await service.createEvent({
        title: 'Org Event 1',
        description: 'First event',
        category: 'concert',
        venue: createTestVenue(),
        startDate: new Date('2025-05-01'),
        endDate: new Date('2025-05-01'),
        organizerId: 'org-specific',
        capacity: 100,
        ticketTypes: [],
      });

      await service.createEvent({
        title: 'Org Event 2',
        description: 'Second event',
        category: 'workshop',
        venue: createTestVenue(),
        startDate: new Date('2025-06-01'),
        endDate: new Date('2025-06-01'),
        organizerId: 'org-specific',
        capacity: 50,
        ticketTypes: [],
      });

      const events = await service.getEventsByOrganizer('org-specific');

      expect(events.length).toBe(2);
    });
  });
});
