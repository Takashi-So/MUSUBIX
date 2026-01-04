/**
 * TicketService Unit Tests
 *
 * @module __tests__/ticket-service.test
 * @traces REQ-EVENT-005, REQ-EVENT-006, REQ-EVENT-007, REQ-EVENT-008
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import {
  TicketService,
  type Ticket,
  type Order,
  type ITicketRepository,
  type IOrderRepository,
} from '../src/ticket-service';

// ============================================================
// Mock Implementations
// ============================================================

function createMockTicketRepository(): ITicketRepository {
  const tickets = new Map<string, Ticket>();

  return {
    save: vi.fn(async (ticket: Ticket) => {
      tickets.set(ticket.id, { ...ticket });
      return ticket;
    }),
    saveMany: vi.fn(async (ticketList: Ticket[]) => {
      ticketList.forEach((t) => tickets.set(t.id, { ...t }));
      return ticketList;
    }),
    findById: vi.fn(async (id: string) => {
      const ticket = tickets.get(id);
      return ticket ? { ...ticket } : null;
    }),
    findByQR: vi.fn(async (qrCode: string) => {
      const ticket = Array.from(tickets.values()).find((t) => t.qrCode === qrCode);
      return ticket ? { ...ticket } : null;
    }),
    findByHolder: vi.fn(async (holderId: string) => {
      return Array.from(tickets.values()).filter((t) => t.holderId === holderId);
    }),
    findByEvent: vi.fn(async (eventId: string) => {
      return Array.from(tickets.values()).filter((t) => t.eventId === eventId);
    }),
    update: vi.fn(async (id: string, data: Partial<Ticket>) => {
      const ticket = tickets.get(id);
      if (!ticket) throw new Error('Ticket not found');
      const updated = { ...ticket, ...data };
      tickets.set(id, updated);
      return updated;
    }),
  };
}

function createMockOrderRepository(): IOrderRepository {
  const orders = new Map<string, Order>();

  return {
    save: vi.fn(async (order: Order) => {
      orders.set(order.id, { ...order });
      return order;
    }),
    findById: vi.fn(async (id: string) => {
      const order = orders.get(id);
      return order ? { ...order } : null;
    }),
    findByBuyer: vi.fn(async (buyerId: string) => {
      return Array.from(orders.values()).filter((o) => o.buyerId === buyerId);
    }),
    findByEvent: vi.fn(async (eventId: string) => {
      return Array.from(orders.values()).filter((o) => o.eventId === eventId);
    }),
    update: vi.fn(async (id: string, data: Partial<Order>) => {
      const order = orders.get(id);
      if (!order) throw new Error('Order not found');
      const updated = { ...order, ...data };
      orders.set(id, updated);
      return updated;
    }),
  };
}

// ============================================================
// Test Suites
// ============================================================

describe('TicketService', () => {
  let service: TicketService;
  let ticketRepo: ITicketRepository;
  let orderRepo: IOrderRepository;

  beforeEach(() => {
    ticketRepo = createMockTicketRepository();
    orderRepo = createMockOrderRepository();
    service = new TicketService(ticketRepo, orderRepo);
  });

  // ==========================================================
  // REQ-EVENT-005: チケット購入
  // ==========================================================
  describe('REQ-EVENT-005: Ticket Purchase', () => {
    it('should purchase tickets successfully', async () => {
      const input = {
        eventId: 'evt-001',
        ticketTypeId: 'tt-ga',
        quantity: 2,
        buyerId: 'user-001',
        buyerName: 'John Doe',
        buyerEmail: 'john@example.com',
      };

      const result = await service.purchaseTickets(input);

      expect(result).toBeDefined();
      expect(result.id).toMatch(/^ORD-/);
      expect(result.status).toBe('completed');
      expect(result.tickets.length).toBe(2);
    });

    it('should generate unique QR codes for each ticket', async () => {
      const input = {
        eventId: 'evt-001',
        ticketTypeId: 'tt-ga',
        quantity: 3,
        buyerId: 'user-002',
        buyerName: 'Jane Smith',
        buyerEmail: 'jane@example.com',
      };

      const result = await service.purchaseTickets(input);
      const qrCodes = result.tickets.map((t) => t.qrCode);
      const uniqueQrCodes = new Set(qrCodes);

      expect(uniqueQrCodes.size).toBe(3);
    });

    it('should calculate correct total amount', async () => {
      const input = {
        eventId: 'evt-001',
        ticketTypeId: 'tt-ga',
        quantity: 2,
        buyerId: 'user-003',
        buyerName: 'Test User',
        buyerEmail: 'test@example.com',
      };

      const result = await service.purchaseTickets(input);

      expect(result.totalAmount).toBe(result.tickets.reduce((sum, t) => sum + t.price, 0));
    });

    it('should set all tickets to active status', async () => {
      const input = {
        eventId: 'evt-001',
        ticketTypeId: 'tt-vip',
        quantity: 2,
        buyerId: 'user-004',
        buyerName: 'VIP User',
        buyerEmail: 'vip@example.com',
      };

      const result = await service.purchaseTickets(input);

      expect(result.tickets.every((t) => t.status === 'active')).toBe(true);
    });
  });

  // ==========================================================
  // REQ-EVENT-006: チケット譲渡
  // ==========================================================
  describe('REQ-EVENT-006: Ticket Transfer', () => {
    let testOrder: Order;

    beforeEach(async () => {
      testOrder = await service.purchaseTickets({
        eventId: 'evt-transfer',
        ticketTypeId: 'tt-ga',
        quantity: 1,
        buyerId: 'original-owner',
        buyerName: 'Original Owner',
        buyerEmail: 'original@example.com',
      });
    });

    it('should transfer ticket to new holder', async () => {
      const ticket = testOrder.tickets[0];
      
      const result = await service.transferTicket({
        ticketId: ticket.id,
        currentHolderId: 'original-owner',
        newHolderName: 'New Owner',
        newHolderEmail: 'new@example.com',
      });

      expect(result.holderName).toBe('New Owner');
      expect(result.holderEmail).toBe('new@example.com');
      expect(result.status).toBe('transferred');
    });

    it('should reject transfer from non-owner', async () => {
      const ticket = testOrder.tickets[0];

      await expect(
        service.transferTicket({
          ticketId: ticket.id,
          currentHolderId: 'wrong-user',
          newHolderName: 'Attacker',
          newHolderEmail: 'attacker@example.com',
        })
      ).rejects.toThrow();
    });
  });

  // ==========================================================
  // REQ-EVENT-007: チケットキャンセル・返金
  // ==========================================================
  describe('REQ-EVENT-007: Ticket Cancellation', () => {
    let testOrder: Order;

    beforeEach(async () => {
      testOrder = await service.purchaseTickets({
        eventId: 'evt-cancel',
        ticketTypeId: 'tt-ga',
        quantity: 2,
        buyerId: 'cancel-user',
        buyerName: 'Cancel User',
        buyerEmail: 'cancel@example.com',
      });
    });

    it('should cancel ticket and calculate refund', async () => {
      const ticket = testOrder.tickets[0];

      const result = await service.cancelTicket(ticket.id, 'cancel-user');

      expect(result.success).toBe(true);
      expect(result.ticketId).toBe(ticket.id);
      expect(result.refundAmount).toBeGreaterThan(0);
    });

    it('should reject cancel from non-holder', async () => {
      const ticket = testOrder.tickets[0];

      const result = await service.cancelTicket(ticket.id, 'wrong-user');

      expect(result.success).toBe(false);
    });
  });

  // ==========================================================
  // REQ-EVENT-008: チケット検証
  // ==========================================================
  describe('REQ-EVENT-008: Ticket Validation', () => {
    let validOrder: Order;

    beforeEach(async () => {
      validOrder = await service.purchaseTickets({
        eventId: 'evt-validate',
        ticketTypeId: 'tt-ga',
        quantity: 1,
        buyerId: 'validate-user',
        buyerName: 'Validate User',
        buyerEmail: 'validate@example.com',
      });
    });

    it('should validate active ticket', async () => {
      const ticket = validOrder.tickets[0];

      const result = await service.validateTicket(ticket.qrCode);

      expect(result.valid).toBe(true);
      expect(result.ticket).toBeDefined();
    });

    it('should reject invalid QR code', async () => {
      const result = await service.validateTicket('invalid-qr-code');

      expect(result.valid).toBe(false);
      expect(result.message).toBe('Invalid ticket');
    });
  });

  // ==========================================================
  // Ticket Retrieval Tests
  // ==========================================================
  describe('Ticket Retrieval', () => {
    beforeEach(async () => {
      await service.purchaseTickets({
        eventId: 'evt-001',
        ticketTypeId: 'tt-ga',
        quantity: 2,
        buyerId: 'retrieval-user',
        buyerName: 'Retrieval User',
        buyerEmail: 'retrieval@example.com',
      });
    });

    it('should get tickets by holder', async () => {
      const tickets = await service.getTicketsByHolder('retrieval-user');

      expect(tickets.length).toBe(2);
    });

    it('should get tickets by event', async () => {
      const tickets = await service.getEventTickets('evt-001');

      expect(tickets.length).toBe(2);
    });

    it('should get orders by buyer', async () => {
      const orders = await service.getOrdersByBuyer('retrieval-user');

      expect(orders.length).toBe(1);
    });
  });
});
