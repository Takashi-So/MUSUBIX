/**
 * EventHub Pro - Main Application Entry Point
 *
 * @module index
 * @description Exports all services and types for the EventHub Pro booking system
 * @traces REQ-EVENT-001 through REQ-EVENT-019
 */

// ============================================================
// Event Service
// ============================================================
export {
  type Event,
  type EventCategory,
  type EventStatus,
  type Venue,
  type TicketType,
  type CreateEventInput,
  type UpdateEventInput,
  type EventSearchOptions,
  type EventSearchResult,
  type IEventService,
  type IEventRepository,
  EventService,
  createEventService,
} from './event-service';

// ============================================================
// Ticket Service
// ============================================================
export {
  type Ticket,
  type TicketStatus,
  type SeatInfo,
  type Order,
  type OrderStatus,
  type PurchaseTicketInput,
  type TransferTicketInput,
  type RefundResult,
  type ITicketService,
  type ITicketRepository,
  type IOrderRepository,
  TicketService,
  createTicketService,
} from './ticket-service';

// ============================================================
// Seat Service
// ============================================================
export {
  type Seat,
  type SeatCategory,
  type SeatStatus,
  type SeatSection,
  type SeatRow,
  type VenueLayout,
  type SeatReservation,
  type CreateLayoutInput,
  type ReserveSeatInput,
  type ISeatService,
  type ISeatRepository,
  type ILayoutRepository,
  type IReservationRepository,
  SeatService,
  createSeatService,
} from './seat-service';

// ============================================================
// CheckIn Service
// ============================================================
export {
  type CheckInRecord,
  type CheckInStats,
  type CheckInResult,
  type OfflineCheckInData,
  type SyncResult,
  type ICheckInService,
  type ICheckInRepository,
  type ITicketCache,
  type CachedTicket,
  type ITicketServiceAdapter,
  CheckInService,
  createCheckInService,
} from './checkin-service';
