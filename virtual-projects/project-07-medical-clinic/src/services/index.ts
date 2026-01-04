/**
 * Services barrel export
 * @module services
 */

export { PatientService, type ServiceResult } from './patient-service.js';
export {
  AppointmentService,
  type BookingRequest,
  type RescheduleRequest,
} from './appointment-service.js';
