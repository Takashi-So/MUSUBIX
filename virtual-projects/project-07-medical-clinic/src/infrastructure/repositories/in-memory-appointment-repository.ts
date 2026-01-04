/**
 * InMemoryAppointmentRepository
 * 
 * In-memory implementation of IAppointmentRepository for testing
 * 
 * @requirement REQ-CLINIC-001-F010 Appointment Booking
 * @design DES-CLINIC-001 Section 5.1 Repository Pattern
 */

import type { IAppointmentRepository } from '../../domain/repositories/appointment-repository.js';
import type {
  Appointment,
  CreateAppointmentDTO,
  UpdateAppointmentDTO,
  TimeSlot,
  AppointmentStatus,
} from '../../domain/entities/appointment.js';

/**
 * In-memory implementation of the Appointment Repository
 */
export class InMemoryAppointmentRepository implements IAppointmentRepository {
  private appointments: Map<string, Appointment> = new Map();
  private idCounter = 0;
  private customSlots: Map<string, TimeSlot[]> = new Map();

  // Default working hours 9:00 to 17:00
  private readonly WORK_START_HOUR = 9;
  private readonly WORK_END_HOUR = 17;
  private readonly DEFAULT_SLOT_DURATION = 30; // minutes

  /**
   * Test helper: Set custom available slots for a doctor on a date
   */
  setAvailableSlots(doctorId: string, date: Date, slots: TimeSlot[]): void {
    const dateKey = `${doctorId}-${date.toISOString().split('T')[0]}`;
    this.customSlots.set(dateKey, slots);
  }

  /**
   * Test helper: Clear all custom slots
   */
  clearCustomSlots(): void {
    this.customSlots.clear();
  }

  async findById(id: string): Promise<Appointment | null> {
    return this.appointments.get(id) || null;
  }

  async findByPatientId(patientId: string): Promise<Appointment[]> {
    return Array.from(this.appointments.values()).filter(
      (a) => a.patientId === patientId
    );
  }

  async findByDoctorId(doctorId: string): Promise<Appointment[]> {
    return Array.from(this.appointments.values()).filter(
      (a) => a.doctorId === doctorId
    );
  }

  async findByDoctorAndDateRange(
    doctorId: string,
    startDate: Date,
    endDate: Date
  ): Promise<Appointment[]> {
    return Array.from(this.appointments.values()).filter(
      (a) =>
        a.doctorId === doctorId &&
        a.dateTime >= startDate &&
        a.dateTime <= endDate
    );
  }

  async create(data: CreateAppointmentDTO): Promise<Appointment> {
    const id = `APT-${++this.idCounter}`;
    const now = new Date();
    
    const appointment: Appointment = {
      id,
      patientId: data.patientId,
      doctorId: data.doctorId,
      dateTime: data.dateTime,
      duration: data.duration || this.DEFAULT_SLOT_DURATION,
      type: data.type,
      status: data.status || 'scheduled',
      notes: data.notes,
      createdAt: now,
      updatedAt: now,
    };

    this.appointments.set(id, appointment);
    return appointment;
  }

  async update(id: string, data: UpdateAppointmentDTO): Promise<Appointment> {
    const existing = this.appointments.get(id);
    if (!existing) {
      throw new Error('Appointment not found');
    }

    const updated: Appointment = {
      ...existing,
      ...data,
      updatedAt: new Date(),
    };

    this.appointments.set(id, updated);
    return updated;
  }

  async delete(id: string): Promise<void> {
    if (!this.appointments.has(id)) {
      throw new Error('Appointment not found');
    }
    this.appointments.delete(id);
  }

  async getAvailableSlots(doctorId: string, date: Date): Promise<TimeSlot[]> {
    // Check for custom slots first (used in testing)
    const dateKey = `${doctorId}-${date.toISOString().split('T')[0]}`;
    if (this.customSlots.has(dateKey)) {
      return this.customSlots.get(dateKey)!;
    }

    const slots: TimeSlot[] = [];
    const dateStart = new Date(date);
    dateStart.setHours(0, 0, 0, 0);
    const dateEnd = new Date(date);
    dateEnd.setHours(23, 59, 59, 999);

    // Get all appointments for this doctor on this date
    const doctorAppointments = await this.findByDoctorAndDateRange(
      doctorId,
      dateStart,
      dateEnd
    );

    // Generate slots from work start to work end
    for (let hour = this.WORK_START_HOUR; hour < this.WORK_END_HOUR; hour++) {
      for (let minute = 0; minute < 60; minute += this.DEFAULT_SLOT_DURATION) {
        const slotStart = new Date(date);
        slotStart.setHours(hour, minute, 0, 0);
        
        const slotEnd = new Date(slotStart);
        slotEnd.setMinutes(slotEnd.getMinutes() + this.DEFAULT_SLOT_DURATION);

        // Check if this slot conflicts with any existing appointment
        const isBooked = doctorAppointments.some((appt) => {
          if (appt.status === 'cancelled' || appt.status === 'completed' || appt.status === 'no_show') {
            return false;
          }
          const apptEnd = new Date(appt.dateTime);
          apptEnd.setMinutes(apptEnd.getMinutes() + appt.duration);
          
          return (
            slotStart.getTime() < apptEnd.getTime() &&
            slotEnd.getTime() > appt.dateTime.getTime()
          );
        });

        slots.push({
          startTime: slotStart,
          endTime: slotEnd,
          doctorId,
          isAvailable: !isBooked,
        });
      }
    }

    return slots;
  }

  async findByStatus(status: AppointmentStatus): Promise<Appointment[]> {
    return Array.from(this.appointments.values()).filter(
      (a) => a.status === status
    );
  }

  async findUpcoming(withinMinutes: number): Promise<Appointment[]> {
    const now = new Date();
    const futureTime = new Date(now.getTime() + withinMinutes * 60 * 1000);

    return Array.from(this.appointments.values()).filter(
      (a) =>
        a.dateTime >= now &&
        a.dateTime <= futureTime &&
        (a.status === 'scheduled' || a.status === 'confirmed')
    );
  }
}
