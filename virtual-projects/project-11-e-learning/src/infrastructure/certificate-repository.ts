/**
 * InMemory Certificate Repository
 * Traceability: DES-ELEARN-001 §6.1
 */

import type { Certificate, CertificateId, EnrollmentId } from '../domain/types.js';

export interface CertificateRepository {
  save(certificate: Certificate): Promise<void>;
  findById(id: CertificateId): Promise<Certificate | null>;
  findByEnrollmentId(enrollmentId: EnrollmentId): Promise<Certificate | null>;
}

export class InMemoryCertificateRepository implements CertificateRepository {
  private certificates: Map<CertificateId, Certificate> = new Map();

  async save(certificate: Certificate): Promise<void> {
    this.certificates.set(certificate.id, { ...certificate });
  }

  async findById(id: CertificateId): Promise<Certificate | null> {
    const certificate = this.certificates.get(id);
    return certificate ? { ...certificate } : null;
  }

  async findByEnrollmentId(enrollmentId: EnrollmentId): Promise<Certificate | null> {
    for (const certificate of this.certificates.values()) {
      if (certificate.enrollmentId === enrollmentId) {
        return { ...certificate };
      }
    }
    return null;
  }

  // For testing
  clear(): void {
    this.certificates.clear();
  }
}
