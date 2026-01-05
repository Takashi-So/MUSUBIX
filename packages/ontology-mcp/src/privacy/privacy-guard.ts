/**
 * @fileoverview Privacy guard for ontology store
 * @traceability TSK-ONTO-008, REQ-ONTO-001-F008
 */

/**
 * Privacy guard configuration
 */
export interface PrivacyGuardConfig {
  /** Block all external network calls */
  blockExternalCommunication: boolean;
  /** Allow only local file system storage */
  localStorageOnly: boolean;
}

/**
 * Privacy guard to ensure ontology data stays local
 * 
 * @description
 * - All data stored locally only
 * - No external network communication
 * - Enforces local-first architecture
 */
export class OntologyPrivacyGuard {
  private config: PrivacyGuardConfig;

  constructor(config: Partial<PrivacyGuardConfig> = {}) {
    this.config = {
      blockExternalCommunication: config.blockExternalCommunication ?? true,
      localStorageOnly: config.localStorageOnly ?? true,
    };
  }

  /**
   * Check if external communication is blocked
   */
  isExternalCommunicationBlocked(): boolean {
    return this.config.blockExternalCommunication;
  }

  /**
   * Check if storage is local only
   */
  isLocalStorageOnly(): boolean {
    return this.config.localStorageOnly;
  }

  /**
   * Validate storage path is local
   */
  validateStoragePath(path: string): boolean {
    if (!this.config.localStorageOnly) return true;

    // Block remote paths
    const remotePatterns = [
      /^https?:\/\//i,
      /^s3:\/\//i,
      /^gs:\/\//i,
      /^azure:\/\//i,
      /^ftp:\/\//i,
    ];

    return !remotePatterns.some(pattern => pattern.test(path));
  }

  /**
   * Assert privacy constraints
   * @throws Error if constraints are violated
   */
  assertPrivacyConstraints(storagePath: string): void {
    if (!this.validateStoragePath(storagePath)) {
      throw new Error(`Privacy violation: Remote storage path not allowed: ${storagePath}`);
    }
  }
}
