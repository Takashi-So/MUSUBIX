/**
 * @fileoverview Custom error classes for musubix-lean package
 * @module @nahisaho/musubix-lean/errors
 * @traceability REQ-LEAN-ERR-001, REQ-LEAN-ERR-002
 */

/**
 * Base error class for Lean-related errors
 */
export class LeanError extends Error {
  constructor(
    message: string,
    public readonly code: string,
    public readonly cause?: Error
  ) {
    super(message);
    this.name = 'LeanError';
  }
}

/**
 * Error thrown when Lean 4 is not installed
 * @traceability REQ-LEAN-ERR-001
 */
export class LeanNotFoundError extends LeanError {
  constructor(os: string) {
    const instructions = getInstallInstructions(os);
    super(
      `Lean 4 is not installed on this system.\n\n${instructions}`,
      'LEAN_NOT_FOUND'
    );
    this.name = 'LeanNotFoundError';
  }
}

/**
 * Error thrown when Lean version is below minimum required
 * @traceability REQ-LEAN-ERR-001
 */
export class LeanVersionError extends LeanError {
  constructor(
    public readonly required: string,
    public readonly actual: string
  ) {
    super(
      `Lean version ${actual} is below minimum required version ${required}. Please upgrade Lean 4.`,
      'LEAN_VERSION_MISMATCH'
    );
    this.name = 'LeanVersionError';
  }
}

/**
 * Error thrown when EARS-to-Lean conversion fails
 * @traceability REQ-LEAN-ERR-002
 */
export class EarsConversionError extends LeanError {
  constructor(
    public readonly requirementId: string,
    public readonly reason: string
  ) {
    super(
      `Failed to convert requirement ${requirementId} to Lean: ${reason}`,
      'EARS_CONVERSION_FAILED'
    );
    this.name = 'EarsConversionError';
  }
}

/**
 * Error thrown when EARS parsing fails
 */
export class EarsParseError extends LeanError {
  constructor(
    public readonly text: string,
    public readonly reason: string
  ) {
    super(`Failed to parse EARS requirement: ${reason}`, 'EARS_PARSE_FAILED');
    this.name = 'EarsParseError';
  }
}

/**
 * Error thrown when TypeScript specification fails
 */
export class TypeScriptSpecificationError extends LeanError {
  constructor(
    public readonly functionName: string,
    public readonly reason: string
  ) {
    super(
      `Failed to specify TypeScript function ${functionName}: ${reason}`,
      'TS_SPECIFICATION_FAILED'
    );
    this.name = 'TypeScriptSpecificationError';
  }
}

/**
 * Error thrown when proof generation times out
 * @traceability REQ-LEAN-PERF-002
 */
export class ProofTimeoutError extends LeanError {
  constructor(
    public readonly theoremName: string,
    public readonly timeout: number
  ) {
    super(
      `Proof search for theorem '${theoremName}' timed out after ${timeout}ms`,
      'PROOF_TIMEOUT'
    );
    this.name = 'ProofTimeoutError';
  }
}

/**
 * Error thrown when proof generation fails
 */
export class ProofGenerationError extends LeanError {
  constructor(
    public readonly theoremName: string,
    public readonly reason: string
  ) {
    super(
      `Failed to generate proof for theorem '${theoremName}': ${reason}`,
      'PROOF_GENERATION_FAILED'
    );
    this.name = 'ProofGenerationError';
  }
}

/**
 * Error thrown when ReProver connection fails
 * @traceability REQ-LEAN-REPROVER-001
 */
export class ReProverConnectionError extends LeanError {
  constructor(
    public readonly endpoint: string,
    public readonly reason: string
  ) {
    super(
      `Failed to connect to ReProver at ${endpoint}: ${reason}`,
      'REPROVER_CONNECTION_FAILED'
    );
    this.name = 'ReProverConnectionError';
  }
}

/**
 * Error thrown when Lean file generation fails
 */
export class LeanFileGenerationError extends LeanError {
  constructor(
    public readonly filePath: string,
    public readonly reason: string
  ) {
    super(
      `Failed to generate Lean file at ${filePath}: ${reason}`,
      'LEAN_FILE_GENERATION_FAILED'
    );
    this.name = 'LeanFileGenerationError';
  }
}

/**
 * Error thrown when Lean execution fails
 */
export class LeanExecutionError extends LeanError {
  constructor(
    public readonly command: string,
    public readonly exitCodeOrMessage: number | string,
    public readonly stderr: string
  ) {
    const message = typeof exitCodeOrMessage === 'number'
      ? `Lean command '${command}' failed with exit code ${exitCodeOrMessage}: ${stderr}`
      : `Lean command '${command}' failed: ${exitCodeOrMessage}. ${stderr}`;
    super(message, 'LEAN_EXECUTION_FAILED');
    this.name = 'LeanExecutionError';
  }
}

/**
 * Get installation instructions for the given OS
 * @traceability REQ-LEAN-ERR-001
 */
function getInstallInstructions(os: string): string {
  const elanUrl = 'https://github.com/leanprover/elan';

  switch (os.toLowerCase()) {
    case 'linux':
      return `To install Lean 4 on Linux:
1. Install elan (Lean version manager):
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
2. Restart your terminal or run: source ~/.profile
3. Install Lean 4: elan default leanprover/lean4:stable

For more information, visit: ${elanUrl}`;

    case 'darwin':
    case 'macos':
      return `To install Lean 4 on macOS:
1. Install elan (Lean version manager):
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   Or via Homebrew: brew install elan-init
2. Restart your terminal
3. Install Lean 4: elan default leanprover/lean4:stable

For more information, visit: ${elanUrl}`;

    case 'win32':
    case 'windows':
      return `To install Lean 4 on Windows:
1. Download the elan installer from: ${elanUrl}/releases
2. Run the installer and follow the prompts
3. Restart your terminal
4. Install Lean 4: elan default leanprover/lean4:stable

For more information, visit: ${elanUrl}`;

    default:
      return `To install Lean 4:
1. Visit ${elanUrl} for installation instructions
2. Install elan (Lean version manager)
3. Run: elan default leanprover/lean4:stable`;
  }
}

export { getInstallInstructions };

/**
 * Error thrown when Lean environment detection fails
 */
export class LeanEnvironmentError extends LeanError {
  constructor(message: string) {
    super(message, 'LEAN_ENVIRONMENT_ERROR');
    this.name = 'LeanEnvironmentError';
  }
}

/**
 * Error thrown when Lean conversion fails
 */
export class LeanConversionError extends LeanError {
  constructor(message: string) {
    super(message, 'LEAN_CONVERSION_ERROR');
    this.name = 'LeanConversionError';
  }
}

/**
 * Error thrown when Lean verification fails
 */
export class LeanVerificationError extends LeanError {
  public readonly errors: string[];

  constructor(message: string, errors: string[] = []) {
    super(message, 'LEAN_VERIFICATION_ERROR');
    this.name = 'LeanVerificationError';
    this.errors = errors;
  }
}

/**
 * Error thrown when Lean proof generation fails
 */
export class LeanProofError extends LeanError {
  constructor(message: string) {
    super(message, 'LEAN_PROOF_ERROR');
    this.name = 'LeanProofError';
  }
}

/**
 * Error thrown when Lean integration fails
 */
export class LeanIntegrationError extends LeanError {
  constructor(message: string) {
    super(message, 'LEAN_INTEGRATION_ERROR');
    this.name = 'LeanIntegrationError';
  }
}

/**
 * Error thrown when ReProver fails
 */
export class ReProverError extends LeanError {
  constructor(message: string) {
    super(message, 'REPROVER_ERROR');
    this.name = 'ReProverError';
  }
}
