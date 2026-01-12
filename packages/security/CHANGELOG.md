# Changelog

All notable changes to @nahisaho/musubix-security will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [3.0.11] - 2026-01-11

### Fixed
- **tree-sitter Peer Dependency Conflict**: Changed tree-sitter dependency from ^0.22.0 to ^0.21.1 for compatibility with tree-sitter-go@0.23.x
- **TypeScript Type System**: Resolved 551+ TypeScript compilation errors from type mismatches

### Changed
- **CodeDB Module**: Temporarily disabled (stubbed) pending type system refactoring
  - `CodeDB`, `CodeDBBuilder`, `buildCodeDB`, `buildCodeDBFromPath` now throw errors with guidance to use variant analysis
  - Full functionality will be restored in v3.1.0
- **MQL Module**: Temporarily disabled pending type system refactoring
  - Query language features will be restored in v3.1.0
- **Extractors**: Simplified to type exports only
  - Java and Go extractors temporarily disabled
- **Variant Analysis**: Refactored to file-based implementation without CodeDB dependency
  - Pattern-based vulnerability detection remains fully functional
  - SARIF report generation working

### Migration Guide
If you were using CodeDB or MQL features:
```typescript
// Before (v3.0.10)
import { createCodeDBBuilder, createMQLEngine } from '@nahisaho/musubix-security';
const builder = createCodeDBBuilder();
const { database } = await builder.build('./src');
const engine = createMQLEngine();
const result = await engine.execute('FROM functions...', database);

// After (v3.0.11) - Use variant analysis instead
import { createScanner } from '@nahisaho/musubix-security';
const scanner = createScanner();
const result = await scanner.scan('./src');
```

## [3.0.10] - 2026-01-11

### Added
- **CodeQL-Equivalent Features**: Multi-language code analysis framework
  - MQL (MUSUBIX Query Language) for code analysis
  - Variant Analysis with SARIF export
  - CodeDB in-memory database

### Known Issues
- tree-sitter peer dependency conflicts during npm install (fixed in v3.0.11)

## [1.8.0] - 2026-01-07

### Added

#### Phase 1: Core Security Infrastructure
- **Vulnerability Scanner**: Static analysis engine with 40+ vulnerability detection rules
- **Secret Detector**: High-precision credential and API key detection with entropy analysis
- **Taint Analysis**: Dataflow tracking for injection vulnerability detection
- **Security Service**: Unified API for all security scanning operations
- **Result Aggregator**: Finding deduplication and prioritization
- **Pipeline Manager**: Configurable multi-stage security pipeline orchestration

#### Phase 2: Advanced Detection Capabilities
- **Interprocedural Analyzer**: Cross-function dataflow analysis for complex vulnerability detection
- **Zero-Day Detector**: ML-based anomaly detection for unknown vulnerability patterns
- **Prompt Injection Detector**: AI-specific security analysis for LLM applications
- **Container/Image Scanner**: Dockerfile and container image security analysis
- **IaC Security Checker**: Terraform, CloudFormation, and Kubernetes manifest validation

#### Phase 3: Enterprise Security Features
- **Dependency Scanner**: SCA with CVE database integration and license analysis
- **Compliance Checker**: OWASP Top 10, PCI-DSS, SOC2, HIPAA framework validation
- **API Security Analyzer**: REST/GraphQL security analysis with OpenAPI support
- **Real-time Monitor**: Continuous security monitoring with change detection
- **Security Dashboard**: Executive reporting with trend analysis and risk scoring

#### Phase 4: Integration and Automation
- **CI/CD Integration**: GitHub Actions, GitLab CI, Azure Pipelines, Jenkins, CircleCI support
- **Report Aggregator**: Multi-scan result aggregation with trend tracking
- **Git Hooks Manager**: Pre-commit and pre-push security scanning automation
- **VS Code Integration**: IDE integration with diagnostics, code actions, and decorations
- **Policy Engine**: Customizable security policies with rule-based evaluation

#### Phase 5: Auto-Fix and Remediation (NEW!)
- **AutoFixer**: Automatic fix generation for detected vulnerabilities
  - Built-in fix templates for XSS, SQL injection, path traversal, and more
  - Strategy-based fix generation (encoding, parameterization, validation, replacement)
  - Configurable confidence thresholds and maximum fixes
- **FixValidator**: Comprehensive fix validation before application
  - Syntax validation with bracket balancing
  - Semantic validation for code structure preservation
  - Security properties validation to prevent new vulnerabilities
  - Custom validation rule registration
- **PatchGenerator**: Unified diff patch generation for fixes
  - Multiple output formats (unified, git, JSON, context)
  - Batch patch generation for multiple fixes
  - Patch parsing, validation, and application
  - Reverse patch generation for rollbacks
- **RemediationPlanner**: Strategic vulnerability remediation planning
  - Priority-based fix scheduling (severity-first, effort-first, risk-based, dependency-aware, balanced)
  - Phase-based remediation with dependency resolution
  - Effort estimation and risk reduction calculation
  - Progress tracking and reporting
- **SecureCodeTransformer**: Automatic secure code pattern transformation
  - 10+ built-in transformations (HTML escaping, crypto upgrades, error handling, etc.)
  - Category-based transformations (output-encoding, cryptography, error-handling, data-protection, session-management)
  - Risk-level classification (safe, caution, review-required)
  - Transformation preview and validation

#### Phase 6: Security Intelligence and Analytics (NEW!)
- **ThreatIntelligence**: External threat feed integration and IOC matching
  - Multi-feed support with automatic refresh and caching
  - Indicator of Compromise (IOC) matching against codebase
  - CVE enrichment with severity and remediation data
  - IOC search and filtering capabilities
- **AttackPatternMatcher**: MITRE ATT&CK framework integration
  - Comprehensive technique library (T1190, T1059, T1078, etc.)
  - Tactic-based pattern organization
  - Code pattern matching against known attack techniques
  - Custom attack pattern registration
- **RiskScorer**: Advanced vulnerability risk assessment
  - CVSS v3.1 calculation (base, temporal, environmental scores)
  - Business impact assessment with asset criticality
  - Exploitability and remediation difficulty factors
  - Composite risk scoring with confidence levels
- **SecurityAnalytics**: Security metrics collection and dashboards
  - Vulnerability metrics tracking (total, by severity, by type, by status)
  - Time-series data with trend analysis
  - Executive dashboard generation with KPIs
  - Event-based analytics (vulnerabilities, fixes, scans)
- **PredictiveAnalyzer**: Security trend forecasting and anomaly detection
  - Linear and exponential smoothing forecast models
  - Anomaly detection with configurable sensitivity
  - Risk projection over time periods
  - Alert generation for detected anomalies

### Statistics
- **Total Tests**: 725 (723 passing, 2 skipped)
- **Test Files**: 32
- **Core Components**: 35+
- **Security Rules**: 40+
- **Supported CI Platforms**: 5
- **Compliance Frameworks**: 4
- **Auto-Fix Templates**: 8+
- **Code Transformations**: 10+
- **Attack Patterns**: 20+ (MITRE ATT&CK)
- **Threat Feed Support**: Multiple external feeds

### Technical Details
- TypeScript 5.x with strict mode
- ESM module format
- Vitest for testing
- Zero external runtime dependencies for core scanning
