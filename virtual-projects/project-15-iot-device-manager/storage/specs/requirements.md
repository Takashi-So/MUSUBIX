# IoT Device Management System - EARS Requirements

## Document Information

- **Project**: IoT Device Management System
- **Version**: 1.0.0
- **Date**: 2026-01-06
- **Status**: Draft

---

## Device Registration (デバイス登録)

### REQ-DEV-001: Device Registration
**Priority**: P0  
**Pattern**: Ubiquitous

THE system SHALL allow users to register IoT devices with the following attributes: device ID, name, type (sensor/actuator/gateway), location, and communication protocol.

**Acceptance Criteria**:
- Device ID must be unique
- Name is required (1-100 characters)
- Type must be one of: sensor, actuator, gateway
- Location is optional but recommended

---

### REQ-DEV-002: Device Status Management
**Priority**: P0  
**Pattern**: State-driven

WHILE a device is registered, THE system SHALL track its status as one of: online, offline, maintenance, or error.

**Acceptance Criteria**:
- Initial status is 'offline'
- Status changes are logged with timestamp
- Status history is retained for 30 days

---

### REQ-DEV-003: Device Grouping
**Priority**: P1  
**Pattern**: Optional

IF a user creates a device group, THEN THE system SHALL allow adding multiple devices to that group for batch operations.

**Acceptance Criteria**:
- Group name must be unique
- A device can belong to multiple groups
- Batch operations: status update, delete, export

---

## Data Collection (データ収集)

### REQ-DATA-001: Telemetry Reception
**Priority**: P0  
**Pattern**: Event-driven

WHEN a sensor sends telemetry data, THE system SHALL receive and validate the data within 100ms.

**Acceptance Criteria**:
- Data format: { deviceId, timestamp, value, unit }
- Validation: deviceId exists, timestamp is valid ISO8601
- Response time < 100ms for 95th percentile

---

### REQ-DATA-002: Time-Series Storage
**Priority**: P0  
**Pattern**: Ubiquitous

THE system SHALL store telemetry data in time-series format with a retention period of 30 days.

**Acceptance Criteria**:
- Data is indexed by deviceId and timestamp
- Automatic purging of data older than 30 days
- Support for aggregation queries (avg, min, max, sum)

---

### REQ-DATA-003: Data Query
**Priority**: P1  
**Pattern**: Event-driven

WHEN a user requests historical data, THE system SHALL return telemetry records filtered by device, time range, and aggregation level.

**Acceptance Criteria**:
- Supported aggregations: raw, hourly, daily
- Maximum query range: 30 days
- Pagination for large result sets

---

## Alert Management (アラート管理)

### REQ-ALERT-001: Threshold Alert Generation
**Priority**: P0  
**Pattern**: Event-driven

WHEN telemetry data exceeds a configured threshold, THE system SHALL generate an alert with severity level (info/warning/critical).

**Acceptance Criteria**:
- Threshold rules: >, <, >=, <=, ==, !=
- Severity mapping is user-configurable
- Duplicate alerts are suppressed within cooldown period

---

### REQ-ALERT-002: Alert Notification
**Priority**: P1  
**Pattern**: Event-driven

WHEN an alert is generated, THE system SHALL send notifications via configured channels (email, Slack, webhook).

**Acceptance Criteria**:
- At least one notification channel must be configured
- Notification includes: device name, value, threshold, timestamp
- Retry logic for failed deliveries (3 attempts)

---

### REQ-ALERT-003: Alert Acknowledgment
**Priority**: P2  
**Pattern**: Event-driven

WHEN a user acknowledges an alert, THE system SHALL update the alert status to 'acknowledged' and stop further notifications.

**Acceptance Criteria**:
- Acknowledgment is logged with user ID and timestamp
- Alert remains in history for audit purposes

---

## Device Lifecycle (ライフサイクル)

### REQ-LIFE-001: Firmware Version Tracking
**Priority**: P1  
**Pattern**: Ubiquitous

THE system SHALL track the firmware version of each registered device.

**Acceptance Criteria**:
- Version format: semantic versioning (x.y.z)
- Version history is maintained
- Alerts for outdated firmware

---

### REQ-LIFE-002: Device Health Statistics
**Priority**: P1  
**Pattern**: Event-driven

WHEN a user requests device statistics, THE system SHALL provide uptime percentage, error count, and last communication time.

**Acceptance Criteria**:
- Uptime calculated over configurable period (7/30/90 days)
- Error count includes communication failures and threshold violations

---

## Security (セキュリティ)

### REQ-SEC-001: Device Authentication
**Priority**: P0  
**Pattern**: Ubiquitous

THE system SHALL NOT accept telemetry from unauthenticated devices.

**Acceptance Criteria**:
- Authentication via API key or certificate
- Failed authentication attempts are logged
- Rate limiting: 10 failed attempts → 1 hour lockout

---

### REQ-SEC-002: Data Encryption
**Priority**: P0  
**Pattern**: Ubiquitous

THE system SHALL encrypt all telemetry data in transit using TLS 1.3 or higher.

**Acceptance Criteria**:
- TLS 1.3 minimum
- Certificate validation is enforced

---

## Performance (パフォーマンス)

### REQ-PERF-001: Concurrent Device Support
**Priority**: P0  
**Pattern**: Ubiquitous

THE system SHALL support up to 1000 concurrent device connections without degradation.

**Acceptance Criteria**:
- 95th percentile latency < 100ms
- No message loss under normal load
- Graceful degradation under overload

---

## Traceability Matrix

| Requirement | Design | Implementation | Test |
|-------------|--------|----------------|------|
| REQ-DEV-001 | DES-DEV-001 | device.ts | device.test.ts |
| REQ-DEV-002 | DES-DEV-002 | device-status.ts | device-status.test.ts |
| REQ-DEV-003 | DES-DEV-003 | device-group.ts | device-group.test.ts |
| REQ-DATA-001 | DES-DATA-001 | telemetry-receiver.ts | telemetry.test.ts |
| REQ-DATA-002 | DES-DATA-002 | time-series-store.ts | storage.test.ts |
| REQ-DATA-003 | DES-DATA-003 | data-query.ts | query.test.ts |
| REQ-ALERT-001 | DES-ALERT-001 | alert-engine.ts | alert.test.ts |
| REQ-ALERT-002 | DES-ALERT-002 | notification-service.ts | notification.test.ts |
| REQ-ALERT-003 | DES-ALERT-003 | alert-ack.ts | alert-ack.test.ts |
| REQ-LIFE-001 | DES-LIFE-001 | firmware-tracker.ts | firmware.test.ts |
| REQ-LIFE-002 | DES-LIFE-002 | device-stats.ts | stats.test.ts |
| REQ-SEC-001 | DES-SEC-001 | device-auth.ts | auth.test.ts |
| REQ-SEC-002 | DES-SEC-002 | tls-handler.ts | tls.test.ts |
| REQ-PERF-001 | DES-PERF-001 | connection-pool.ts | load.test.ts |
