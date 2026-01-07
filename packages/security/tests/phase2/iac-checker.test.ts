/**
 * @fileoverview Phase 2 Analyzer Tests - IaC Checker
 * @module @nahisaho/musubix-security/tests/phase2
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { IaCChecker, createIaCChecker, type IaCCheckOptions } from '../../src/analyzers/iac/iac-checker.js';
import { writeFileSync, mkdirSync, rmSync } from 'node:fs';
import path from 'node:path';
import os from 'node:os';

describe('IaCChecker', () => {
  let checker: IaCChecker;
  let tempDir: string;

  beforeEach(() => {
    checker = createIaCChecker();
    tempDir = path.join(os.tmpdir(), `iac-test-${Date.now()}`);
    mkdirSync(tempDir, { recursive: true });
  });

  afterEach(() => {
    try {
      rmSync(tempDir, { recursive: true, force: true });
    } catch {
      // Ignore cleanup errors
    }
  });

  describe('Terraform Analysis', () => {
    it('should detect S3 bucket with public ACL', async () => {
      const tfContent = `
resource "aws_s3_bucket" "public_bucket" {
  bucket = "my-public-bucket"
  acl    = "public-read"
}
`;
      const filePath = path.join(tempDir, 'main.tf');
      writeFileSync(filePath, tfContent);

      const result = await checker.analyzeFile(filePath, 'terraform');
      
      expect(result.issues.length).toBeGreaterThan(0);
      expect(result.issues.some(i => i.ruleId === 'TF-001')).toBe(true);
    });

    it('should detect security group open to world', async () => {
      const tfContent = `
resource "aws_security_group" "allow_all" {
  name = "allow_all"
  
  ingress {
    from_port   = 0
    to_port     = 65535
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }
}
`;
      const filePath = path.join(tempDir, 'sg.tf');
      writeFileSync(filePath, tfContent);

      const result = await checker.analyzeFile(filePath, 'terraform');
      
      expect(result.issues.some(i => i.ruleId === 'TF-002')).toBe(true);
    });

    it('should detect RDS public accessibility', async () => {
      const tfContent = `
resource "aws_db_instance" "public_db" {
  identifier = "public-database"
  publicly_accessible = true
}
`;
      const filePath = path.join(tempDir, 'rds.tf');
      writeFileSync(filePath, tfContent);

      const result = await checker.analyzeFile(filePath, 'terraform');
      
      expect(result.issues.some(i => i.ruleId === 'TF-003')).toBe(true);
    });

    it('should detect hardcoded credentials', async () => {
      const tfContent = `
resource "aws_db_instance" "db" {
  password = "supersecretpassword123"
}
`;
      const filePath = path.join(tempDir, 'creds.tf');
      writeFileSync(filePath, tfContent);

      const result = await checker.analyzeFile(filePath, 'terraform');
      
      expect(result.issues.some(i => i.ruleId === 'TF-005')).toBe(true);
    });

    it('should not flag variable references as hardcoded', async () => {
      const tfContent = `
resource "aws_db_instance" "db" {
  password = var.db_password
}
`;
      const filePath = path.join(tempDir, 'safe.tf');
      writeFileSync(filePath, tfContent);

      const result = await checker.analyzeFile(filePath, 'terraform');
      
      expect(result.issues.filter(i => i.ruleId === 'TF-005').length).toBe(0);
    });
  });

  describe('Kubernetes Analysis', () => {
    it('should detect container running as root', async () => {
      const k8sContent = `
apiVersion: v1
kind: Pod
metadata:
  name: root-pod
spec:
  containers:
  - name: web
    image: nginx
    securityContext:
      runAsUser: 0
`;
      const filePath = path.join(tempDir, 'pod.yaml');
      writeFileSync(filePath, k8sContent);

      const result = await checker.analyzeFile(filePath, 'kubernetes');
      
      expect(result.issues.some(i => i.ruleId === 'K8S-001')).toBe(true);
    });

    it('should detect privileged container', async () => {
      const k8sContent = `
apiVersion: v1
kind: Pod
metadata:
  name: privileged-pod
spec:
  containers:
  - name: web
    image: nginx
    securityContext:
      privileged: true
`;
      const filePath = path.join(tempDir, 'privileged.yaml');
      writeFileSync(filePath, k8sContent);

      const result = await checker.analyzeFile(filePath, 'kubernetes');
      
      expect(result.issues.some(i => i.ruleId === 'K8S-002')).toBe(true);
    });

    it('should detect host network usage', async () => {
      const k8sContent = `
apiVersion: v1
kind: Pod
metadata:
  name: hostnet-pod
spec:
  hostNetwork: true
  containers:
  - name: web
    image: nginx
`;
      const filePath = path.join(tempDir, 'hostnet.yaml');
      writeFileSync(filePath, k8sContent);

      const result = await checker.analyzeFile(filePath, 'kubernetes');
      
      expect(result.issues.some(i => i.ruleId === 'K8S-003')).toBe(true);
    });
  });

  describe('CloudFormation Analysis', () => {
    it('should detect unrestricted security group ingress', async () => {
      const cfnContent = `
AWSTemplateFormatVersion: '2010-09-09'
Resources:
  SecurityGroup:
    Type: AWS::EC2::SecurityGroup
    Properties:
      GroupDescription: Open to world
      SecurityGroupIngress:
        - IpProtocol: tcp
          FromPort: 22
          ToPort: 22
          CidrIp: 0.0.0.0/0
`;
      const filePath = path.join(tempDir, 'cfn-template.yaml');
      writeFileSync(filePath, cfnContent);

      const result = await checker.analyzeFile(filePath, 'cloudformation');
      
      expect(result.issues.some(i => i.ruleId === 'CFN-002')).toBe(true);
    });
  });

  describe('Options', () => {
    it('should filter by minimum severity', async () => {
      const tfContent = `
resource "aws_s3_bucket" "bucket" {
  bucket = "my-bucket"
  acl    = "public-read"
}
`;
      const filePath = path.join(tempDir, 'severity.tf');
      writeFileSync(filePath, tfContent);

      const highOnlyChecker = createIaCChecker({ minSeverity: 'high' });
      const result = await highOnlyChecker.analyzeFile(filePath, 'terraform');
      
      // All reported issues should be high severity or above
      for (const issue of result.issues) {
        expect(['critical', 'high']).toContain(issue.severity);
      }
    });

    it('should skip specified rules', async () => {
      const tfContent = `
resource "aws_s3_bucket" "bucket" {
  acl = "public-read"
}
resource "aws_security_group" "sg" {
  cidr_blocks = ["0.0.0.0/0"]
}
`;
      const filePath = path.join(tempDir, 'skip.tf');
      writeFileSync(filePath, tfContent);

      const skipChecker = createIaCChecker({ skipRules: ['TF-001'] });
      const result = await skipChecker.analyzeFile(filePath, 'terraform');
      
      expect(result.issues.some(i => i.ruleId === 'TF-001')).toBe(false);
    });
  });

  describe('toVulnerabilities', () => {
    it('should convert IaC issues to standard vulnerability format', async () => {
      const tfContent = `
resource "aws_security_group" "sg" {
  cidr_blocks = ["0.0.0.0/0"]
}
`;
      const filePath = path.join(tempDir, 'vuln.tf');
      writeFileSync(filePath, tfContent);

      const result = await checker.analyzeFile(filePath, 'terraform');
      const vulnerabilities = checker.toVulnerabilities([result]);
      
      expect(vulnerabilities.length).toBeGreaterThan(0);
      expect(vulnerabilities[0]).toHaveProperty('id');
      expect(vulnerabilities[0]).toHaveProperty('type', 'configuration');
      expect(vulnerabilities[0]).toHaveProperty('severity');
      expect(vulnerabilities[0]).toHaveProperty('location');
    });
  });

  describe('Resource Extraction', () => {
    it('should extract Terraform resources', async () => {
      const tfContent = `
resource "aws_s3_bucket" "main" {
  bucket = "my-bucket"
}

resource "aws_lambda_function" "handler" {
  function_name = "my-function"
}
`;
      const filePath = path.join(tempDir, 'resources.tf');
      writeFileSync(filePath, tfContent);

      const result = await checker.analyzeFile(filePath, 'terraform');
      
      expect(result.resources.length).toBe(2);
      expect(result.resources.some(r => r.type === 'aws_s3_bucket')).toBe(true);
      expect(result.resources.some(r => r.type === 'aws_lambda_function')).toBe(true);
    });

    it('should extract Kubernetes resources', async () => {
      const k8sContent = `
apiVersion: v1
kind: Deployment
metadata:
  name: web-app
---
apiVersion: v1
kind: Service
metadata:
  name: web-service
`;
      const filePath = path.join(tempDir, 'k8s.yaml');
      writeFileSync(filePath, k8sContent);

      const result = await checker.analyzeFile(filePath, 'kubernetes');
      
      expect(result.resources.length).toBeGreaterThanOrEqual(1);
    });
  });
});
