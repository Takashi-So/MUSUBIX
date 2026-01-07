/**
 * @fileoverview Infrastructure as Code (IaC) Checker
 * @module @nahisaho/musubix-security/analyzers/iac/iac-checker
 * @trace DES-SEC2-IAC-001, REQ-SEC2-IAC-001
 */

import { existsSync, readFileSync, readdirSync, statSync } from 'node:fs';
import path from 'node:path';
import type { Vulnerability, Severity, SourceLocation } from '../../types/vulnerability.js';

/**
 * IaC file type
 */
export type IaCType = 'terraform' | 'cloudformation' | 'kubernetes' | 'docker-compose' | 'helm' | 'ansible';

/**
 * IaC issue
 */
export interface IaCIssue {
  id: string;
  ruleId: string;
  severity: Severity;
  title: string;
  description: string;
  location: SourceLocation;
  remediation: string;
  references?: string[];
  cwes?: string[];
}

/**
 * IaC analysis result
 */
export interface IaCAnalysisResult {
  filePath: string;
  fileType: IaCType;
  issues: IaCIssue[];
  resources: IaCResource[];
  analysisTime: number;
}

/**
 * IaC resource
 */
export interface IaCResource {
  type: string;
  name: string;
  location: SourceLocation;
  properties: Record<string, unknown>;
}

/**
 * IaC check options
 */
export interface IaCCheckOptions {
  /** File types to analyze */
  fileTypes?: IaCType[];
  /** Minimum severity to report */
  minSeverity?: Severity;
  /** Custom rules */
  customRules?: IaCRule[];
  /** Skip specific rules */
  skipRules?: string[];
}

/**
 * IaC rule definition
 */
export interface IaCRule {
  id: string;
  name: string;
  description: string;
  severity: Severity;
  fileTypes: IaCType[];
  check: (content: string, filePath: string) => IaCRuleMatch[];
  remediation: string;
  cwes?: string[];
  references?: string[];
}

/**
 * IaC rule match
 */
export interface IaCRuleMatch {
  line: number;
  column?: number;
  endLine?: number;
  endColumn?: number;
  matchedText?: string;
  context?: string;
}

/**
 * Built-in Terraform rules
 */
const TERRAFORM_RULES: IaCRule[] = [
  {
    id: 'TF-001',
    name: 'AWS S3 Bucket Public Access',
    description: 'S3 bucket should not allow public access',
    severity: 'critical',
    fileTypes: ['terraform'],
    cwes: ['CWE-284'],
    references: ['https://docs.aws.amazon.com/AmazonS3/latest/userguide/access-control-block-public-access.html'],
    remediation: 'Add block_public_acls = true, block_public_policy = true, ignore_public_acls = true, restrict_public_buckets = true',
    check: (content, _filePath) => {
      const matches: IaCRuleMatch[] = [];
      const lines = content.split('\n');
      
      // Find S3 bucket resources without public access block
      let inS3Bucket = false;
      let bucketStartLine = 0;
      let hasPublicAccessBlock = false;
      
      for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        
        if (line.includes('resource "aws_s3_bucket"')) {
          inS3Bucket = true;
          bucketStartLine = i + 1;
          hasPublicAccessBlock = false;
        }
        
        if (inS3Bucket && line.includes('aws_s3_bucket_public_access_block')) {
          hasPublicAccessBlock = true;
        }
        
        if (inS3Bucket && line.trim() === '}' && !line.includes('{')) {
          if (!hasPublicAccessBlock) {
            matches.push({
              line: bucketStartLine,
              matchedText: 'aws_s3_bucket without public access block',
            });
          }
          inS3Bucket = false;
        }
      }
      
      // Also check for explicit public ACLs
      for (let i = 0; i < lines.length; i++) {
        if (lines[i].match(/acl\s*=\s*["']public-(read|read-write)["']/)) {
          matches.push({
            line: i + 1,
            matchedText: lines[i].trim(),
          });
        }
      }
      
      return matches;
    },
  },
  {
    id: 'TF-002',
    name: 'AWS Security Group Open to World',
    description: 'Security group should not allow unrestricted inbound access',
    severity: 'high',
    fileTypes: ['terraform'],
    cwes: ['CWE-284'],
    references: ['https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/security-group-rules-reference.html'],
    remediation: 'Restrict cidr_blocks to specific IP ranges instead of 0.0.0.0/0',
    check: (content, _filePath) => {
      const matches: IaCRuleMatch[] = [];
      const lines = content.split('\n');
      
      for (let i = 0; i < lines.length; i++) {
        if (lines[i].match(/cidr_blocks\s*=\s*\[\s*["']0\.0\.0\.0\/0["']\s*\]/)) {
          matches.push({
            line: i + 1,
            matchedText: lines[i].trim(),
          });
        }
      }
      
      return matches;
    },
  },
  {
    id: 'TF-003',
    name: 'AWS RDS Public Accessibility',
    description: 'RDS instance should not be publicly accessible',
    severity: 'high',
    fileTypes: ['terraform'],
    cwes: ['CWE-284'],
    references: ['https://docs.aws.amazon.com/AmazonRDS/latest/UserGuide/USER_VPC.WorkingWithRDSInstanceinaVPC.html'],
    remediation: 'Set publicly_accessible = false',
    check: (content, _filePath) => {
      const matches: IaCRuleMatch[] = [];
      const lines = content.split('\n');
      
      for (let i = 0; i < lines.length; i++) {
        if (lines[i].match(/publicly_accessible\s*=\s*true/)) {
          matches.push({
            line: i + 1,
            matchedText: lines[i].trim(),
          });
        }
      }
      
      return matches;
    },
  },
  {
    id: 'TF-004',
    name: 'AWS EC2 Unencrypted EBS',
    description: 'EBS volumes should be encrypted',
    severity: 'medium',
    fileTypes: ['terraform'],
    cwes: ['CWE-311'],
    references: ['https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/EBSEncryption.html'],
    remediation: 'Set encrypted = true in ebs_block_device',
    check: (content, _filePath) => {
      const matches: IaCRuleMatch[] = [];
      const lines = content.split('\n');
      
      let inEbsBlock = false;
      let ebsStartLine = 0;
      let hasEncryption = false;
      
      for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        
        if (line.includes('ebs_block_device') || line.includes('aws_ebs_volume')) {
          inEbsBlock = true;
          ebsStartLine = i + 1;
          hasEncryption = false;
        }
        
        if (inEbsBlock && line.includes('encrypted')) {
          hasEncryption = true;
        }
        
        if (inEbsBlock && line.trim() === '}') {
          if (!hasEncryption) {
            matches.push({
              line: ebsStartLine,
              matchedText: 'EBS volume without encryption',
            });
          }
          inEbsBlock = false;
        }
      }
      
      return matches;
    },
  },
  {
    id: 'TF-005',
    name: 'Hardcoded Credentials',
    description: 'Credentials should not be hardcoded',
    severity: 'critical',
    fileTypes: ['terraform'],
    cwes: ['CWE-798'],
    references: ['https://owasp.org/www-community/vulnerabilities/Use_of_hard-coded_password'],
    remediation: 'Use variables, environment variables, or secret management services',
    check: (content, _filePath) => {
      const matches: IaCRuleMatch[] = [];
      const lines = content.split('\n');
      
      const patterns = [
        /password\s*=\s*["'][^"']+["']/i,
        /secret\s*=\s*["'][^"']+["']/i,
        /api_key\s*=\s*["'][^"']+["']/i,
        /access_key\s*=\s*["']AKIA[0-9A-Z]+["']/i,
      ];
      
      for (let i = 0; i < lines.length; i++) {
        for (const pattern of patterns) {
          if (lines[i].match(pattern) && !lines[i].includes('var.')) {
            matches.push({
              line: i + 1,
              matchedText: lines[i].trim().replace(/["'][^"']{10,}["']/, '"***"'),
            });
          }
        }
      }
      
      return matches;
    },
  },
  {
    id: 'TF-006',
    name: 'AWS CloudWatch Logs Not Encrypted',
    description: 'CloudWatch log groups should be encrypted',
    severity: 'medium',
    fileTypes: ['terraform'],
    cwes: ['CWE-311'],
    references: ['https://docs.aws.amazon.com/AmazonCloudWatch/latest/logs/encrypt-log-data-kms.html'],
    remediation: 'Add kms_key_id to aws_cloudwatch_log_group',
    check: (content, _filePath) => {
      const matches: IaCRuleMatch[] = [];
      const lines = content.split('\n');
      
      let inLogGroup = false;
      let logGroupStartLine = 0;
      let hasKmsKey = false;
      
      for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        
        if (line.includes('resource "aws_cloudwatch_log_group"')) {
          inLogGroup = true;
          logGroupStartLine = i + 1;
          hasKmsKey = false;
        }
        
        if (inLogGroup && line.includes('kms_key_id')) {
          hasKmsKey = true;
        }
        
        if (inLogGroup && line.trim() === '}' && !line.includes('{')) {
          if (!hasKmsKey) {
            matches.push({
              line: logGroupStartLine,
              matchedText: 'CloudWatch log group without KMS encryption',
            });
          }
          inLogGroup = false;
        }
      }
      
      return matches;
    },
  },
];

/**
 * Built-in Kubernetes rules
 */
const KUBERNETES_RULES: IaCRule[] = [
  {
    id: 'K8S-001',
    name: 'Container Running as Root',
    description: 'Containers should not run as root',
    severity: 'high',
    fileTypes: ['kubernetes'],
    cwes: ['CWE-250'],
    references: ['https://kubernetes.io/docs/concepts/security/pod-security-standards/'],
    remediation: 'Set securityContext.runAsNonRoot = true',
    check: (content, _filePath) => {
      const matches: IaCRuleMatch[] = [];
      const lines = content.split('\n');
      
      // Check for missing runAsNonRoot or runAsUser: 0
      let inContainer = false;
      let hasSecurityContext = false;
      let containerStartLine = 0;
      
      for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        
        if (line.match(/^\s*-?\s*name:\s*\S+/) && lines[i - 1]?.includes('containers:')) {
          inContainer = true;
          containerStartLine = i + 1;
          hasSecurityContext = false;
        }
        
        if (inContainer && line.includes('securityContext:')) {
          hasSecurityContext = true;
        }
        
        if (line.match(/runAsUser:\s*0/)) {
          matches.push({
            line: i + 1,
            matchedText: line.trim(),
          });
        }
        
        if (inContainer && line.match(/^\s*-?\s*name:/) && i > containerStartLine) {
          if (!hasSecurityContext) {
            matches.push({
              line: containerStartLine,
              matchedText: 'Container without securityContext',
            });
          }
          containerStartLine = i + 1;
          hasSecurityContext = false;
        }
      }
      
      return matches;
    },
  },
  {
    id: 'K8S-002',
    name: 'Privileged Container',
    description: 'Containers should not run in privileged mode',
    severity: 'critical',
    fileTypes: ['kubernetes'],
    cwes: ['CWE-250'],
    references: ['https://kubernetes.io/docs/concepts/security/pod-security-standards/'],
    remediation: 'Set securityContext.privileged = false or remove it',
    check: (content, _filePath) => {
      const matches: IaCRuleMatch[] = [];
      const lines = content.split('\n');
      
      for (let i = 0; i < lines.length; i++) {
        if (lines[i].match(/privileged:\s*true/)) {
          matches.push({
            line: i + 1,
            matchedText: lines[i].trim(),
          });
        }
      }
      
      return matches;
    },
  },
  {
    id: 'K8S-003',
    name: 'Host Network Enabled',
    description: 'Pods should not use host network',
    severity: 'high',
    fileTypes: ['kubernetes'],
    cwes: ['CWE-668'],
    references: ['https://kubernetes.io/docs/concepts/security/pod-security-standards/'],
    remediation: 'Set hostNetwork = false or remove it',
    check: (content, _filePath) => {
      const matches: IaCRuleMatch[] = [];
      const lines = content.split('\n');
      
      for (let i = 0; i < lines.length; i++) {
        if (lines[i].match(/hostNetwork:\s*true/)) {
          matches.push({
            line: i + 1,
            matchedText: lines[i].trim(),
          });
        }
      }
      
      return matches;
    },
  },
  {
    id: 'K8S-004',
    name: 'No Resource Limits',
    description: 'Containers should have resource limits',
    severity: 'medium',
    fileTypes: ['kubernetes'],
    cwes: ['CWE-400'],
    references: ['https://kubernetes.io/docs/concepts/configuration/manage-resources-containers/'],
    remediation: 'Add resources.limits for CPU and memory',
    check: (content, _filePath) => {
      const matches: IaCRuleMatch[] = [];
      const lines = content.split('\n');
      
      let inContainer = false;
      let hasLimits = false;
      let containerStartLine = 0;
      
      for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        
        if (line.match(/^\s*-?\s*name:/) && lines[i - 1]?.includes('containers:')) {
          if (inContainer && !hasLimits) {
            matches.push({
              line: containerStartLine,
              matchedText: 'Container without resource limits',
            });
          }
          inContainer = true;
          containerStartLine = i + 1;
          hasLimits = false;
        }
        
        if (inContainer && line.includes('limits:')) {
          hasLimits = true;
        }
      }
      
      // Check last container
      if (inContainer && !hasLimits) {
        matches.push({
          line: containerStartLine,
          matchedText: 'Container without resource limits',
        });
      }
      
      return matches;
    },
  },
  {
    id: 'K8S-005',
    name: 'Secrets in Environment Variables',
    description: 'Secrets should not be exposed as environment variables',
    severity: 'medium',
    fileTypes: ['kubernetes'],
    cwes: ['CWE-200'],
    references: ['https://kubernetes.io/docs/concepts/configuration/secret/#using-secrets'],
    remediation: 'Use secretKeyRef with volume mounts instead',
    check: (content, _filePath) => {
      const matches: IaCRuleMatch[] = [];
      const lines = content.split('\n');
      
      for (let i = 0; i < lines.length; i++) {
        // Check for inline secret values in env vars
        if (lines[i].match(/^\s*-?\s*name:\s*(password|secret|key|token)/i) && 
            lines[i + 1]?.match(/^\s*value:/)) {
          matches.push({
            line: i + 1,
            matchedText: `${lines[i].trim()} with inline value`,
          });
        }
      }
      
      return matches;
    },
  },
];

/**
 * Built-in CloudFormation rules
 */
const CLOUDFORMATION_RULES: IaCRule[] = [
  {
    id: 'CFN-001',
    name: 'S3 Bucket Without Encryption',
    description: 'S3 buckets should have encryption enabled',
    severity: 'high',
    fileTypes: ['cloudformation'],
    cwes: ['CWE-311'],
    references: ['https://docs.aws.amazon.com/AWSCloudFormation/latest/UserGuide/aws-properties-s3-bucket.html'],
    remediation: 'Add BucketEncryption property with ServerSideEncryptionConfiguration',
    check: (content, _filePath) => {
      const matches: IaCRuleMatch[] = [];
      const lines = content.split('\n');
      
      let inS3Bucket = false;
      let bucketStartLine = 0;
      let hasEncryption = false;
      
      for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        
        if (line.includes('AWS::S3::Bucket')) {
          inS3Bucket = true;
          bucketStartLine = i + 1;
          hasEncryption = false;
        }
        
        if (inS3Bucket && line.includes('BucketEncryption')) {
          hasEncryption = true;
        }
        
        // Simple heuristic for resource end
        if (inS3Bucket && line.match(/^\s{2}\w+:/) && i > bucketStartLine + 2) {
          if (!hasEncryption) {
            matches.push({
              line: bucketStartLine,
              matchedText: 'S3 bucket without encryption',
            });
          }
          inS3Bucket = false;
        }
      }
      
      return matches;
    },
  },
  {
    id: 'CFN-002',
    name: 'Security Group Unrestricted Ingress',
    description: 'Security groups should not allow unrestricted ingress',
    severity: 'high',
    fileTypes: ['cloudformation'],
    cwes: ['CWE-284'],
    references: ['https://docs.aws.amazon.com/AWSCloudFormation/latest/UserGuide/aws-properties-ec2-security-group.html'],
    remediation: 'Restrict CidrIp to specific IP ranges',
    check: (content, _filePath) => {
      const matches: IaCRuleMatch[] = [];
      const lines = content.split('\n');
      
      for (let i = 0; i < lines.length; i++) {
        if (lines[i].match(/CidrIp:\s*['"]?0\.0\.0\.0\/0['"]?/)) {
          matches.push({
            line: i + 1,
            matchedText: lines[i].trim(),
          });
        }
      }
      
      return matches;
    },
  },
];

/**
 * All built-in rules
 */
const BUILTIN_RULES: IaCRule[] = [
  ...TERRAFORM_RULES,
  ...KUBERNETES_RULES,
  ...CLOUDFORMATION_RULES,
];

/**
 * IaC Checker implementation
 * @trace DES-SEC2-IAC-001
 */
export class IaCChecker {
  private options: IaCCheckOptions;
  private rules: IaCRule[];

  constructor(options: IaCCheckOptions = {}) {
    this.options = {
      fileTypes: options.fileTypes ?? ['terraform', 'cloudformation', 'kubernetes'],
      minSeverity: options.minSeverity ?? 'low',
      skipRules: options.skipRules ?? [],
    };
    
    // Build rule set
    this.rules = [
      ...BUILTIN_RULES.filter(r => !this.options.skipRules?.includes(r.id)),
      ...(options.customRules ?? []),
    ];
  }

  /**
   * Analyze IaC files in a directory
   * @trace REQ-SEC2-IAC-001
   */
  async analyze(dirPath: string, options?: IaCCheckOptions): Promise<IaCAnalysisResult[]> {
    const mergedOptions = { ...this.options, ...options };
    const results: IaCAnalysisResult[] = [];
    
    // Find IaC files
    const files = this.findIaCFiles(dirPath, mergedOptions.fileTypes ?? []);
    
    for (const file of files) {
      const result = await this.analyzeFile(file.path, file.type, mergedOptions);
      results.push(result);
    }
    
    return results;
  }

  /**
   * Analyze a single IaC file
   */
  async analyzeFile(
    filePath: string,
    fileType: IaCType,
    options?: IaCCheckOptions
  ): Promise<IaCAnalysisResult> {
    const startTime = Date.now();
    const mergedOptions = { ...this.options, ...options };
    
    if (!existsSync(filePath)) {
      throw new Error(`File not found: ${filePath}`);
    }
    
    const content = readFileSync(filePath, 'utf-8');
    const issues: IaCIssue[] = [];
    const resources: IaCResource[] = [];
    
    // Get applicable rules
    const applicableRules = this.rules.filter(
      r => r.fileTypes.includes(fileType) && !mergedOptions.skipRules?.includes(r.id)
    );
    
    // Run rules
    const minSeverityLevel = this.getSeverityLevel(mergedOptions.minSeverity ?? 'low');
    
    for (const rule of applicableRules) {
      if (this.getSeverityLevel(rule.severity) < minSeverityLevel) {
        continue;
      }
      
      const matches = rule.check(content, filePath);
      
      for (const match of matches) {
        issues.push({
          id: `${rule.id}-${match.line}`,
          ruleId: rule.id,
          severity: rule.severity,
          title: rule.name,
          description: rule.description,
          location: {
            file: filePath,
            startLine: match.line,
            endLine: match.endLine ?? match.line,
            startColumn: match.column ?? 0,
            endColumn: match.endColumn ?? 0,
          },
          remediation: rule.remediation,
          references: rule.references,
          cwes: rule.cwes,
        });
      }
    }
    
    // Extract resources (simplified)
    resources.push(...this.extractResources(content, fileType, filePath));
    
    return {
      filePath,
      fileType,
      issues,
      resources,
      analysisTime: Date.now() - startTime,
    };
  }

  /**
   * Convert IaC issues to standard vulnerability format
   */
  toVulnerabilities(results: IaCAnalysisResult[]): Vulnerability[] {
    const vulnerabilities: Vulnerability[] = [];
    
    for (const result of results) {
      for (const issue of result.issues) {
        vulnerabilities.push({
          id: issue.id,
          type: 'configuration' as const,
          severity: issue.severity,
          cwes: issue.cwes ?? [],
          owasp: ['A05:2021'], // Security Misconfiguration
          location: issue.location,
          description: `${issue.title}: ${issue.description}`,
          recommendation: issue.remediation,
          confidence: 0.9,
          ruleId: issue.ruleId,
          codeSnippet: '',
          detectedAt: new Date(),
        });
      }
    }
    
    return vulnerabilities;
  }

  /**
   * Find IaC files in a directory
   */
  private findIaCFiles(
    dirPath: string,
    fileTypes: IaCType[]
  ): Array<{ path: string; type: IaCType }> {
    const files: Array<{ path: string; type: IaCType }> = [];
    
    if (!existsSync(dirPath)) {
      return files;
    }
    
    const scan = (dir: string) => {
      const entries = readdirSync(dir);
      
      for (const entry of entries) {
        const fullPath = path.join(dir, entry);
        const stat = statSync(fullPath);
        
        if (stat.isDirectory()) {
          // Skip common non-IaC directories
          if (!['node_modules', '.git', '.terraform', 'vendor'].includes(entry)) {
            scan(fullPath);
          }
        } else {
          const type = this.detectFileType(entry, fullPath);
          if (type && fileTypes.includes(type)) {
            files.push({ path: fullPath, type });
          }
        }
      }
    };
    
    const stat = statSync(dirPath);
    if (stat.isFile()) {
      const type = this.detectFileType(path.basename(dirPath), dirPath);
      if (type && fileTypes.includes(type)) {
        files.push({ path: dirPath, type });
      }
    } else {
      scan(dirPath);
    }
    
    return files;
  }

  /**
   * Detect IaC file type
   */
  private detectFileType(filename: string, filePath: string): IaCType | null {
    // Terraform
    if (filename.endsWith('.tf') || filename.endsWith('.tf.json')) {
      return 'terraform';
    }
    
    // Kubernetes
    if (filename.endsWith('.yaml') || filename.endsWith('.yml')) {
      try {
        const content = readFileSync(filePath, 'utf-8');
        if (content.includes('apiVersion:') && content.includes('kind:')) {
          return 'kubernetes';
        }
      } catch {
        // Ignore read errors
      }
    }
    
    // CloudFormation
    if (filename.includes('cloudformation') || filename.includes('cfn')) {
      return 'cloudformation';
    }
    if ((filename.endsWith('.yaml') || filename.endsWith('.yml') || filename.endsWith('.json'))) {
      try {
        const content = readFileSync(filePath, 'utf-8');
        if (content.includes('AWSTemplateFormatVersion') || content.includes('AWS::')) {
          return 'cloudformation';
        }
      } catch {
        // Ignore read errors
      }
    }
    
    // Docker Compose
    if (filename === 'docker-compose.yml' || filename === 'docker-compose.yaml') {
      return 'docker-compose';
    }
    
    // Helm
    if (filename === 'Chart.yaml' || (filename.endsWith('.yaml') && filePath.includes('/templates/'))) {
      return 'helm';
    }
    
    // Ansible
    if (filename.endsWith('.yml') || filename.endsWith('.yaml')) {
      try {
        const content = readFileSync(filePath, 'utf-8');
        if (content.includes('- hosts:') || content.includes('- name:') && content.includes('tasks:')) {
          return 'ansible';
        }
      } catch {
        // Ignore read errors
      }
    }
    
    return null;
  }

  /**
   * Extract resources from IaC content
   */
  private extractResources(content: string, fileType: IaCType, filePath: string): IaCResource[] {
    const resources: IaCResource[] = [];
    const lines = content.split('\n');
    
    if (fileType === 'terraform') {
      // Extract Terraform resources
      const resourcePattern = /resource\s+"([^"]+)"\s+"([^"]+)"/;
      
      for (let i = 0; i < lines.length; i++) {
        const match = lines[i].match(resourcePattern);
        if (match) {
          resources.push({
            type: match[1],
            name: match[2],
            location: {
              file: filePath,
              startLine: i + 1,
              endLine: i + 1,
              startColumn: 0,
              endColumn: lines[i].length,
            },
            properties: {},
          });
        }
      }
    } else if (fileType === 'kubernetes') {
      // Extract Kubernetes resources
      let currentKind = '';
      let currentName = '';
      let kindLine = 0;
      
      for (let i = 0; i < lines.length; i++) {
        const kindMatch = lines[i].match(/^kind:\s*(\S+)/);
        const nameMatch = lines[i].match(/^\s*name:\s*(\S+)/);
        
        if (kindMatch) {
          if (currentKind && currentName) {
            resources.push({
              type: currentKind,
              name: currentName,
              location: {
                file: filePath,
                startLine: kindLine,
                endLine: i,
                startColumn: 0,
                endColumn: 0,
              },
              properties: {},
            });
          }
          currentKind = kindMatch[1];
          kindLine = i + 1;
          currentName = '';
        }
        
        if (nameMatch && currentKind && !currentName) {
          currentName = nameMatch[1];
        }
      }
      
      // Add last resource
      if (currentKind && currentName) {
        resources.push({
          type: currentKind,
          name: currentName,
          location: {
            file: filePath,
            startLine: kindLine,
            endLine: lines.length,
            startColumn: 0,
            endColumn: 0,
          },
          properties: {},
        });
      }
    }
    
    return resources;
  }

  /**
   * Get numeric severity level
   */
  private getSeverityLevel(severity: Severity): number {
    const levels: Record<Severity, number> = {
      critical: 4,
      high: 3,
      medium: 2,
      low: 1,
      info: 0,
    };
    return levels[severity] ?? 0;
  }
}

/**
 * Create IaC checker instance
 */
export function createIaCChecker(options?: IaCCheckOptions): IaCChecker {
  return new IaCChecker(options);
}
