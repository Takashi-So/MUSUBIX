/**
 * @nahisaho/musubix-codegraph - GitHub Adapter
 *
 * GitHub API integration using Octokit or gh CLI fallback
 *
 * @packageDocumentation
 * @module @nahisaho/musubix-codegraph/pr
 *
 * @see REQ-CG-PR-001 - GitHub Authentication
 * @see REQ-CG-PR-005 - GitHub PR Creation
 * @see DES-CG-PR-004 - Class Design
 */

import { execSync } from 'node:child_process';
import type {
  GitHubConfig,
  GitHubAuthMethod,
  GitHubAuthResult,
  PRInfo,
} from './types.js';

/**
 * Pull Request creation options for GitHub API
 */
export interface CreatePROptions {
  /** PR title */
  title: string;
  /** PR body (Markdown) */
  body: string;
  /** Head branch (the branch with changes) */
  head: string;
  /** Base branch (the branch to merge into) */
  base: string;
  /** Create as draft PR */
  draft?: boolean;
  /** Maintainer can modify */
  maintainerCanModify?: boolean;
}

/**
 * Options for updating a PR
 */
export interface UpdatePROptions {
  /** PR number */
  number: number;
  /** New title */
  title?: string;
  /** New body */
  body?: string;
  /** New state */
  state?: 'open' | 'closed';
}

/**
 * PR label
 */
export interface PRLabel {
  name: string;
  color?: string;
  description?: string;
}

/**
 * GitHub Adapter
 *
 * Provides a unified interface for GitHub operations.
 * Supports both direct API access (via GITHUB_TOKEN) and gh CLI fallback.
 *
 * @see DES-CG-PR-004
 * @example
 * ```typescript
 * const github = new GitHubAdapter({ owner: 'user', repo: 'project' });
 * await github.authenticate();
 * const pr = await github.createPullRequest({
 *   title: 'refactor: extract interface',
 *   body: '...',
 *   head: 'refactor/extract-interface',
 *   base: 'main'
 * });
 * ```
 */
export class GitHubAdapter {
  private readonly config: GitHubConfig;
  private authMethod: GitHubAuthMethod = 'none';
  private authenticated = false;
  private username?: string;

  /**
   * Create a new GitHubAdapter
   * @param config - GitHub configuration
   */
  constructor(config: GitHubConfig) {
    this.config = {
      ...config,
      baseUrl: config.baseUrl ?? 'https://api.github.com',
    };
  }

  // ============================================================================
  // Authentication
  // ============================================================================

  /**
   * Authenticate with GitHub
   * @see REQ-CG-PR-001
   */
  async authenticate(): Promise<GitHubAuthResult> {
    // Try environment variable token first
    const envToken = process.env.GITHUB_TOKEN;
    if (envToken || this.config.token) {
      const token = this.config.token ?? envToken;
      try {
        const result = await this.validateToken(token!);
        if (result.authenticated) {
          this.authMethod = 'token';
          this.authenticated = true;
          this.username = result.username;
          return result;
        }
      } catch {
        // Token validation failed, try gh CLI
      }
    }

    // Try gh CLI
    if (this.isGhCliAvailable()) {
      try {
        const result = await this.authenticateWithGhCli();
        if (result.authenticated) {
          this.authMethod = 'gh-cli';
          this.authenticated = true;
          this.username = result.username;
          return result;
        }
      } catch {
        // gh CLI auth failed
      }
    }

    return {
      authenticated: false,
      method: 'none',
      error: 'No valid authentication method found. Set GITHUB_TOKEN or authenticate with gh CLI.',
    };
  }

  /**
   * Check if authenticated
   */
  isAuthenticated(): boolean {
    return this.authenticated;
  }

  /**
   * Get authentication method
   */
  getAuthMethod(): GitHubAuthMethod {
    return this.authMethod;
  }

  /**
   * Get authenticated username
   */
  getUsername(): string | undefined {
    return this.username;
  }

  /**
   * Validate a GitHub token
   */
  private async validateToken(token: string): Promise<GitHubAuthResult> {
    try {
      const response = await fetch(`${this.config.baseUrl}/user`, {
        headers: {
          Authorization: `Bearer ${token}`,
          Accept: 'application/vnd.github+json',
          'X-GitHub-Api-Version': '2022-11-28',
        },
      });

      if (!response.ok) {
        return {
          authenticated: false,
          method: 'token',
          error: `Token validation failed: ${response.status} ${response.statusText}`,
        };
      }

      const user = await response.json() as { login: string };
      return {
        authenticated: true,
        method: 'token',
        username: user.login,
      };
    } catch (error) {
      return {
        authenticated: false,
        method: 'token',
        error: `Token validation error: ${error instanceof Error ? error.message : String(error)}`,
      };
    }
  }

  /**
   * Check if gh CLI is available
   */
  private isGhCliAvailable(): boolean {
    try {
      execSync('gh --version', { stdio: 'pipe' });
      return true;
    } catch {
      return false;
    }
  }

  /**
   * Authenticate using gh CLI
   */
  private async authenticateWithGhCli(): Promise<GitHubAuthResult> {
    try {
      // Check auth status
      execSync('gh auth status', {
        encoding: 'utf-8',
        stdio: ['pipe', 'pipe', 'pipe'],
      });

      // Get username
      const username = execSync('gh api user --jq .login', {
        encoding: 'utf-8',
        stdio: ['pipe', 'pipe', 'pipe'],
      }).trim();

      return {
        authenticated: true,
        method: 'gh-cli',
        username,
      };
    } catch (error) {
      return {
        authenticated: false,
        method: 'gh-cli',
        error: `gh CLI authentication failed: ${error instanceof Error ? error.message : String(error)}`,
      };
    }
  }

  // ============================================================================
  // Pull Request Operations
  // ============================================================================

  /**
   * Create a pull request
   * @see REQ-CG-PR-005
   */
  async createPullRequest(options: CreatePROptions): Promise<PRInfo> {
    this.ensureAuthenticated();

    if (this.authMethod === 'gh-cli') {
      return this.createPRWithGhCli(options);
    }

    return this.createPRWithApi(options);
  }

  /**
   * Create PR using GitHub API
   */
  private async createPRWithApi(options: CreatePROptions): Promise<PRInfo> {
    const token = this.config.token ?? process.env.GITHUB_TOKEN;
    if (!token) {
      throw new Error('No GitHub token available');
    }

    const response = await fetch(
      `${this.config.baseUrl}/repos/${this.config.owner}/${this.config.repo}/pulls`,
      {
        method: 'POST',
        headers: {
          Authorization: `Bearer ${token}`,
          Accept: 'application/vnd.github+json',
          'X-GitHub-Api-Version': '2022-11-28',
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({
          title: options.title,
          body: options.body,
          head: options.head,
          base: options.base,
          draft: options.draft ?? false,
          maintainer_can_modify: options.maintainerCanModify ?? true,
        }),
      }
    );

    if (!response.ok) {
      const error = await response.json() as { message: string };
      throw new Error(`Failed to create PR: ${response.status} ${error.message}`);
    }

    const pr = await response.json() as {
      number: number;
      html_url: string;
      title: string;
      state: 'open' | 'closed';
      head: { ref: string };
      base: { ref: string };
      created_at: string;
    };

    return {
      number: pr.number,
      url: pr.html_url,
      title: pr.title,
      state: pr.state,
      head: pr.head.ref,
      base: pr.base.ref,
      createdAt: new Date(pr.created_at),
    };
  }

  /**
   * Create PR using gh CLI
   */
  private createPRWithGhCli(options: CreatePROptions): PRInfo {
    const args = [
      'pr', 'create',
      '--repo', `${this.config.owner}/${this.config.repo}`,
      '--title', options.title,
      '--body', options.body,
      '--head', options.head,
      '--base', options.base,
    ];

    if (options.draft) {
      args.push('--draft');
    }

    try {
      const output = execSync(`gh ${args.join(' ')}`, {
        encoding: 'utf-8',
        stdio: ['pipe', 'pipe', 'pipe'],
      }).trim();

      // Parse PR URL from output
      const urlMatch = output.match(/https:\/\/github\.com\/[^/]+\/[^/]+\/pull\/(\d+)/);
      if (!urlMatch) {
        throw new Error(`Failed to parse PR URL from gh output: ${output}`);
      }

      const prNumber = parseInt(urlMatch[1], 10);

      return {
        number: prNumber,
        url: output,
        title: options.title,
        state: 'open',
        head: options.head,
        base: options.base,
        createdAt: new Date(),
      };
    } catch (error) {
      throw new Error(
        `gh CLI PR creation failed: ${error instanceof Error ? error.message : String(error)}`
      );
    }
  }

  /**
   * Get PR information
   */
  async getPullRequest(prNumber: number): Promise<PRInfo> {
    this.ensureAuthenticated();

    if (this.authMethod === 'gh-cli') {
      return this.getPRWithGhCli(prNumber);
    }

    return this.getPRWithApi(prNumber);
  }

  /**
   * Get PR using API
   */
  private async getPRWithApi(prNumber: number): Promise<PRInfo> {
    const token = this.config.token ?? process.env.GITHUB_TOKEN;
    if (!token) {
      throw new Error('No GitHub token available');
    }

    const response = await fetch(
      `${this.config.baseUrl}/repos/${this.config.owner}/${this.config.repo}/pulls/${prNumber}`,
      {
        headers: {
          Authorization: `Bearer ${token}`,
          Accept: 'application/vnd.github+json',
          'X-GitHub-Api-Version': '2022-11-28',
        },
      }
    );

    if (!response.ok) {
      throw new Error(`Failed to get PR: ${response.status}`);
    }

    const pr = await response.json() as {
      number: number;
      html_url: string;
      title: string;
      state: 'open' | 'closed';
      merged: boolean;
      head: { ref: string };
      base: { ref: string };
      created_at: string;
    };

    return {
      number: pr.number,
      url: pr.html_url,
      title: pr.title,
      state: pr.merged ? 'merged' : pr.state,
      head: pr.head.ref,
      base: pr.base.ref,
      createdAt: new Date(pr.created_at),
    };
  }

  /**
   * Get PR using gh CLI
   */
  private getPRWithGhCli(prNumber: number): PRInfo {
    try {
      const output = execSync(
        `gh pr view ${prNumber} --repo ${this.config.owner}/${this.config.repo} --json number,url,title,state,headRefName,baseRefName,createdAt`,
        { encoding: 'utf-8', stdio: ['pipe', 'pipe', 'pipe'] }
      );

      const pr = JSON.parse(output) as {
        number: number;
        url: string;
        title: string;
        state: string;
        headRefName: string;
        baseRefName: string;
        createdAt: string;
      };

      return {
        number: pr.number,
        url: pr.url,
        title: pr.title,
        state: pr.state.toLowerCase() as 'open' | 'closed' | 'merged',
        head: pr.headRefName,
        base: pr.baseRefName,
        createdAt: new Date(pr.createdAt),
      };
    } catch (error) {
      throw new Error(
        `Failed to get PR: ${error instanceof Error ? error.message : String(error)}`
      );
    }
  }

  /**
   * Add labels to PR
   */
  async addLabels(prNumber: number, labels: string[]): Promise<void> {
    this.ensureAuthenticated();

    if (this.authMethod === 'gh-cli') {
      execSync(
        `gh pr edit ${prNumber} --repo ${this.config.owner}/${this.config.repo} --add-label "${labels.join(',')}"`,
        { stdio: 'pipe' }
      );
      return;
    }

    const token = this.config.token ?? process.env.GITHUB_TOKEN;
    if (!token) {
      throw new Error('No GitHub token available');
    }

    await fetch(
      `${this.config.baseUrl}/repos/${this.config.owner}/${this.config.repo}/issues/${prNumber}/labels`,
      {
        method: 'POST',
        headers: {
          Authorization: `Bearer ${token}`,
          Accept: 'application/vnd.github+json',
          'X-GitHub-Api-Version': '2022-11-28',
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({ labels }),
      }
    );
  }

  /**
   * Add reviewers to PR
   */
  async addReviewers(prNumber: number, reviewers: string[]): Promise<void> {
    this.ensureAuthenticated();

    if (this.authMethod === 'gh-cli') {
      execSync(
        `gh pr edit ${prNumber} --repo ${this.config.owner}/${this.config.repo} --add-reviewer "${reviewers.join(',')}"`,
        { stdio: 'pipe' }
      );
      return;
    }

    const token = this.config.token ?? process.env.GITHUB_TOKEN;
    if (!token) {
      throw new Error('No GitHub token available');
    }

    await fetch(
      `${this.config.baseUrl}/repos/${this.config.owner}/${this.config.repo}/pulls/${prNumber}/requested_reviewers`,
      {
        method: 'POST',
        headers: {
          Authorization: `Bearer ${token}`,
          Accept: 'application/vnd.github+json',
          'X-GitHub-Api-Version': '2022-11-28',
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({ reviewers }),
      }
    );
  }

  /**
   * Add assignees to PR
   */
  async addAssignees(prNumber: number, assignees: string[]): Promise<void> {
    this.ensureAuthenticated();

    if (this.authMethod === 'gh-cli') {
      execSync(
        `gh pr edit ${prNumber} --repo ${this.config.owner}/${this.config.repo} --add-assignee "${assignees.join(',')}"`,
        { stdio: 'pipe' }
      );
      return;
    }

    const token = this.config.token ?? process.env.GITHUB_TOKEN;
    if (!token) {
      throw new Error('No GitHub token available');
    }

    await fetch(
      `${this.config.baseUrl}/repos/${this.config.owner}/${this.config.repo}/issues/${prNumber}/assignees`,
      {
        method: 'POST',
        headers: {
          Authorization: `Bearer ${token}`,
          Accept: 'application/vnd.github+json',
          'X-GitHub-Api-Version': '2022-11-28',
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({ assignees }),
      }
    );
  }

  // ============================================================================
  // Repository Information
  // ============================================================================

  /**
   * Get repository information
   */
  async getRepository(): Promise<{ defaultBranch: string; private: boolean }> {
    this.ensureAuthenticated();

    if (this.authMethod === 'gh-cli') {
      const output = execSync(
        `gh repo view ${this.config.owner}/${this.config.repo} --json defaultBranchRef,isPrivate`,
        { encoding: 'utf-8', stdio: ['pipe', 'pipe', 'pipe'] }
      );
      const repo = JSON.parse(output) as {
        defaultBranchRef: { name: string };
        isPrivate: boolean;
      };
      return {
        defaultBranch: repo.defaultBranchRef.name,
        private: repo.isPrivate,
      };
    }

    const token = this.config.token ?? process.env.GITHUB_TOKEN;
    if (!token) {
      throw new Error('No GitHub token available');
    }

    const response = await fetch(
      `${this.config.baseUrl}/repos/${this.config.owner}/${this.config.repo}`,
      {
        headers: {
          Authorization: `Bearer ${token}`,
          Accept: 'application/vnd.github+json',
          'X-GitHub-Api-Version': '2022-11-28',
        },
      }
    );

    if (!response.ok) {
      throw new Error(`Failed to get repository: ${response.status}`);
    }

    const repo = await response.json() as {
      default_branch: string;
      private: boolean;
    };

    return {
      defaultBranch: repo.default_branch,
      private: repo.private,
    };
  }

  // ============================================================================
  // Private Helpers
  // ============================================================================

  /**
   * Ensure authenticated before operations
   */
  private ensureAuthenticated(): void {
    if (!this.authenticated) {
      throw new Error('Not authenticated. Call authenticate() first.');
    }
  }
}

/**
 * Create a GitHubAdapter instance
 */
export function createGitHubAdapter(
  owner: string,
  repo: string,
  token?: string
): GitHubAdapter {
  return new GitHubAdapter({ owner, repo, token });
}
