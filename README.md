# MUSUBIX - Fork Repository

> This repository is a **fork** of [nahisaho/MUSUBIX](https://github.com/nahisaho/MUSUBIX) for contributing to the upstream project.

**[日本語版 README](README.ja.md)**

---

## About This Fork

This fork exists to contribute bug fixes, new features, and documentation improvements back to the original [MUSUBIX](https://github.com/nahisaho/MUSUBIX) project, as well as to develop custom extensions for personal use.

**For the full project documentation, please visit the upstream repository:**
**https://github.com/nahisaho/MUSUBIX**

---

## Acknowledgements

MUSUBIX is developed and maintained by [nahisaho](https://github.com/nahisaho). Thank you for creating and sharing this excellent neuro-symbolic AI integration system as open source.

---

## Branch Structure

| Branch | Purpose |
|--------|---------|
| [`main`](https://github.com/Takashi-So/MUSUBIX/tree/main) | Mirror of upstream `main` (always in sync) |
| [`develop`](https://github.com/Takashi-So/MUSUBIX/tree/develop) | Personal integration branch (upstream + custom improvements) |
| `contrib/*` | Contribution branches for upstream PRs (temporary) |
| `feature/*` | Custom feature branches for personal use (merged into `develop`) |
| `fork-home` | This branch - fork information display (default branch) |

---

## Workflows

### Contribution (upstream PR)

1. `main` is kept in sync with upstream
2. Contribution branches (`contrib/*`) are created from `main`
3. Pull requests are submitted to [nahisaho/MUSUBIX](https://github.com/nahisaho/MUSUBIX)
4. After merge, contribution branches are deleted

### Custom Features (personal use)

1. Feature branches (`feature/*`) are created from `develop`
2. After completion, merged into `develop`
3. These changes are not submitted to upstream

---

## Active Contributions

> This section is updated as contributions are in progress.

| Branch | Status | Description |
|--------|--------|-------------|
| `contrib/context-optimization` | In Progress | Context management optimization for sub-agent architecture |
| `contrib/docs-restructure` | In Progress | Documentation restructuring and reorganization |

---

## Links

- **Upstream Repository**: https://github.com/nahisaho/MUSUBIX
- **npm**: https://www.npmjs.com/package/musubix
- **License**: [MIT](https://github.com/nahisaho/MUSUBIX/blob/main/LICENSE)
