# Dependency Management: Docker Best Practices and Renovate Bot

**Research Date:** January 10, 2026
**Purpose:** Inform implementation of Issue #25 - Docker and GitHub Actions dependency management improvements

## Executive Summary

This research explores best practices for Docker dependency management and evaluates Renovate as an automated dependency update tool. Key findings:

- **APT package pinning trade-off**: Security updates vs reproducibility is an active debate, with growing consensus toward security-first approach for LTS systems
- **Renovate capabilities**: Superior to Dependabot in features (90+ package managers, digest pinning, automerge) but requires more configuration
- **Elan stability**: Lean version manager has stable release cadence, latest v4.1.2 (May 2025)
- **Hybrid approach recommended**: Combine Renovate for general dependencies with custom automation for domain-specific tooling

---

## Part 1: Docker Dependency Management Best Practices

### The Security vs Reproducibility Debate

#### Core Trade-off

> "SHA pinning gives you completely reliable and reproducible builds, but it also likely means you won't have any obvious way to pull in important security fixes from the base images you use. If you use major.minor tags, you get security fixes by accident when you build new versions of your image - at the cost of builds being less reproducible."
>
> — [Always Use Docker Image Digests - Craig Andrews](https://candrews.integralblue.com/2023/09/always-use-docker-image-digests/)

#### Arguments Against APT Version Pinning (Pro-Security)

The traditional "best practice" of avoiding `apt-get upgrade` in Dockerfiles is increasingly challenged:

- **Security updates are critical**: Ubuntu releases security updates regularly (e.g., libzstd1 patches) that aren't in older base images
- **LTS stability**: With Ubuntu LTS, package updates are stable and won't break code
- **Real-world risk**: Many teams pin versions but never upgrade, creating long-term security debt

> "Many official sources, including Docker's documentation, have historically advised against running apt-get upgrade in Docker images, but this advice is increasingly challenged."
>
> — [The worst so-called "best practice" for Docker](https://pythonspeed.com/articles/security-updates-in-docker/)

#### Arguments For Version Pinning (Pro-Reproducibility)

The reproducibility perspective:

- **Build consistency**: Version pinning prevents unwanted upgrades and undefined behavior
- **Cache control**: Forces builds to retrieve specific versions regardless of cache state
- **Repository availability concerns**: Old package versions sometimes get removed from APT repositories

> "Version pinning forces the build to retrieve a particular version regardless of what's in the cache. This technique can also reduce failures due to unanticipated changes in required packages."
>
> — [Best practices | Docker Docs](https://docs.docker.com/build/building/best-practices/)

#### Recommended Hybrid Solution: Digest Pinning + Automation

Modern best practice combines both goals:

1. **Pin to digests for reproducibility**: Use SHA256 digests instead of mutable tags
2. **Automate digest updates for security**: Tools like Docker Scout or Renovate raise PRs for new versions
3. **Maintain audit trail**: Version changes are tracked in git history with CI validation

> "Docker Scout supports an automated remediation workflow for keeping your base images up-to-date. When a new image digest is available, Docker Scout can automatically raise a pull request on your repository to update your Dockerfiles to use the latest version. This is better than using a tag that changes the version automatically, because you're in control and you have an audit trail of when and how the change occurred."
>
> — [Docker Security: 14 Best Practices | Better Stack](https://betterstack.com/community/guides/scaling-docker/docker-security-best-practices/)

#### Tool: docker-lock

A practical implementation of this approach:

- Tracks exact Docker image SHAs while using major.minor tags in Dockerfiles
- Enables reproducible builds as if using SHA pinning
- Allows security updates when new major.minor releases occur
- Provides the best of both worlds

### APT Package Management Recommendations

**For Ubuntu LTS-based images:**

1. **Don't pin APT package versions** for most use cases
2. **Rely on LTS stability guarantees** (API compatibility until EOL)
3. **Document package purpose** in comments for audit trail
4. **Consider pinning only critical packages** where breaking changes are unacceptable
5. **Accept security-first trade-off** over absolute reproducibility

**Exception cases requiring pinning:**

- Compiler toolchains with strict version requirements
- Libraries with known breaking changes between minor versions
- Compliance requirements mandating exact version tracking

---

## Part 2: Renovate Bot Deep Dive

### Overview

**Repository:** [renovatebot/renovate](https://github.com/renovatebot/renovate)
**Stars:** 20,525+ (as of January 2026)
**License:** AGPL-3.0
**Maintainer:** Mend.io
**Language:** TypeScript

> "Renovate is an automated dependency update tool. It helps to update dependencies in your code without needing to do it manually."
>
> — [Renovate GitHub Repository](https://github.com/renovatebot/renovate)

### Key Features

#### 1. Automated Discovery and Updates

- Scans repositories for outdated dependencies across 90+ package managers
- Automatically creates pull requests with updates
- Provides metadata: age, adoption rates, merge confidence scores

#### 2. Dependency Dashboard

Enabled by default, provides centralized view of:
- Pending updates
- Ignored/pinned dependencies
- Failed update attempts
- Scheduled updates

#### 3. Merge Confidence

Four-part scoring system:
- **Age**: How long the version has existed
- **Adoption**: How many projects use it
- **Passing**: CI test success rates
- **Confidence**: Overall recommendation score

(Compared to Dependabot's single compatibility score)

#### 4. Flexible Scheduling and Grouping

- Per-dependency or global schedules (e.g., "before 9am on Monday")
- Community presets for common groupings (monorepo packages in single PR)
- Manual configuration supported

#### 5. Automerge with CI Validation

```json
{
  "automerge": true,
  "platformAutomerge": true,
  "automergeType": "pr"
}
```

PRs automatically merge after tests pass (unlike Dependabot which requires separate GitHub configuration).

### Supported Package Managers

Renovate supports 90+ package managers including:

- **JavaScript**: npm, Yarn, pnpm, Bun
- **Python**: pip, Poetry, Pipenv
- **Java**: Maven, Gradle
- **Ruby**: Bundler
- **Go**: Go modules
- **Rust**: Cargo
- **Docker**: Dockerfile, docker-compose
- **CI/CD**: GitHub Actions, GitLab CI, CircleCI
- **Infrastructure**: Terraform, Kubernetes, Helm
- **And many more...**

### Platform Support

- GitHub (native GitHub App)
- GitLab
- Bitbucket
- Azure DevOps
- AWS CodeCommit
- Gitea
- Forgejo
- Gerrit (experimental)

(Dependabot officially supports only GitHub and Azure DevOps)

### Deployment Options

1. **GitHub App** (recommended): Zero infrastructure, free for public repos
2. **Self-hosted CLI**: npm package `renovate`, runs in any Node.js environment
3. **Docker**: Images on Docker Hub (`renovate/renovate`) and GHCR (`ghcr.io/renovatebot/renovate`)
4. **CI/CD Integration**: GitHub Actions, GitLab Runner workflows
5. **Enterprise**: Commercial on-premises solutions by Mend.io

---

## Part 3: Renovate vs Dependabot Comparison

### Feature Matrix

| Feature | Renovate | Dependabot | Winner |
|---------|----------|------------|--------|
| **GitHub Actions** | ✅ + digest pinning presets | ✅ Basic support | Renovate |
| **Docker base images** | ✅ Full support | ✅ Full support | Tie |
| **Git submodules** | ✅ + advanced config | ✅ Basic support | Renovate |
| **Package managers** | 90+ | ~20 | Renovate |
| **Platform support** | Multi-platform | GitHub, Azure only | Renovate |
| **Dependency Dashboard** | ✅ Default | ❌ Not available | Renovate |
| **Grouping** | ✅ Community presets | ⚠️ Manual config | Renovate |
| **Automerge** | ✅ Built-in with CI | ⚠️ Limited | Renovate |
| **Merge Confidence** | ✅ 4-part scoring | ⚠️ Single score | Renovate |
| **Monorepo support** | ✅ Single PR | ⚠️ Multiple PRs | Renovate |
| **Configuration flexibility** | ✅ Extensive | ⚠️ Limited | Renovate |
| **Setup complexity** | ⚠️ App install + config | ✅ Native GitHub | Dependabot |
| **License** | AGPL-3.0 | MIT | Dependabot |
| **Release notes** | ✅ External links | ✅ Integrated display | Dependabot |

### When to Use Dependabot

- Already using GitHub exclusively
- Prefer zero-configuration setup
- MIT license requirement
- Simple dependency update needs
- Don't need advanced grouping or automerge

### When to Use Renovate

- Need multi-platform support (GitLab, Bitbucket, etc.)
- Want digest pinning for GitHub Actions (supply chain security)
- Require flexible scheduling and grouping
- Need automerge with CI validation
- Working with monorepos
- Want extensibility (custom managers, regex matching)

---

## Part 4: Renovate's Custom Regex Manager

### Purpose

Detect dependencies not covered by built-in package managers (e.g., shell scripts, custom tools, ARG variables).

### Configuration Requirements

Renovate needs three pieces of information:

1. **Dependency name**: `depName` or `packageName` capture group
2. **Datasource**: Where to check for updates (npm, Docker, GitHub releases, etc.)
3. **Versioning**: Defaults to `semver-coerced`, alternatives include `pep440`, `loose`

### Example: Dockerfile ARG Variable

```json
{
  "customManagers": [
    {
      "customType": "regex",
      "fileMatch": ["^Dockerfile$"],
      "matchStrings": [
        "ARG ELAN_VERSION=(?<currentValue>.*?)\\n"
      ],
      "depNameTemplate": "elan",
      "datasourceTemplate": "github-releases",
      "packageNameTemplate": "leanprover/elan",
      "extractVersionTemplate": "^v(?<version>.*)$"
    }
  ]
}
```

### Limitations

- **Regex engine**: Uses RE2 (no backreferences or lookahead assertions)
- **Matching scope**: Per-file, not per-line (`^` and `$` match file boundaries)
- **Complexity**: Manual regex configuration required, fragile to format changes

### Use Cases for Ziku Project

**Potentially useful:**
- Elan installer version in Dockerfile
- Lean toolchain version in `lean-toolchain` file

**Not recommended:**
- APT packages (complex regex, marginal benefit)
- Lake dependencies (already handled by custom workflow)

---

## Part 5: Renovate's Dockerfile Manager

### Detection Capabilities

Automatically detects:

- `FROM` directives (base images)
- `COPY --from` (multi-stage builds)
- `RUN --mount` (build-time mounts)
- `syntax` directives (Dockerfile syntax versions)

Handles:
- `--platform` flags
- `ARG` variable expansion
- Multi-stage builds

### What It Cannot Do

- **APT packages**: No native support for detecting/updating `apt-get install` versions
- **Custom URLs**: Doesn't detect raw curl commands (requires regex manager)
- **Semantic understanding**: Treats Dockerfiles as text, not understanding full context

### Example Configuration

```json
{
  "packageRules": [
    {
      "matchDatasources": ["docker"],
      "matchPackageNames": ["ubuntu"],
      "allowedVersions": "!/^.*-slim$/"
    }
  ]
}
```

This allows filtering specific image tags or versions.

---

## Part 6: Elan Version Manager

### Overview

**Repository:** [leanprover/elan](https://github.com/leanprover/elan)
**Purpose:** Lean theorem prover version manager
**Based on:** rustup (Rust version manager fork)
**Language:** 95.2% Rust
**Latest Release:** v4.1.2 (May 26, 2025)

### How It Works

> "Elan places `lean` and `lake` binaries in your `PATH` that automatically select and, if necessary, download the Lean version described in your project's `lean-toolchain` file."
>
> — [Elan GitHub Repository](https://github.com/leanprover/elan)

**Key mechanism:**
1. Project has `lean-toolchain` file (e.g., `leanprover/lean4:v4.26.0`)
2. Running `lean` or `lake` triggers elan
3. Elan checks toolchain file, downloads if needed, executes correct version

### Installation Methods

**Unix-like systems:**
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

**Windows:**
```powershell
# PowerShell script (see repository)
```

**NixOS:**
```bash
nix-env -iA nixpkgs.elan
```

**Manual:** Download binaries from GitHub releases

### Release History

Elan has 67 total releases with regular maintenance:

```
v4.1.2   - 2025-05-26  (Latest stable)
v4.1.1   - 2025-04-30
v4.1.0   - 2025-04-30
v4.0.1   - 2025-04-18
v4.0.0   - 2025-01-30
v3.1.1   - 2024-02-22
v3.1.0   - 2024-02-19
v3.0.0   - 2023-09-08
```

**Release cadence:** Approximately quarterly for stable releases, with more frequent experimental branches.

### Pinning Strategy for Ziku

**Recommended approach:**

```dockerfile
# Pin to specific release tag
ARG ELAN_VERSION=v4.1.2
RUN curl -sSfL "https://raw.githubusercontent.com/leanprover/elan/${ELAN_VERSION}/elan-init.sh" | sh -s -- -y --default-toolchain none
```

**Rationale:**
- Releases are stable and infrequent
- Tag pinning is maintainable
- Can automate updates via GitHub Actions
- Elan itself is backward-compatible with older Lean versions

**Alternative (maximum security):**

Add SHA256 checksum verification:
```dockerfile
ARG ELAN_VERSION=v4.1.2
ARG ELAN_INIT_SHA256=<checksum>
RUN curl -sSfL "https://raw.githubusercontent.com/leanprover/elan/${ELAN_VERSION}/elan-init.sh" -o /tmp/elan-init.sh && \
    echo "${ELAN_INIT_SHA256}  /tmp/elan-init.sh" | sha256sum -c - && \
    sh /tmp/elan-init.sh -y --default-toolchain none
```

**Trade-off:** Checksum verification is most secure but requires maintaining checksums for each version.

---

## Part 7: Implementation Recommendations for Ziku

Based on this research, here are evidence-based recommendations for Issue #25:

### 1. Elan Installer Pinning ✅ HIGH PRIORITY

**Recommendation:** Pin to git release tags with automated updates

**Implementation:**
```dockerfile
ARG ELAN_VERSION=v4.1.2
RUN curl -sSfL "https://raw.githubusercontent.com/leanprover/elan/${ELAN_VERSION}/elan-init.sh" | sh -s -- -y --default-toolchain none
```

**Automation:**
Add job to `.github/workflows/update-dependencies.yml` that:
1. Queries GitHub API for latest elan release
2. Updates Dockerfile ARG if new version exists
3. Creates PR with CI validation

**Rationale:**
- Elan releases are stable (quarterly cadence)
- Tag pinning balances security and maintainability
- Automated updates prevent stale versions

### 2. APT Package Strategy ✅ DOCUMENT, DON'T PIN

**Recommendation:** Do NOT pin APT package versions

**Rationale:**
- Ubuntu 24.04 LTS provides stability until 2029
- Security updates are more important than absolute reproducibility
- Maintenance burden of pinning outweighs benefits
- Package repositories sometimes remove old versions

**Implementation:**
Add comprehensive Dockerfile comments:
```dockerfile
# APT Packages (unpinned for security updates)
# Strategy: Security-first approach relying on Ubuntu 24.04 LTS stability
# Trade-off: Accepts minor version changes for security patches
# Current versions (Jan 2026):
#   - build-essential: GCC/G++ 12.x
#   - python3: 3.12.x
#   - chezscheme: 10.0.0
```

### 3. Migrate to Renovate - Hybrid Approach ✅ HIGH PRIORITY

**Recommendation:** Use Renovate for GitHub Actions, Docker, submodules; keep custom workflow for Lean/Lake

**Rationale:**
- **Digest pinning** for GitHub Actions improves supply chain security
- **Automerge** reduces PR backlog
- **90+ package managers** provides extensibility
- **Custom workflow validation** for Lean/Lake ensures builds work

**Configuration:**
```json
{
  "$schema": "https://docs.renovatebot.com/renovate-schema.json",
  "extends": [
    "config:recommended",
    "helpers:pinGitHubActionDigestsToSemver"
  ],
  "schedule": ["before 9am on Monday"],
  "packageRules": [
    {
      "matchManagers": ["github-actions"],
      "groupName": "GitHub Actions",
      "pinDigests": true
    }
  ]
}
```

### 4. Optional: Renovate Regex Manager for Elan

**Recommendation:** Consider adding if manual updates become burdensome

**Implementation:**
```json
{
  "customManagers": [
    {
      "customType": "regex",
      "fileMatch": ["^Dockerfile$"],
      "matchStrings": [
        "ARG ELAN_VERSION=(?<currentValue>v[0-9.]+)"
      ],
      "datasourceTemplate": "github-releases",
      "depNameTemplate": "elan",
      "packageNameTemplate": "leanprover/elan"
    }
  ]
}
```

**Trade-off:** Adds complexity for marginal benefit since elan updates are infrequent. Custom workflow may be simpler.

---

## Conclusion

Modern dependency management balances three goals:
1. **Security**: Automated updates for vulnerabilities
2. **Reproducibility**: Version pinning for consistent builds
3. **Maintainability**: Automation reduces manual burden

**Key insights:**
- **Digest pinning + automation** solves security vs reproducibility debate
- **Renovate superiority** is clear for complex projects (90+ managers, automerge, digest pinning)
- **APT pinning debate** increasingly favors security-first for LTS systems
- **Hybrid approaches** leverage strengths of different tools

**For Ziku specifically:**
- Pin elan to release tags with automated updates
- Document (but don't pin) APT packages
- Migrate to Renovate for general dependencies
- Keep custom workflow for Lean-specific tooling with validation

This approach provides comprehensive coverage, strong security posture, and maintainable automation with clear audit trails.

---

## Sources

### Renovate Documentation
- [GitHub - renovatebot/renovate](https://github.com/renovatebot/renovate)
- [Bot comparison - Renovate Docs](https://docs.renovatebot.com/bot-comparison/)
- [Custom Manager Support using Regex - Renovate Docs](https://docs.renovatebot.com/modules/manager/regex/)
- [Automated Dependency Updates for Dockerfile - Renovate Docs](https://docs.renovatebot.com/modules/manager/dockerfile/)
- [Automated Dependency Updates for GitHub Actions - Renovate Docs](https://docs.renovatebot.com/modules/manager/github-actions/)
- [Renovate - Automatic Dependency Updates | ServerSpace](https://serverspace.io/support/help/renovate-automatic-dependency-updates-github-bot-for-projects/)
- [Mend Renovate Products](https://www.mend.io/renovate/)

### Docker Best Practices
- [Best practices | Docker Docs](https://docs.docker.com/build/building/best-practices/)
- [Always Use Docker Image Digests - Craig Andrews](https://candrews.integralblue.com/2023/09/always-use-docker-image-digests/)
- [Docker Security: 14 Best Practices | Better Stack](https://betterstack.com/community/guides/scaling-docker/docker-security-best-practices/)
- [Docker Tip #18: Pin Your Docker Image Versions - Nick Janetakis](https://nickjanetakis.com/blog/docker-tip-18-please-pin-your-docker-image-versions)

### APT Package Pinning Debate
- [The worst so-called "best practice" for Docker](https://pythonspeed.com/articles/security-updates-in-docker/)
- [Always pin versions in apt-get install - Datadog](https://docs.datadoghq.com/security/code_security/static_analysis/static_analysis_rules/docker-best-practices/apt-pin-version/)
- [GitHub Issue: Should we pin OS packages in Dockerfiles?](https://github.com/sourcegraph/lsp-adapter/issues/72)
- [Use pinned versions for apt-get packages - PR #570](https://github.com/replicate/cog/pull/570)
- [Why You Should Always Specify Version Numbers - Samuel Fajreldines](https://www.samuelfaj.com/posts/2025-01-29-115351/index.html)

### Elan Version Manager
- [GitHub - leanprover/elan](https://github.com/leanprover/elan)
- [Elan Releases](https://github.com/leanprover/elan/releases)

### Dependency Management Comparisons
- [Renovate vs Dependabot - TurboStarter](https://www.turbostarter.dev/blog/renovate-vs-dependabot-whats-the-best-tool-to-automate-your-dependency-updates)
- [Dependabot vs. Renovate - PullNotifier Blog](https://blog.pullnotifier.com/blog/dependabot-vs-renovate-dependency-update-tools)

### Tools
- [GitHub - Jille/dockpin: Pin Docker image and apt package versions](https://github.com/Jille/dockpin)
- [How to Use Container Image Digests - Chainguard Academy](https://edu.chainguard.dev/chainguard/chainguard-images/how-to-use/container-image-digests/)
