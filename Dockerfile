FROM --platform=linux/amd64 ubuntu:24.04

# Install system dependencies including Chez Scheme
#
# Dependency Management Strategy:
# - No version pinning to allow security updates from Ubuntu 24.04 LTS
# - Ubuntu LTS provides API stability guarantees until 2029
# - Current versions (as of Jan 2026):
#   - ca-certificates: SSL/TLS certificates for HTTPS connections
#   - curl: HTTP client for downloading resources
#   - git: Version control, required by Lake
#   - build-essential: GCC/G++ toolchain (12.x)
#   - python3: Build system utilities (3.12.x)
#   - chezscheme: Scheme compiler for backend (10.0.0)
#
# Trade-off: Security updates prioritized over absolute reproducibility
# For pinned builds, use --build-arg with specific versions
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    git \
    build-essential \
    python3 \
    chezscheme \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean 4 version manager)
# Pinned to specific release for reproducibility
# Latest release: https://github.com/leanprover/elan/releases
# Update strategy: Automated via GitHub Actions workflow
ARG ELAN_VERSION=v4.1.2
ENV ELAN_HOME=/root/.elan \
    PATH=/root/.elan/bin:$PATH

RUN curl -sSfL "https://raw.githubusercontent.com/leanprover/elan/${ELAN_VERSION}/elan-init.sh" | sh -s -- -y --default-toolchain none

# Install Lean toolchain
COPY lean-toolchain .
RUN elan toolchain install $(cat lean-toolchain) && \
    elan default $(cat lean-toolchain)

# Set working directory
WORKDIR /app

# Copy project files
COPY lakefile.lean lake-manifest.json lean-toolchain ./
COPY Main.lean Ziku.lean ZikuTest.lean ./
COPY Ziku/ Ziku/
COPY Backend/ Backend/
COPY tests/ tests/

# Build project
RUN lake build

# Default command
CMD ["bash"]
