FROM --platform=linux/amd64 ubuntu:24.04

# Install system dependencies including Chez Scheme
#
# Dependency Management Strategy:
# - Version pinning enabled for Renovate tracking (Jan 2026)
# - Automated updates via Renovate with manual PR review
# - Ubuntu 24.04 LTS provides API stability guarantees until 2029
# - Trade-off: Security visibility + audit trail vs absolute flexibility
#
# APT package versions tracked by Renovate (deb datasource, suite=noble)
# renovate: datasource=deb depName=ca-certificates
ARG CA_CERTIFICATES_VERSION=20240203
# renovate: datasource=deb depName=curl
ARG CURL_VERSION=8.5.0-2ubuntu10.6
# renovate: datasource=deb depName=git
ARG GIT_VERSION=1:2.43.0-1ubuntu7.3
# renovate: datasource=deb depName=build-essential
ARG BUILD_ESSENTIAL_VERSION=12.10ubuntu1
# renovate: datasource=deb depName=python3
ARG PYTHON3_VERSION=3.12.3-0ubuntu2.1
# renovate: datasource=deb depName=chezscheme
ARG CHEZSCHEME_VERSION=9.5.8+dfsg-1

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates=${CA_CERTIFICATES_VERSION} \
    curl=${CURL_VERSION} \
    git=${GIT_VERSION} \
    build-essential=${BUILD_ESSENTIAL_VERSION} \
    python3=${PYTHON3_VERSION} \
    chezscheme=${CHEZSCHEME_VERSION} \
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
