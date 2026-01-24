# Multi-stage build for minimal image size
# Supports both amd64 and arm64 architectures

# Stage 1: Build Lean project
FROM debian:trixie-slim AS builder

RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    git \
    ca-certificates \
    make \
    chezscheme \
    && rm -rf /var/lib/apt/lists/*

# Install elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | \
    sh -s -- -y --default-toolchain none

ENV PATH="/root/.elan/bin:${PATH}"

WORKDIR /app

# Install Lean toolchain (for caching)
COPY lean-toolchain ./
RUN elan toolchain install $(cat lean-toolchain)

# Copy dependency files and fetch
COPY lakefile.lean lake-manifest.json ./
RUN lake update

# Copy source and build
COPY Main.lean Ziku.lean ZikuTest.lean ./
COPY Ziku/ Ziku/
COPY Backend/ Backend/
COPY tests/ tests/

RUN lake build && lake build test-runner

# Stage 2: Runtime (minimal)
FROM debian:trixie-slim

# Install runtime dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    git \
    make \
    ca-certificates \
    chezscheme \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# Copy elan and Lean toolchain
COPY --from=builder /root/.elan /root/.elan
ENV PATH="/root/.elan/bin:${PATH}"

# Copy built artifacts
COPY --from=builder /app/.lake /app/.lake
COPY --from=builder /app/lakefile.lean /app/
COPY --from=builder /app/lake-manifest.json /app/
COPY --from=builder /app/lean-toolchain /app/
COPY --from=builder /app/Main.lean /app/
COPY --from=builder /app/Ziku.lean /app/
COPY --from=builder /app/ZikuTest.lean /app/
COPY --from=builder /app/Ziku /app/Ziku
COPY --from=builder /app/Backend /app/Backend

# Copy test files and scripts
COPY tests/ tests/
COPY Makefile ./
COPY scripts/ scripts/

CMD ["bash", "-c", "make -j4 test-parallel"]
