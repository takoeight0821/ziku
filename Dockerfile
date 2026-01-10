FROM --platform=linux/amd64 ubuntu:22.04

# Install system dependencies including Chez Scheme
RUN apt-get update && apt-get install -y \
    curl \
    git \
    build-essential \
    python3 \
    chezscheme \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean 4 version manager)
ENV ELAN_HOME=/usr/local/elan \
    PATH=/usr/local/elan/bin:$PATH

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

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
