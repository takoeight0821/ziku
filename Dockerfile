FROM nixos/nix:latest

# Enable flakes
RUN mkdir -p /etc/nix && \
    echo "experimental-features = nix-command flakes" >> /etc/nix/nix.conf

# Set working directory
WORKDIR /app

# Copy flake files first for better caching
COPY flake.nix flake.lock ./

# Build the development environment
RUN nix develop --command true

# Copy project files
COPY lean-toolchain lakefile.lean lake-manifest.json ./
COPY Main.lean Ziku.lean ZikuTest.lean ./
COPY Ziku/ Ziku/
COPY Backend/ Backend/
COPY tests/ tests/
COPY Makefile ./
COPY scripts/ scripts/

# Install Lean toolchain and build
RUN nix develop --command sh -c "elan toolchain install \$(cat lean-toolchain) && lake build"

# Default command
CMD ["nix", "develop", "--command", "bash"]
