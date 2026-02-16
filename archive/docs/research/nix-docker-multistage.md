# Nix Docker Multi-Stage Build Optimization

## Overview

NixとDockerマルチステージビルドを組み合わせることで、**19倍以上のイメージサイズ削減**（624MB → 33MB）が可能。

## 主要なアプローチ

### 1. Multi-Stage Build with nix-store -qR（推奨）

最もシンプルで効果的なアプローチ。Nixのビルド成果物の「クロージャ」（実行に必要な最小限の依存関係）のみを最終イメージにコピー。

```dockerfile
# Nix builder
FROM nixos/nix:latest AS builder

COPY . /tmp/build
WORKDIR /tmp/build

# Build with Nix
RUN nix \
    --extra-experimental-features "nix-command flakes" \
    --option filter-syscalls false \
    build

# Copy the Nix store closure into a directory
RUN mkdir /tmp/nix-store-closure
RUN cp -R $(nix-store -qR result/) /tmp/nix-store-closure

# Final image is based on scratch
FROM scratch

WORKDIR /app

# Copy /nix/store (runtime dependencies only)
COPY --from=builder /tmp/nix-store-closure /nix/store
COPY --from=builder /tmp/build/result /app
CMD ["/app/bin/app"]
```

**ポイント:**
- `nix-store -qR result/`: ビルド成果物の実行時依存関係のみをリストアップ
- `FROM scratch`: ベースイメージなし（最小サイズ）
- Nixのビルド自体はbuilderステージで完結

### 2. dockerTools.buildLayeredImage

Nixネイティブのイメージビルドツール。DAGベースの最適化でレイヤーを自動分割。

```nix
pkgs.dockerTools.buildLayeredImage {
  name = "hello";
  config.Cmd = [ "${pkgs.hello}/bin/hello" ];
  maxLayers = 120;  # レイヤー数の最適化
}
```

**特徴:**
- 依存関係グラフを解析してレイヤーを最適配置
- 共有可能なレイヤー（glibc等）は分離される
- `maxLayers`: 最大125（Dockerの制限）

### 3. nix2container

高速なリビルド・プッシュサイクルを実現。

```nix
{
  inputs.nix2container.url = "github:nlewo/nix2container";
  outputs = { self, nixpkgs, nix2container }: let
    pkgs = import nixpkgs { system = "x86_64-linux"; };
    nix2containerPkgs = nix2container.packages.x86_64-linux;
  in {
    packages.x86_64-linux.hello = nix2containerPkgs.nix2container.buildImage {
      name = "hello";
      config = {
        entrypoint = ["${pkgs.hello}/bin/hello"];
      };
    };
  };
}
```

**パフォーマンス比較:**
| 手法 | リビルド/プッシュ時間 |
|------|----------------------|
| dockerTools.buildImage | ~10s |
| dockerTools.streamLayeredImage | ~7.5s |
| nix2container | ~1.8s |

## Zikuプロジェクトへの適用案

### 課題

現在のDockerfile:
- `nixos/nix:latest`ベース
- `nix develop`で開発環境全体をインストール
- イメージサイズ: **4.26GB**

### 解決策: テスト用マルチステージビルド

```dockerfile
# Stage 1: Build with Nix
FROM nixos/nix:latest AS builder

RUN mkdir -p /etc/nix && \
    echo "experimental-features = nix-command flakes" >> /etc/nix/nix.conf

WORKDIR /app

# Copy flake files
COPY flake.nix flake.lock ./

# Pre-fetch dependencies
RUN nix develop --command true

# Copy source
COPY lean-toolchain lakefile.lean lake-manifest.json ./
COPY Main.lean Ziku.lean ZikuTest.lean ./
COPY Ziku/ Ziku/
COPY Backend/ Backend/
COPY tests/ tests/
COPY Makefile ./
COPY scripts/ scripts/

# Build and collect closure
RUN nix develop --command sh -c "elan toolchain install \$(cat lean-toolchain) && lake build"
RUN mkdir /tmp/closure
RUN cp -R $(nix-store -qR /root/.elan) /tmp/closure/ 2>/dev/null || true
RUN cp -R $(nix-store -qR /nix/var/nix/profiles/default) /tmp/closure/ 2>/dev/null || true

# Stage 2: Minimal runtime
FROM debian:bookworm-slim

# Install only runtime dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    libgmp10 \
    chezscheme \
    make \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# Copy Nix store closure
COPY --from=builder /tmp/closure /nix/store

# Copy built artifacts
COPY --from=builder /app/.lake /app/.lake
COPY --from=builder /app/Makefile /app/
COPY --from=builder /app/scripts /app/scripts
COPY --from=builder /app/tests /app/tests
COPY --from=builder /root/.elan /root/.elan

ENV PATH="/root/.elan/bin:${PATH}"

CMD ["make", "test-parallel"]
```

### 代替案: Nixを使わないシンプルなアプローチ

テスト実行のみが目的なら、Nixを完全に排除して軽量化:

```dockerfile
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    git \
    chezscheme \
    make \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Install elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | \
    sh -s -- -y --default-toolchain none

ENV PATH="/root/.elan/bin:${PATH}"

WORKDIR /app
COPY . .

RUN elan toolchain install $(cat lean-toolchain) && lake build

CMD ["lake", "test"]
```

**予想サイズ:** 500MB〜1GB（Lean toolchain + Chez Scheme）

## 注意点

1. **`FROM scratch`の制限**: シェルがないためデバッグが困難
2. **Lean toolchainの依存関係**: elanが管理する依存関係のクロージャ取得が複雑
3. **テスト実行の要件**: Chez Scheme、makeなどが必要

## 参考資料

- [Using Nix with Dockerfiles – Mitchell Hashimoto](https://mitchellh.com/writing/nix-with-dockerfiles)
- [Nix and small containers with Docker multi-stage builds](https://marcopolo.io/code/nix-and-small-containers/)
- [nix2container GitHub](https://github.com/nlewo/nix2container)
- [pkgs.dockerTools | nixpkgs](https://ryantm.github.io/nixpkgs/builders/images/dockertools/)
- [Optimising Docker Layers for Better Caching with Nix](https://grahamc.com/blog/nix-and-layered-docker-images/)
- [lenianiva/lean4-nix - Nix overlay for Lean 4](https://github.com/lenianiva/lean4-nix)
