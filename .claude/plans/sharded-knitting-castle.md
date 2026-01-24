# Docker イメージ軽量化プラン（改訂版）

**日付**: 2026-01-24（改訂）

## 目的

Docker CIのイメージサイズを削減し、イメージのload時間を短縮する。
また、arm64/amd64両アーキテクチャで動作可能にする。

## 現状の問題

- **イメージサイズ**: 4.26GB（Nix環境全体が含まれる）
- **プラットフォーム制約**: arm64ではChezSchemeのDebianパッケージが未提供
- **前回の試行結果**: Nixクロージャ抽出は複雑すぎて断念

## 解決策: ChezSchemeをソースからビルド

ChezSchemeをソースからビルドすることで：
1. arm64/amd64両対応を実現
2. Nixへの依存を排除
3. 必要最小限の依存関係でイメージを軽量化

### ChezScheme ビルドの特徴

- **arm64サポート**: Cisco公式で完全サポート
- **ビルド時間**: 5-10分程度
- **最小化オプション**: `--disable-x11 --disable-curses`で依存関係削減
- **ランタイム依存**: libc, libz程度で済む

## 実装詳細

### Dockerfile

```dockerfile
# Multi-stage build for minimal image size
# Supports both amd64 and arm64 architectures

# Chez Scheme version (managed by Renovate)
# renovate: datasource=github-releases depName=cisco/ChezScheme
ARG CHEZ_VERSION=10.1.0

# Stage 1: Build Chez Scheme
FROM debian:bookworm-slim AS chez-builder

ARG CHEZ_VERSION

RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    curl \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /build

# Download and build Chez Scheme (minimal configuration)
RUN curl -L https://github.com/cisco/ChezScheme/releases/download/v${CHEZ_VERSION}/csv${CHEZ_VERSION}.tar.gz | tar xz && \
    cd csv${CHEZ_VERSION} && \
    ./configure --disable-x11 --disable-curses && \
    make && \
    make install DESTDIR=/chez-install

# Stage 2: Build Lean project
FROM debian:bookworm-slim AS lean-builder

RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    git \
    ca-certificates \
    make \
    && rm -rf /var/lib/apt/lists/*

# Copy Chez Scheme from previous stage
COPY --from=chez-builder /chez-install/usr/local /usr/local

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

RUN lake build

# Stage 3: Runtime (minimal)
FROM debian:bookworm-slim

# Install minimal runtime dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    git \
    make \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# Copy Chez Scheme
COPY --from=chez-builder /chez-install/usr/local /usr/local

# Copy elan and Lean toolchain
COPY --from=lean-builder /root/.elan /root/.elan
ENV PATH="/root/.elan/bin:${PATH}"

# Copy built artifacts
COPY --from=lean-builder /app/.lake /app/.lake
COPY --from=lean-builder /app/lakefile.lean /app/
COPY --from=lean-builder /app/lake-manifest.json /app/
COPY --from=lean-builder /app/lean-toolchain /app/
COPY --from=lean-builder /app/Main.lean /app/
COPY --from=lean-builder /app/Ziku.lean /app/
COPY --from=lean-builder /app/ZikuTest.lean /app/
COPY --from=lean-builder /app/Ziku /app/Ziku
COPY --from=lean-builder /app/Backend /app/Backend

# Copy test files and scripts
COPY tests/ tests/
COPY Makefile ./
COPY scripts/ scripts/

CMD ["bash", "-c", "make -j4 test-parallel"]
```

### 期待効果

- **マルチアーキテクチャ対応**: arm64/amd64両方で動作
- **Nix依存排除**: シンプルなDebianベースに
- **イメージサイズ削減**: ChezSchemeパッケージ（arm64で未提供）の問題を解決

## 修正対象ファイル

- `Dockerfile`: 3ステージビルドに書き換え
- `.github/renovate.json`: ChezScheme用のcustomManagerを追加

### renovate.json への追加

```json
{
  "customManagers": [
    {
      "customType": "regex",
      "fileMatch": ["^Dockerfile$"],
      "matchStrings": [
        "# renovate: datasource=(?<datasource>[a-z-]+) depName=(?<depName>[^\\s]+)\\nARG CHEZ_VERSION=(?<currentValue>\\d+\\.\\d+\\.\\d+)"
      ],
      "datasourceTemplate": "{{datasource}}",
      "depNameTemplate": "{{depName}}"
    }
  ]
}
```

## 検証方法

1. ローカルでイメージビルド（arm64ネイティブ）
   ```bash
   docker build -t ziku:chez-build .
   ```

2. イメージサイズ確認
   ```bash
   docker images ziku --format "table {{.Tag}}\t{{.Size}}"
   ```

3. テスト実行
   ```bash
   docker run --rm ziku:chez-build
   ```

4. schemeコマンド動作確認
   ```bash
   docker run --rm ziku:chez-build scheme --version
   ```

## 注意点

1. **ChezSchemeバージョン**: v10.1.0を使用（最新安定版）
2. **ビルド時間増加**: ChezSchemeビルドで5-10分追加
3. **キャッシュ最適化**: ChezSchemeビルドを最初のステージで分離

## 参考資料

- [Cisco ChezScheme BUILDING](https://github.com/cisco/ChezScheme/blob/main/BUILDING)
- [ChezScheme Releases](https://github.com/cisco/ChezScheme/releases)
