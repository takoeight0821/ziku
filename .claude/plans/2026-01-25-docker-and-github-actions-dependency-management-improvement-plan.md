# Docker and GitHub Actions Dependency Management Improvement Plan

**日付**: 2026-01-25
**Issue**: https://github.com/takoeight0821/ziku/issues/25

## 現状分析

### 既に実装済み ✅

1. **Renovate設定** (`.github/renovate.json`, `.github/workflows/renovate.yml`)
   - GitHub Actions (SHA digest pinning)
   - Nix flake inputs
   - Git submodules

2. **カスタムワークフロー** (`.github/workflows/update-dependencies.yml`)
   - Lean toolchain更新
   - Lake dependencies更新
   - Elan version更新ジョブ（ただしDockerfileにARGがない）

3. **ドキュメント** (`README.md`)
   - Renovateセットアップ手順
   - 依存関係管理の説明

### ギャップ（対応が必要）

1. **DockerfileにELAN_VERSION ARGがない**
   - `update-elan-version`ジョブがDockerfile内の`ARG ELAN_VERSION=`を期待しているが存在しない
   - elanは未だmasterブランチから直接取得

2. **lean_action_ci.ymlでもelanがピン留めされていない**
   - 28行目: masterブランチから取得

3. **dependabot.ymlがまだ存在**
   - Renovateが同じ機能をカバーしているため冗長
   - 重複PRの原因になる可能性

4. **APTパッケージの方針が文書化されていない**
   - なぜバージョン固定しないかの説明がない

## 実装計画

### Phase 1: Dockerfileのelanバージョン固定

**ファイル**: `Dockerfile`

**変更内容**:
```dockerfile
# Stage 1: Build Lean project
FROM debian:trixie-slim AS builder

# Elan version - updated automatically by update-dependencies.yml
ARG ELAN_VERSION=v4.1.2

# APT packages: Using Debian trixie LTS packages without version pinning
# Rationale: Security updates are prioritized over absolute reproducibility.
# Debian trixie provides API stability for its support period.
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    git \
    ca-certificates \
    make \
    chezscheme \
    && rm -rf /var/lib/apt/lists/*

# Install elan from specific release (not master branch)
RUN curl -sSf -L "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-init.sh" | \
    sh -s -- -y --default-toolchain none
```

### Phase 2: lean_action_ci.ymlのelanピン留め

**ファイル**: `.github/workflows/lean_action_ci.yml`

**変更内容** (28行目付近):
```yaml
- name: Install elan
  env:
    ELAN_VERSION: v4.1.2  # Updated by update-dependencies.yml
  run: |
    curl -sSf -L "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-init.sh" | sh -s -- -y --default-toolchain none
    echo "$HOME/.elan/bin" >> $GITHUB_PATH
```

### Phase 3: update-dependencies.ymlのelanジョブ修正

**ファイル**: `.github/workflows/update-dependencies.yml`

**変更内容**:
- Dockerfileに加えてlean_action_ci.ymlも更新するように拡張
- 両方のファイルでELAN_VERSIONを更新

```yaml
update-elan-version:
  runs-on: ubuntu-latest
  steps:
    - name: Checkout repository
      uses: actions/checkout@8e8c483db84b4bee98b60c0593521ed34d9990e8 # v6.0.1

    - name: Check for elan updates
      id: check
      run: |
        current_version=$(grep 'ARG ELAN_VERSION=' Dockerfile | cut -d= -f2)
        echo "Current version: $current_version"

        latest_version=$(curl -s "https://api.github.com/repos/leanprover/elan/releases/latest" | jq -r .tag_name)
        echo "Latest version: $latest_version"

        if [ "$current_version" != "$latest_version" ]; then
          echo "New version available!"
          # Update Dockerfile
          sed -i "s/ARG ELAN_VERSION=.*/ARG ELAN_VERSION=$latest_version/" Dockerfile
          # Update lean_action_ci.yml
          sed -i "s/ELAN_VERSION: .*/ELAN_VERSION: $latest_version/" .github/workflows/lean_action_ci.yml
          echo "updated=true" >> $GITHUB_OUTPUT
          echo "version=$latest_version" >> $GITHUB_OUTPUT
        else
          echo "Already up to date."
          echo "updated=false" >> $GITHUB_OUTPUT
        fi
    # ... rest of job
```

### Phase 4: dependabot.ymlの削除

**ファイル**: `.github/dependabot.yml`

**アクション**: ファイル削除（`trash`コマンド使用）

**理由**:
- Renovateが同等以上の機能を提供
- GitHub Actions: Renovateでdigest pinning対応
- Docker: Renovateで対応
- Git submodules: Renovateで対応

### Phase 5: ドキュメント更新

**ファイル**: `CLAUDE.md`

**変更内容**:
- 依存関係管理セクションの更新
- Renovate + カスタムワークフローのハイブリッドアプローチの説明

## 修正対象ファイル一覧

1. `Dockerfile` - ELAN_VERSION ARG追加、APTコメント追加
2. `.github/workflows/lean_action_ci.yml` - elanバージョン固定
3. `.github/workflows/update-dependencies.yml` - 両ファイル更新対応
4. `.github/dependabot.yml` - 削除
5. `CLAUDE.md` - 依存関係管理の説明更新（必要に応じて）

## 検証方法

1. **ローカルDockerビルド確認**
   ```bash
   docker build -t ziku-test .
   docker run --rm ziku-test
   ```

2. **GitHub Actions確認**
   - PRを作成してCIが通ることを確認
   - lean_action_ci.ymlとdocker-ci.ymlの両方が成功すること

3. **Elan更新ワークフローの手動実行**
   - Actions → Update Dependencies → Run workflow
   - 正常に実行されることを確認（PRが作成されなくてもOK）

4. **Renovateの動作確認**
   - 既存のPRが影響を受けていないこと
   - dependabot.yml削除後もRenovateが動作すること

## リスクと軽減策

1. **Elanリリースページのフォーマット変更**
   - 軽減: GitHub APIを使用しているため安定
   - 対策: 更新失敗時はPRを作成しない

2. **Dependabot削除の影響**
   - 軽減: Renovateで同等機能をカバー済み
   - 対策: 段階的に削除（まずdependabotを無効化→動作確認→削除）

## 優先度

このissueの優先度は「中」です。現状でも基本的な依存関係管理は機能していますが、elanのピン留めはサプライチェーンセキュリティの観点から対応すべきです。
