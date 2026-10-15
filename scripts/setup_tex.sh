#!/usr/bin/env bash
set -euo pipefail
NT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [[ "$(uname -s)-$(uname -m)" != "Linux-x86_64" ]]; then
  echo 'This installer supports Linux x86_64. Install Tectonic 0.17.0 for your platform.' >&2
  exit 1
fi
NT_TEX_DIR="$NT_ROOT/.tools/tectonic"
mkdir -p "$NT_TEX_DIR"
if [[ ! -x "$NT_TEX_DIR/tectonic" ]]; then
  curl --fail --location --silent --show-error \
    'https://github.com/tectonic-typesetting/tectonic/releases/download/tectonic%400.17.0/tectonic-0.17.0-x86_64-unknown-linux-musl.tar.gz' \
    -o "$NT_TEX_DIR/release.tar.gz"
  (cd "$NT_TEX_DIR" && echo '8533d07f9ccbd7a65824b9e0459041bca34af1eb33daba48f59215593753a3b7  release.tar.gz' | sha256sum --check)
  tar -xzf "$NT_TEX_DIR/release.tar.gz" -C "$NT_TEX_DIR" tectonic
fi
"$NT_TEX_DIR/tectonic" --version
