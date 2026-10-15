#!/usr/bin/env bash
set -euo pipefail
NT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
export ELAN_HOME="$NT_ROOT/.tools/elan"
export PATH="$ELAN_HOME/bin:$PATH"
mkdir -p "$NT_ROOT/.tools"
if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  curl --fail --location --silent --show-error https://elan.lean-lang.org/elan-init.sh -o "$NT_ROOT/.tools/elan-init.sh"
  sh "$NT_ROOT/.tools/elan-init.sh" -y --no-modify-path --default-toolchain none
fi
cd "$NT_ROOT"
lake exe cache get
python3 research/sam-altman-number/verify.py
