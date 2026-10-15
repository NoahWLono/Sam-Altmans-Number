#!/usr/bin/env bash
set -euo pipefail
SAM_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
export ELAN_HOME="$SAM_ROOT/.tools/elan"
export PATH="$ELAN_HOME/bin:$PATH"
mkdir -p "$SAM_ROOT/.tools"
if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  curl --fail --location --silent --show-error https://elan.lean-lang.org/elan-init.sh -o "$SAM_ROOT/.tools/elan-init.sh"
  sh "$SAM_ROOT/.tools/elan-init.sh" -y --no-modify-path --default-toolchain none
fi
cd "$SAM_ROOT"
lake exe cache get
python3 research/sam-altman-number/verify.py
