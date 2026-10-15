#!/usr/bin/env bash
set -euo pipefail
NT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
export ELAN_HOME="$NT_ROOT/.tools/elan"
export PATH="$ELAN_HOME/bin:$PATH"
cd "$NT_ROOT"
exec "$@"
