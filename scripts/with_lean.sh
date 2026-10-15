#!/usr/bin/env bash
set -euo pipefail
SAM_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
export ELAN_HOME="$SAM_ROOT/.tools/elan"
export PATH="$ELAN_HOME/bin:$PATH"
cd "$SAM_ROOT"
exec "$@"
