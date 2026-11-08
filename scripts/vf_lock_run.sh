#!/usr/bin/env bash
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [ -f "$REPO_ROOT/config.sh" ]; then
  . "$REPO_ROOT/config.sh"
fi
VFDEPS="/tmp/${VFDEPS_NAME:-vfdeps-adf88dc}"
CARGO_PATHS="$HOME/.cargo/bin"
if [ -d "/home/devin/.cargo/bin" ] && [ "$HOME/.cargo/bin" != "/home/devin/.cargo/bin" ]; then
  CARGO_PATHS="$CARGO_PATHS:/home/devin/.cargo/bin"
fi
export PATH="$CARGO_PATHS:$VFDEPS/bin:$REPO_ROOT/bin:$PATH"
export CAPNP_INCLUDE="$VFDEPS/include"
export Z3_DLL_DIR="$VFDEPS/lib"
exec flock -w 300 /tmp/vf_dune_build.lock "$@"
