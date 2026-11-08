#!/usr/bin/env bash
set -euo pipefail
export PATH="/home/devin/.cargo/bin:/tmp/vfdeps-adf88dc/bin:/home/devin/verifast-src/bin:$PATH"
export CAPNP_INCLUDE="/tmp/vfdeps-adf88dc/include"
export Z3_DLL_DIR="/tmp/vfdeps-adf88dc/lib"
exec flock -w 300 /tmp/vf_dune_build.lock "$@"
