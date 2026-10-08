#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p results
lake build 2>&1 | tee results/build.log
lake test 2>&1 | tee results/tests.log
lake env lean Tests/Trust.lean | tee results/trust.log
python3 scripts/audit.py results/trust.log
julia --startup-file=no scripts/upstream_fixtures.jl | tee results/julia-fixtures.log
python3 scripts/source_hashes.py
