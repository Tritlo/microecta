#!/usr/bin/env bash
set -euo pipefail

repository_root="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
cd "$repository_root"

if [[ -z "${IN_NIX_SHELL:-}" ]]; then
  exec nix-shell --run './scripts/benchmark-generators.sh'
fi

cabal bench microcfta-generator:untyped-expression-speed --enable-optimization=2
