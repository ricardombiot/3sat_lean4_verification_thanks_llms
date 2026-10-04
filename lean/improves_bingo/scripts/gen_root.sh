#!/usr/bin/env bash
# Regenera AbsSatBingo.lean con todos los módulos de AbsSatBingo/.
set -euo pipefail
cd "$(dirname "$0")/.."
{
  echo "-- lean/improves_bingo/AbsSatBingo.lean  (generado por scripts/gen_root.sh)"
  find AbsSatBingo -name '*.lean' | sort | sed 's#/#.#g; s#\.lean$##; s#^#import #'
} > AbsSatBingo.lean
