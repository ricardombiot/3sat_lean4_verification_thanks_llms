#!/usr/bin/env bash
# Regenera AbsSatBin.lean importando todos los módulos de AbsSatBin/.
cd "$(dirname "$0")/.."
{
  echo "-- lean/improves_bin/AbsSatBin.lean  (generado por scripts/gen_root.sh)"
  find AbsSatBin -name '*.lean' | sort | sed -e 's|\.lean$||' -e 's|/|.|g' -e 's|^|import |'
  cat <<'DOC'

/-! # `AbsSatBin` — the machine over the binary map

Lean mirror of `julia/improves_bin`: the `bin` map (three 2-node steps per clause, prohibited
window `(0,0,0)`) and the UP that skips it. Modules arrive from `lean_project` one at a time,
as the migration needs them; see `README.md` for the ledger of what came from where.
-/
DOC
} > AbsSatBin.lean
