#!/usr/bin/env bash
# Diferencial del mapa bin: CnfMapBin (Lean) contra GraphMapBin (Julia), sobre el corpus de
# julia/improves_bin/test_3sat/compare_bin.jl. Sale con 1 si algún volcado difiere.
#
#   lean/improves_bin/scripts/diff_map_bin.sh [OUTDIR]
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
JL="$HERE/../../julia/improves_bin"
OUT="${1:-$HERE/.lake/diff_map_bin}"
rm -rf "$OUT"; mkdir -p "$OUT/lean" "$OUT/julia"

FILES=()
for d in "$JL/test/example_cnf" "$JL/test_window/instances" "$JL/test_window/instances_bin"; do
  for f in "$d"/*.cnf; do FILES+=("$f"); done
done

(cd "$HERE" && lake build mapbin-dump >/dev/null && lake exe mapbin-dump "$OUT/lean" "${FILES[@]}")
(cd "$JL/test_3sat" && julia --project=.. dump_map_bin.jl "$OUT/julia" "${FILES[@]}" >/dev/null)

agree=0; differ=0; skipped=0
for f in "${FILES[@]}"; do
  n="$(basename "${f%.cnf}").txt"
  if grep -q '^SKIP' "$OUT/julia/$n" || grep -q '^SKIP' "$OUT/lean/$n"; then
    skipped=$((skipped+1)); echo "SKIP  $n  (lean: $(head -1 "$OUT/lean/$n" | cut -c1-40); julia: $(head -1 "$OUT/julia/$n" | cut -c1-60))"
  elif diff -q <(sort "$OUT/lean/$n") <(sort "$OUT/julia/$n") >/dev/null; then
    agree=$((agree+1))
  else
    differ=$((differ+1)); echo "DIFF  $n"
    diff <(sort "$OUT/lean/$n") <(sort "$OUT/julia/$n") | head -10 || true
  fi
done
echo "iguales=$agree distintos=$differ saltados=$skipped (de ${#FILES[@]})"
[ "$differ" -eq 0 ]
