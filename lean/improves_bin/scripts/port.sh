#!/usr/bin/env bash
# Migra módulos en orden: copia (migrate.sh, salvo --no-copy), hila forb (thread_forb.py) e
# inserta los forb que pide el compilador (fix_forb.py). Lo que quede es trabajo a mano.
#   scripts/port.sh [--no-copy] GraphPath/Model/A GraphPath/Model/B …
cd "$(dirname "$0")/.."
copy=1; [ "$1" = "--no-copy" ] && { copy=0; shift; }
for m in "$@"; do
  [ $copy = 1 ] && ./scripts/migrate.sh "$m" >/dev/null
  ./scripts/gen_root.sh
  ./scripts/thread_forb.py "$m"
  ./scripts/fix_forb.py "$m"
  n=$(lake build "AbsSatBin.${m//\//.}" 2>&1 | grep -c '^error: AbsSatBin')
  echo "  → $m: $n error(es) restantes; $(./scripts/index_lint.py | tail -1)"
done
