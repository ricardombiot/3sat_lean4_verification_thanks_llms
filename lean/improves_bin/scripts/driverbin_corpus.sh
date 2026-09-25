#!/usr/bin/env bash
# Corre `driverbin-check` sobre cada fichero de una lista, en paralelo, con límite de tiempo.
#   scripts/driverbin_corpus.sh LISTA [SEGUNDOS=300] [PARALELO=6]
HERE="$(cd "$(dirname "$0")/.." && pwd)"
if [ "$1" = "--one-wrap" ]; then
  lim="$2"; f="$3"; out="$(mktemp)"
  "$HERE/.lake/build/bin/driverbin-check" "$f" > "$out" 2>&1 & p=$!
  ( sleep "$lim"; kill "$p" 2>/dev/null ) & w=$!
  wait "$p" 2>/dev/null; { kill "$w"; wait "$w"; } 2>/dev/null
  if [ -s "$out" ]; then head -1 "$out"; else printf '%s\tTIMEOUT\t>%ss\n' "$(basename "$f")" "$lim"; fi
  rm -f "$out"; exit 0
fi
LIST="$1"; LIM="${2:-300}"; PAR="${3:-6}"
xargs -P "$PAR" -n 1 "$0" --one-wrap "$LIM" < "$LIST"
