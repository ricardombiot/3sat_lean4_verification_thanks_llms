#!/bin/bash
# Lanza un comando con tope de memoria y de tiempo (29-sept-2026, rama row-tags).
#
#   test_3sat/run_capped.sh <tope_MB> <tope_segundos> <comando…>
#
# macOS no respeta `ulimit -v`, y la memoria comprimida no sale en el RSS: en el v197 `clause_mix_sep` llegó a
# 88,7 GB de huella con 6,9 GB residentes. Por eso se vigila la huella física (`footprint`, lo que cuenta el
# sistema, comprimida incluida) cada segundo, y se mata el grupo de procesos entero si pasa el tope.
# Al terminar escribe una línea «run_capped: …» con la huella máxima vista y el motivo de salida.
# Código de salida: el del comando, 137 si se mató por memoria, 124 si se mató por tiempo.

set -u
CAP_MB=$1; CAP_S=$2; shift 2

footprint_mb() {
    # «… Footprint: 123 MB (…)» o «… KB» o «… GB»
    footprint -p "$1" 2>/dev/null | awk '/Footprint:/ {
        for (i = 1; i <= NF; i++) if ($i == "Footprint:") { v = $(i+1); u = $(i+2) }
        if (u == "KB") v = v / 1024; else if (u == "GB") v = v * 1024; else if (u == "B") v = v / 1048576
        printf "%d", v; exit }'
}

"$@" &
PID=$!
# Se mata el proceso y sus hijos por pid (no por grupo: si el grupo fuera el del shell que llama, lo mataría también).
kill_tree() { pkill -9 -P "$1" 2>/dev/null; kill -9 "$1" 2>/dev/null; }
PEAK=0; START=$(date +%s); REASON=exit

while kill -0 "$PID" 2>/dev/null; do
    MB=$(footprint_mb "$PID"); MB=${MB:-0}
    [ "$MB" -gt "$PEAK" ] && PEAK=$MB
    if [ "$MB" -gt "$CAP_MB" ]; then
        REASON="memory ($MB MB > $CAP_MB MB)"; kill_tree "$PID"; break
    fi
    if [ $(( $(date +%s) - START )) -gt "$CAP_S" ]; then
        REASON="time (> $CAP_S s)"; kill_tree "$PID"; break
    fi
    sleep 1
done
wait "$PID" 2>/dev/null; CODE=$?
case "$REASON" in memory*) CODE=137 ;; time*) CODE=124 ;; esac
echo "run_capped: reason=$REASON peak_footprint_mb=$PEAK code=$CODE elapsed_s=$(( $(date +%s) - START ))" >&2
exit $CODE
