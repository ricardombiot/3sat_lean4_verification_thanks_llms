#!/usr/bin/env bash
# Copia un módulo de lean_project a lean/improves_bin cambiando el namespace, y lo compila.
#   scripts/migrate.sh GraphPath/Model/Pruned
set -e
HERE="$(cd "$(dirname "$0")/.." && pwd)"
SRC="$HERE/../../lean_project/AbsSat/$1.lean"
DST="$HERE/AbsSatBin/$1.lean"
mkdir -p "$(dirname "$DST")"
sed -e 's/AbsSat\./AbsSatBin./g' -e 's|^-- lean_project/AbsSat/|-- lean/improves_bin/AbsSatBin/|' "$SRC" > "$DST"
echo "copiado $1 (lean_project@$(git -C "$HERE/../.." log -1 --format=%h -- lean_project))"
# Transformaciones mecánicas comunes (el resto se revisa a mano):
#   * `variable (reqOf …)` recibe también `(forb : PathNodeId → Bool)`;
#   * `Reachable reqOf g` pasa a `Reachable reqOf forb g`.
python3 - "$DST" <<'PY'
import re, sys
p = sys.argv[1]
s = open(p).read()
s = s.replace("variable (reqOf : NodeId → List NodeId)\n",
              "variable (reqOf : NodeId → List NodeId) (forb : PathNodeId → Bool)\n")
s = re.sub(r"Reachable reqOf (?!forb)", "Reachable reqOf forb ", s)
open(p, "w").write(s)
PY
