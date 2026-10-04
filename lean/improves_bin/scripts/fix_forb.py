#!/usr/bin/env python3
"""Inserta `forb` donde el compilador dice que falta.

Tras `migrate.sh`, muchas llamadas `X reqOf g …` fallan porque `X` ahora recibe
`(forb : PathNodeId → Bool)` después de `reqOf`. Qué lemas lo reciben lo sabe el entorno de
Lean, no un regex, así que este script compila el módulo y, en cada error
«Application type mismatch … expected to have type PathNodeId → Bool», inserta `forb ` en la
línea y columna exactas del argumento. Repite hasta que no quede ninguno de esos errores.

Solo toca ese error concreto; todo lo demás se revisa a mano.

Uso:  scripts/fix_forb.py GraphPath/Model/Candidates
"""
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent


def build(mod: str) -> str:
    r = subprocess.run(["lake", "build", "AbsSatBin." + mod.replace("/", ".")],
                       cwd=HERE, capture_output=True, text=True)
    return r.stdout + r.stderr


def main() -> int:
    mod = sys.argv[1]
    path = HERE / "AbsSatBin" / (mod + ".lean")
    total = 0
    for _ in range(50):
        out = build(mod)
        spots = []
        rel = "AbsSatBin/" + mod + ".lean"
        # exactly: "The argument\n  X\nhas type\n  T\nbut is expected to have type\n  PathNodeId → Bool"
        pat = (r"error: " + re.escape(rel) + r":(\d+):(\d+): Application type mismatch: The argument\n"
               r"  [^\n]*\nhas type\n  [^\n]*\n(?:of sort `[^`]*` )?but is expected to have type\n  PathNodeId → Bool\n")
        for m in re.finditer(pat, out):
            spots.append((int(m.group(1)), int(m.group(2))))
        if not spots:
            break
        lines = path.read_text().split("\n")
        # right-to-left within a line so earlier columns stay valid
        for ln, col in sorted(set(spots), reverse=True):
            line = lines[ln - 1]
            lines[ln - 1] = line[:col] + "forb " + line[col:]
            total += 1
        path.write_text("\n".join(lines))
    print(f"fix_forb {mod}: {total} inserción(es)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
