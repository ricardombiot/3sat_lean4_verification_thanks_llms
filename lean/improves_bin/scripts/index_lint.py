#!/usr/bin/env python3
"""Lint de índices de lean/improves_bin.

Evita que el código copiado de lean_project traiga la aritmética del mapa clásico.

Reglas:
  1. Nombres del mapa clásico: no deben aparecer (litBlock, reqOfCnf, clauseAt, b1/b2/b3, Lit.step…),
     salvo en una línea que cite su origen (`lean_project`, «classic», «clásico»).
     El compilador ya los rechaza si se usan; el lint también los caza en comentarios y en
     cadenas, que el compilador no mira.
  2. Aritmética de pasos del mapa: fuera de CnfMapBin (la única fuente), toda línea de código que
     haga aritmética con literales sobre un paso (`.step`, `step :=`, `2 *`, `% 2`, `% 3`, `/ 3`) o
     use el literal `7` como índice debe llevar `-- idx: <motivo>` en esa línea o en la anterior.
  3. `current_step ± k` es aritmética de filas del gpath, no del mapa: se admite sin anotación,
     porque lo que une las dos es la hipótesis explícita `d.step = g.current_step`.

Uso:  scripts/index_lint.py            (sale con 1 si hay hallazgos)
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "AbsSatBin"
SOURCE = {"GraphMap/CnfMapBin.lean", "Cnf/Formula.lean", "GraphMap/CnfSelBin.lean"}  # las únicas fuentes de aritmética del mapa
# Una mención histórica de un nombre clásico se admite si la línea cita su origen.
HISTORY = re.compile(r"lean_project|classic|clásic")

LEGACY = [
    r"\blitBlock\b", r"\breqOfCnf\b", r"\bclauseAt\b", r"\bb[123]\s*\(", r"\bLit\.step\b",
    r"\bbits_not_all_zero\b", r"\bindex_range_of_clauseNode\b", r"\bmapSons\b",
    r"\bCnfMap\.", r"\bCnfSel\b", r"\browOf\b",
]
ARITH = [
    r"\.step\s*[-+]\s*\d", r"\d\s*[-+]\s*\w*\.step\b", r"[{,]\s*step\s*:=\s*[^,}]*[-+]\s*\d",
    r"\b2\s*\*", r"%\s*[23]\b", r"/\s*3\b", r"index\s*:=\s*7\b", r",\s*7\s*⟩",
]
PATH_ROW = re.compile(r"current_step\s*[-+]\s*\d")


def strip_comment(line: str) -> str:
    return line.split("--", 1)[0]


def main() -> int:
    findings = []
    for path in sorted(ROOT.rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        lines = path.read_text().splitlines()
        in_block = False
        for i, line in enumerate(lines):
            for pat in LEGACY:
                if re.search(pat, line) and not HISTORY.search(line):
                    findings.append(f"{rel}:{i+1}: nombre clásico `{re.search(pat, line).group(0)}`: {line.strip()}")
            # skip block comments / docstrings for rule 2
            if "/-" in line:
                in_block = True
            if in_block:
                if "-/" in line:
                    in_block = False
                continue
            if rel in SOURCE:
                continue
            code = strip_comment(line)
            code_wo_rows = PATH_ROW.sub("", code)
            if any(re.search(p, code_wo_rows) for p in ARITH):
                annotated = "-- idx:" in line or (i > 0 and "-- idx:" in lines[i - 1])
                if not annotated:
                    findings.append(f"{rel}:{i+1}: aritmética de pasos sin `-- idx:`: {line.strip()}")
    for f in findings:
        print(f)
    print(f"index_lint: {len(findings)} hallazgo(s)")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
