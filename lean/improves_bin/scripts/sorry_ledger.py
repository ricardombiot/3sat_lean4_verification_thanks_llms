#!/usr/bin/env python3
"""Deuda de demostraciones: `sorry` en código (fuera de comentarios y docstrings), por módulo."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "AbsSatBin"
total = 0
for path in sorted(ROOT.rglob("*.lean")):
    text = re.sub(r"/-.*?-/", "", path.read_text(), flags=re.S)  # block comments / docstrings
    code = "\n".join(l.split("--", 1)[0] for l in text.splitlines())
    n = len(re.findall(r"\bsorry\b", code))
    if n:
        print(f"{n:4d}  {path.relative_to(ROOT)}")
        total += n
print(f"sorry pendientes: {total}")
