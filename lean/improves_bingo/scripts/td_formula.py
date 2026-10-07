#!/usr/bin/env python3
"""El acolchado por bolsas: gemelo de `tdCnf` (ForbidOnBagPad.lean).

    python3 scripts/td_formula.py entrada.cnf "1,2,3;1,4,2;2,5,3" salida.cnf

Las bolsas, en DIMACS (desde 1), separadas por «;», de tres variables cada una (se pueden repetir). Con `v` de Lean
desde 0: la real `v` pasa a `2v + 1` (DIMACS `2v + 2`), las pares son de relleno (DIMACS `x1` es `x₀`). Cláusulas en
bloques de tres: por bolsa `(a, b, c)`: `T, (a ∨ ¬a ∨ b), (c ∨ ¬c ∨ c)`; por cláusula `C`: `T, C', T`; y una `T`
final, con `T = (x₀ ∨ ¬x₀ ∨ x₀)`.
"""
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from helly_formula import parse  # noqa: E402


def td(n, clauses, bags):
    x = lambda v: 2 * v + 2          # DIMACS de la real v (desde 0)
    T = [1, -1, 1]
    out = []
    for (a, b, c) in bags:
        out += [T, [x(a), -x(a), x(b)], [x(c), -x(c), x(c)]]
    for cl in clauses:
        out += [T, [(x(v) if pos else -x(v)) for (v, pos) in cl], T]
    out.append(T)
    return 2 * n + 1, out


if __name__ == "__main__":
    src, bags_s, dst = sys.argv[1:4]
    n, clauses = parse(src)
    bags = [tuple(int(t) - 1 for t in b.split(",")) for b in bags_s.split(";")]
    N, out = td(n, clauses, bags)
    with open(dst, "w") as f:
        f.write(f"c acolchada por bolsas de {src.rsplit('/', 1)[-1]}: bolsas {bags_s}\n")
        f.write(f"p cnf {N} {len(out)}\n")
        for c in out:
            f.write(" ".join(map(str, c)) + " 0\n")
