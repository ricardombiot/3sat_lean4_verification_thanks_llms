#!/usr/bin/env python3
"""El acolchado: una fórmula equivalente cuyo mapa lee siempre dentro de un bloque, salvo variables libres.

    python3 scripts/pad_formula.py entrada.cnf salida.cnf

* Variables: d0, x1, d1, x2, …, xn, dn (una de relleno antes de cada variable real y otra al final). Las de relleno no
  están en ninguna cláusula real.
* Cláusulas: T(d0), C1, T(d1), C2, …, Cm, T(dm), con T(d) = (d ∨ ¬d ∨ d) tautológica (si hay menos variables de
  relleno que huecos, se reutiliza la última).

Con esto la ventana de tres pasos de cualquier nodo lee, fuera de las variables de relleno, una sola variable real o
variables de una sola cláusula real: el nodo de x_i lee {x_i, d_{i-1}}, el de la copia l1 de C_j lee {l1, d, d}, el de
la l1 de T(d_j) lee {d_j} y el final de C_j. Las soluciones son las de la fórmula original por cualquier valor de las
variables de relleno.
"""
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from helly_formula import parse  # noqa: E402


def pad(n, clauses):
    # nuevo índice (base 0): d_i = 2i, x_i (real i, base 0) = 2i + 1; d_n = 2n
    dv = lambda i: 2 * i
    xv = lambda i: 2 * i + 1
    N = 2 * n + 1
    out = []
    for j, c in enumerate(clauses):
        d = dv(min(j, n))
        out.append([(d, True), (d, False), (d, True)])
        out.append([(xv(v), pos) for v, pos in c])
    d = dv(min(len(clauses), n))
    out.append([(d, True), (d, False), (d, True)])
    return N, out


def write(path, n, clauses, comment):
    with open(path, "w") as f:
        f.write(f"c {comment}\n")
        f.write(f"p cnf {n} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(str((v + 1) if pos else -(v + 1)) for v, pos in c) + " 0\n")


if __name__ == "__main__":
    n, cl = parse(sys.argv[1])
    N, pc = pad(n, cl)
    write(sys.argv[2], N, pc, f"acolchada de {sys.argv[1].split('/')[-1]}")
