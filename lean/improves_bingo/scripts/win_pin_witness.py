#!/usr/bin/env python3
"""Cuántos pasos de testigo hacen falta para `WinPinFree` con la ventana entera.

    python3 scripts/win_pin_witness.py [--orden=cadena|inversa] f1.cnf ...

Como `win_pin_formula.py --helly`, pero solo con la ventana entera: P0 = las soluciones con las ventanas anteriores,
P = además la ventana nueva, σ = el paso de su nodo de ventana. Para cada ventana se calcula la mayor estructura
cerrada exigiendo testigos solo en un conjunto `L` de pasos (`σ ∈ L`), y se busca el `L` más pequeño que no deja
fantasmas: primero `{σ}`, después `{σ, l}` para cada `l`, después `{σ, l, l'}`.

Por fórmula: ventanas, cuántas necesitan 0, 1, 2 o más pasos además de σ, y para cada ventana que necesita alguno,
los pasos que bastan (la lista de todos los `l` que bastan solos, o el primer par), descritos por lo que leen.
"""
import sys
from itertools import product, combinations

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from helly_formula import parse, Map  # noqa: E402
from win_pin_formula import phantom  # noqa: E402


def describe(M, l):
    if l == 0:
        return "raíz"
    if l < M.mid:
        v = (l - 1) // 2
        return f"x{v + 1}" if l % 2 == 1 else f"¬x{v + 1}"
    if l == M.mid:
        return "fusión"
    if l >= M.top:
        return "final"
    o = l - M.mid - 1
    v, pos = M.cl[o // 3][o % 3]
    return f"c{o // 3}.{o % 3}({'' if pos else '¬'}x{v + 1})"


def check(path, order):
    n, clauses = parse(path)
    M = Map(n, clauses)
    C = M.count
    sols, pids = [], []
    for a in product((False, True), repeat=n):
        s = [M.sel(a, k) for k in range(C)]
        p = [(s[k], s[k - 1] if k > 0 else None, s[k - 2] if k > 1 else None) for k in range(C)]
        if any(M.is_l3(k) and p[k] == (0, 0, 0) for k in range(C)):
            continue
        sols.append(s); pids.append(p)
    name = path.split("/")[-1]
    clist = list(range(len(clauses)))
    if order == "inversa":
        clist.reverse()
    hist = {}
    examples = []
    total = [0]

    def need(P0, P, k):
        if phantom(pids, P0, P, C, k, [k]) == 0:
            return 0, []
        ok1 = [l for l in range(C) if l != k and phantom(pids, P0, P, C, k, [k, l]) == 0]
        if ok1:
            return 1, ok1
        for l, l2 in combinations([l for l in range(C) if l != k], 2):
            if phantom(pids, P0, P, C, k, [k, l, l2]) == 0:
                return 2, [(l, l2)]
        return 3, []

    def go(F, idx):
        if idx == len(clist):
            return
        j = clist[idx]
        k = M.mid + 1 + 3 * j + 2
        steps = (k - 2, k - 1, k)
        for v in sorted({tuple(sols[a][st] for st in steps) for a in F}):
            total[0] += 1
            P0 = sorted(F)
            P = [a for a in P0 if all(sols[a][st] == x for st, x in zip(steps, v))]
            d, ls = need(P0, P, k)
            hist[d] = hist.get(d, 0) + 1
            if d and len(examples) < 6:
                if d == 1:
                    examples.append((j, v, d, [describe(M, l) for l in ls]))
                else:
                    examples.append((j, v, d, [tuple(describe(M, x) for x in pr) for pr in ls]))
            go(frozenset(P), idx + 1)

    go(frozenset(range(len(sols))), 0)
    h = "\t".join(f"extra{d}={hist.get(d, 0)}" for d in range(4))
    print(f"{name}\torden={order}\tventanas={total[0]}\t{h}")
    for j, v, d, ls in examples:
        print(f"   cláusula {j} {clauses[j]} ventana {v}: {d} paso(s) más; bastan: {ls}")


if __name__ == "__main__":
    order = "cadena"
    files = []
    for a in sys.argv[1:]:
        if a.startswith("--orden="):
            order = a.split("=", 1)[1]
        else:
            files.append(a)
    for p in files:
        check(p, order)
