#!/usr/bin/env python3
"""El descenso por caras: ¿a qué nivel muere cada trío fantasma de una ventana?

    python3 scripts/win_pin_descent.py [--orden=cadena|inversa] [--max=K] f.cnf ...

Para la ventana entera (P0 = soluciones con las ventanas anteriores, P = además la ventana, σ = el paso de su nodo de
ventana), los tríos fantasma de la estructura cerrada con testigos solo en σ (`win_pin_formula.phantom`). Un trío
`t = (x, u, w)` sin rama de P **muere al nivel k** si hay un paso λ fuera de los suyos tal que para todo nodo s de λ
alcanzable por ramas de P desde cada uno de los tres (`NodeProj`), alguna cara `(y, z, s)` no tiene rama de P y,
o no es un trío de P0, o muere al nivel k - 1. Nivel 1 = H2 (`ForbidOnTwoWitness.lean`): ningún s alcanzable.

Es la hipótesis de una prueba por inducción sobre el nivel (cada trío de la estructura con nivel finito es de P), con
un λ distinto por trío. Por fórmula: tríos fantasma y su nivel (1, 2, …, K, o «>K»).
"""
import sys
from itertools import product

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from helly_formula import parse, Map  # noqa: E402
from win_pin_formula import phantom, ram_guard  # noqa: E402


def check(path, order, K):
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
    clist = list(range(len(clauses)))
    if order == "inversa":
        clist.reverse()
    hist = {}

    def go(F, idx):
        if idx == len(clist):
            return
        j = clist[idx]
        k = M.mid + 1 + 3 * j + 2
        steps = (k - 2, k - 1, k)
        for v in sorted({tuple(sols[a][t] for t in steps) for a in F}):
            P0 = sorted(F)
            P = [a for a in P0 if all(sols[a][t] == x for t, x in zip(steps, v))]
            Vs, Rs, Gs, key_of = phantom(pids, P0, P, C, k, [k], ret=True)
            if Gs:
                ram_guard()
                mP, m0, at = {}, {}, {}
                for a in P0:
                    bit = 1 << a
                    for l in range(C):
                        key = (l, pids[a][l])
                        m0[key] = m0.get(key, 0) | bit
                for a in P:
                    bit = 1 << a
                    for l in range(C):
                        key = (l, pids[a][l])
                        mP[key] = mP.get(key, 0) | bit
                for key in mP:
                    at.setdefault(key[0], []).append(key)
                memo = {}

                def p_of(*ns):
                    m = -1
                    for x in ns:
                        m &= mP.get(x, 0)
                    return m != 0

                def p0_of(*ns):
                    m = -1
                    for x in ns:
                        m &= m0.get(x, 0)
                    return m != 0

                def kill(t, lev):
                    if lev <= 0:
                        return False
                    key = (t, lev)
                    if key in memo:
                        return memo[key]
                    memo[key] = False                 # contra ciclos
                    x, u, w = t
                    st = {x[0], u[0], w[0]}
                    res = False
                    for lam in range(C):
                        if lam in st:
                            continue
                        ok = True
                        for s in at.get(lam, ()):
                            if not (p_of(x, s) and p_of(u, s) and p_of(w, s)):
                                continue
                            dead_face = False
                            for (y, z) in ((x, u), (x, w), (u, w)):
                                if p_of(y, z, s):
                                    continue
                                f = tuple(sorted((y, z, s)))
                                if not p0_of(y, z, s) or kill(f, lev - 1):
                                    dead_face = True
                                    break
                            if not dead_face:
                                ok = False
                                break
                        if ok:
                            res = True
                            break
                    memo[key] = res
                    return res

                for t in Gs:
                    tt = tuple(sorted(key_of[i] for i in t))
                    lvl = next((l for l in range(1, K + 1) if kill(tt, l)), None)
                    hist[lvl] = hist.get(lvl, 0) + 1
            go(frozenset(P), idx + 1)

    go(frozenset(range(len(sols))), 0)
    name = path.split("/")[-1]
    h = "\t".join(f"nivel{l}={hist.get(l, 0)}" for l in range(1, K + 1))
    print(f"{name}\torden={order}\ttríos={sum(hist.values())}\t{h}\tmás_de_{K}={hist.get(None, 0)}")


if __name__ == "__main__":
    order = "cadena"
    K = 4
    files = []
    for a in sys.argv[1:]:
        if a.startswith("--orden="):
            order = a.split("=", 1)[1]
        elif a.startswith("--max="):
            K = int(a.split("=", 1)[1])
        else:
            files.append(a)
    for p in files:
        check(p, order, K)
