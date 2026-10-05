#!/usr/bin/env python3
"""H2′ (`ForbidOnTwoWitness.TwoWitnessF`) tal cual, con todas las listas previas de ventanas.

    python3 scripts/win_pin_h2all.py [--tope=N] f.cnf ...

La familia de antes depende solo de qué ventanas se fijaron y con qué valores (no del orden): se recorren todas las
familias alcanzables fijando ventanas (cada ventana: los tres valores de copia de una cláusula, tomados de alguna
solución de la familia). Para cada familia P0 y cada ventana nueva (cláusula j, valores v), con P = P0 ∧ ventana:

  tríos Helly-fallidos  tres nodos distintos con una rama de P0 por los tres, una de P por cada pareja y ninguna de P
                        por los tres (todos, no solo los que sobreviven al cierre con el testigo en σ);
  H2′                   para cada uno, un paso λ fuera de los suyos tal que todo nodo s de λ alcanzable por ramas de P
                        desde los tres deja alguna cara (y, z, s) sin rama de P0.

Por fórmula: familias, casos (familia, ventana), tríos Helly-fallidos, cuántos cumplen H2′ y el primer fallo.
"""
import sys
from itertools import product, combinations

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from helly_formula import parse, Map  # noqa: E402
from win_pin_formula import ram_guard  # noqa: E402


def check(path, cap):
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
    st = {"familias": 0, "casos": 0, "tríos": 0, "h2ok": 0}
    first = [None]
    seen = set()
    done_case = set()

    def masks(F):
        m = {}
        at = {}
        for a in F:
            bit = 1 << a
            for l in range(C):
                key = (l, pids[a][l])
                m[key] = m.get(key, 0) | bit
        for key in m:
            at.setdefault(key[0], []).append(key)
        return m, at

    def case(F, j, v, m0):
        k = M.mid + 1 + 3 * j + 2
        steps = (k - 2, k - 1, k)
        P = [a for a in F if all(sols[a][t] == x for t, x in zip(steps, v))]
        if len(P) == len(F):
            return
        mP, atP = masks(P)
        inP = set(P)

        def pm(*ns):
            r = -1
            for x in ns:
                r &= mP.get(x, 0)
            return r != 0

        def p0m(*ns):
            r = -1
            for x in ns:
                r &= m0.get(x, 0)
            return r != 0

        tris = set()
        for a0 in F:
            if a0 in inP:
                continue
            ns = [(l, pids[a0][l]) for l in range(C) if mP.get((l, pids[a0][l]), 0)]
            for x, u in combinations(ns, 2):
                if not pm(x, u):
                    continue
                for w in ns:
                    if w <= u or w == x:
                        continue
                    if pm(x, w) and pm(u, w) and not pm(x, u, w):
                        tris.add((x, u, w))
        for (x, u, w) in tris:
            st["tríos"] += 1
            stp = {x[0], u[0], w[0]}
            ok = False
            for lam in range(C):
                if lam in stp:
                    continue
                good = True
                for s in atP.get(lam, ()):
                    if not (pm(x, s) and pm(u, s) and pm(w, s)):
                        continue
                    if p0m(x, u, s) and p0m(x, w, s) and p0m(u, w, s):
                        good = False
                        break
                if good:
                    ok = True
                    break
            if ok:
                st["h2ok"] += 1
            elif first[0] is None:
                first[0] = (j, v, (x, u, w), len(F))

    stack = [frozenset(range(len(sols)))]
    while stack and st["familias"] < cap:
        F = stack.pop()
        if F in seen or not F:
            continue
        seen.add(F)
        st["familias"] += 1
        ram_guard()
        m0, _ = masks(F)
        for j in range(len(clauses)):
            k = M.mid + 1 + 3 * j + 2
            steps = (k - 2, k - 1, k)
            for v in {tuple(sols[a][t] for t in steps) for a in F}:
                st["casos"] += 1
                case(F, j, v, m0)
                F2 = frozenset(a for a in F if all(sols[a][t] == x for t, x in zip(steps, v)))
                if F2 not in seen:
                    stack.append(F2)
    name = path.split("/")[-1]
    print(f"{name}\t" + "\t".join(f"{a}={b}" for a, b in st.items()) +
          ("\tcompleto" if not stack else "\tcortado_por_tope"))
    if first[0] is not None:
        print("   primer fallo de H2′ (cláusula, ventana, trío, |P0|):", first[0])


if __name__ == "__main__":
    cap = 10 ** 9
    files = []
    for a in sys.argv[1:]:
        if a.startswith("--tope="):
            cap = int(a.split("=", 1)[1])
        else:
            files.append(a)
    for p in files:
        check(p, cap)
