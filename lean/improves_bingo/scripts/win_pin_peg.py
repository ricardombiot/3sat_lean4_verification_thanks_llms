#!/usr/bin/env python3
"""¿Tiene todo trío Helly-fallido un paso λ con `Peg` (ForbidOnGluePeg.lean)?

    python3 scripts/win_pin_peg.py [--tope=N] f.cnf ...

Recorre las familias de ventanas previas como `win_pin_h2all.py`. Para cada trío Helly-fallido busca un paso λ fuera
de los suyos con `Peg`: el corte son las variables constantes en P (`KF`, que cumple `hfix` por definición) y las que
lee la ventana de λ; las regiones son las componentes del grafo primal sin el corte;
  no3  ninguna región toca lo que leen los tres nodos;
  two  si una región toca lo de dos nodos, las variables de λ fuera de KF vecinas de la región las lee uno de ellos.
`Peg_libre` es la extensión con regiones libres: se ignoran las regiones cuyas variables solo están en cláusulas
tautológicas (o en ninguna), donde el pegado puede tomar el valor común de los nodos.

Por fórmula: casos, tríos Helly-fallidos, con λ y `Peg`, con λ y `Peg_libre`.
"""
import sys
from itertools import product, combinations

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from helly_formula import parse, Map  # noqa: E402
from win_pin_formula import ram_guard  # noqa: E402
from win_pin_rule import node_vars  # noqa: E402


def check(path, cap):
    n, clauses = parse(path)
    M = Map(n, clauses)
    C = M.count
    asg, sols, pids = [], [], []
    for a in product((False, True), repeat=n):
        s = [M.sel(a, k) for k in range(C)]
        p = [(s[k], s[k - 1] if k > 0 else None, s[k - 2] if k > 1 else None) for k in range(C)]
        if any(M.is_l3(k) and p[k] == (0, 0, 0) for k in range(C)):
            continue
        asg.append(a); sols.append(s); pids.append(p)
    taut = [any(v == v2 and p1 != p2 for v, p1 in c for v2, p2 in c) for c in clauses]
    free = [all(taut[ci] for ci, c in enumerate(clauses) if any(v == z for v, _ in c)) for z in range(n)]
    reads = [node_vars(M, k) for k in range(C)]
    st = {"familias": 0, "casos": 0, "tríos": 0, "peg": 0, "peg_libre": 0}
    first = [None]
    seen = set()

    def comps(K):
        par = {z: z for z in range(n) if z not in K}

        def f(z):
            while par[z] != z:
                par[z] = par[par[z]]
                z = par[z]
            return z
        for c in clauses:
            vs = [v for v, _ in c if v not in K]
            for a_, b_ in zip(vs, vs[1:]):
                ra, rb = f(a_), f(b_)
                if ra != rb:
                    par[ra] = rb
        return {z: f(z) for z in par}

    def peg_ok(nodes, lam, KF, with_free):
        S = reads[lam]
        K = KF | S
        cm = comps(K)
        touch = {}
        for i, (stp, _) in enumerate(nodes):
            for z in reads[stp]:
                if z not in K:
                    touch.setdefault(cm[z], set()).add(i)
        region_free = {}
        for z, r in cm.items():
            region_free[r] = region_free.get(r, True) and free[z]
        for r, who in touch.items():
            if with_free and region_free[r]:
                continue
            if len(who) == 3:
                return False
            if len(who) == 2:
                i1, i2 = sorted(who)
                ok_vars = reads[nodes[i1][0]] | reads[nodes[i2][0]]
                for c in clauses:
                    if not any(v not in K and cm[v] == r for v, _ in c):
                        continue
                    for v, _ in c:
                        if v in S and v not in KF and v not in ok_vars:
                            return False
        return True

    def case(F, j, v, m0):
        k = M.mid + 1 + 3 * j + 2
        steps = (k - 2, k - 1, k)
        P = [a for a in F if all(sols[a][t] == x for t, x in zip(steps, v))]
        if len(P) == len(F):
            return
        mP = {}
        for a in P:
            bit = 1 << a
            for l in range(C):
                key = (l, pids[a][l])
                mP[key] = mP.get(key, 0) | bit
        inP = set(P)
        KF = {z for z in range(n) if len({asg[a][z] for a in P}) == 1}

        def pm(*ns):
            r = -1
            for x in ns:
                r &= mP.get(x, 0)
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
        for t in tris:
            st["tríos"] += 1
            stp = {y[0] for y in t}
            lams = [l for l in range(C) if l not in stp]
            a1 = any(peg_ok(t, l, KF, False) for l in lams)
            a2 = a1 or any(peg_ok(t, l, KF, True) for l in lams)
            st["peg"] += a1
            st["peg_libre"] += a2
            if not a2 and first[0] is None:
                first[0] = (j, v, t)

    stack = [frozenset(range(len(sols)))]
    while stack and st["familias"] < cap:
        F = stack.pop()
        if F in seen or not F:
            continue
        seen.add(F)
        st["familias"] += 1
        ram_guard()
        for j in range(len(clauses)):
            k = M.mid + 1 + 3 * j + 2
            steps = (k - 2, k - 1, k)
            for v in {tuple(sols[a][t] for t in steps) for a in F}:
                st["casos"] += 1
                case(F, j, v, None)
                F2 = frozenset(a for a in F if all(sols[a][t] == x for t, x in zip(steps, v)))
                if F2 not in seen:
                    stack.append(F2)
    name = path.split("/")[-1]
    print(f"{name}\tvars={n}\tcláusulas={len(clauses)}\tsoluciones={len(sols)}\t" +
          "\t".join(f"{a}={b}" for a, b in st.items()) + ("\tcompleto" if not stack else "\tcortado_por_tope"))
    if first[0] is not None:
        print("   primer trío sin λ (cláusula, ventana, nodos):", first[0])


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
