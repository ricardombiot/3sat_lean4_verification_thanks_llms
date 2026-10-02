#!/usr/bin/env python3
"""La condición de cuatro ramas `HellyAt` de ForbidOnHelly.lean, por fuerza bruta sobre la fórmula.

    python3 scripts/helly_formula.py f1.cnf f2.cnf ...

No ejecuta la máquina: enumera las 2^n asignaciones y comprueba, para cada línea T, cada nodo k del paso T - 1 y cada
hijo d suyo en el mapa bin, las dos condiciones de `HellyAt φ T`:

  filtro (HF)  P0 = SolE T k                       P = P0 con el requisito r de d      σ = r.step
  UP     (HU)  P0 = SolE T k con el requisito de d  P = SolE (T+1) d con sel (T-1) = k  σ = T

`Helly4 P0 P N σ` (N = T): una rama a0 de P0 por tres nodos de los pasos i, j, l < T y tres ramas de P que pasan cada
una por dos de ellos y las tres por un mismo nodo s del paso σ dan una rama de P por los tres nodos.

Espejo de las definiciones de Lean (`CnfMapBin`, `CnfSelBin`, `ForbidOnMaj`): `selOfAssign`, `pidOfAssign`,
`isProhibited`, `ValidUpTo`, `SolE`, `mapNodes`, `sonsOfMap`, `reqOf`.

Por línea de salida: fichero, variables, cláusulas, casos (T, k, d) comprobados, ramas a0 que no están ya en P,
hipótesis (pares de pasos con algún tercero candidato) y fallos, con su desglose por operación. Con fallos, el primero se imprime entero.

Donde `HellyAt` falla (o en todos los casos, con `--phantom-all`) se comprueba además `PhantomAt`, la condición de
todos los pasos (`PhantomFree P0 P N σ`, con N = T en el filtro y N = T + 1 en el UP): se calcula la mayor estructura
cerrada por la regla hecha de nodos, parejas y tríos de ramas de P0 (los nodos del paso σ, solo los que anclan en P) y
se cuentan sus elementos que no son de ninguna rama de P: los fantasmas. Los elementos de ramas de P forman una
estructura cerrada y nunca caen, así que solo se itera sobre los sospechosos (de P0 y no de P).
  casos_f   casos en los que se calculó la estructura
  fantasmas nodos + parejas + tríos fantasma (0 = `PhantomFree` se cumple en esos casos)
"""
import sys
from itertools import product, combinations


def parse(path):
    n = 0
    clauses = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("%") or line.startswith("0"):
            break
        tok = line.split()
        if len(tok) >= 3 and tok[1] == "cnf":
            n = int(tok[2])
            continue
        if len(tok) < 3:
            continue
        lits = []
        ok = True
        for t in tok[:3]:
            v = int(t)
            if v == 0 or abs(v) > n:
                ok = False
                break
            lits.append((abs(v) - 1, v > 0))
        if ok:
            clauses.append(lits)
    return n, clauses


class Map:
    def __init__(self, n, clauses):
        self.n, self.cl = n, clauses
        self.m = len(clauses)
        self.mid = 2 * n + 1
        self.top = 2 * n + 3 * self.m + 2
        self.count = 2 * n + 3 * self.m + 3

    def lit_step(self, lit):
        v, pos = lit
        return 2 * v + 1 + (0 if pos else 1)

    def sel(self, a, k):
        if k <= 0:
            return 0
        if k < self.mid:
            b = a[(k - 1) // 2]
            return int(b) if k % 2 == 1 else int(not b)
        if k == self.mid or k >= self.top:
            return 0
        o = k - self.mid - 1
        v, pos = self.cl[o // 3][o % 3]
        return int(a[v] if pos else not a[v])

    def is_l3(self, k):
        return self.mid < k < self.top and (k - self.mid - 1) % 3 == 2

    def map_nodes(self, k):
        if k < 0 or k >= self.count:
            return []
        if k == 0 or k == self.mid or k >= self.top:
            return [0]
        return [0, 1]

    def sons(self, s, i):
        if 0 < s < self.mid and s % 2 == 1:
            return [(s + 1, 1 - i)]
        return [(s + 1, j) for j in self.map_nodes(s + 1)]

    def req(self, s, i):
        if s <= 0:
            return []
        if s < self.mid:
            return [] if s % 2 == 1 else [(s - 1, 1 - i)]
        if s == self.mid or s >= self.top:
            return []
        o = s - self.mid - 1
        return [(self.lit_step(self.cl[o // 3][o % 3]), i)]


def check(path):
    n, clauses = parse(path)
    M = Map(n, clauses)
    C = M.count
    # por asignación: los nodos elegidos, las ventanas y el primer paso con ventana prohibida
    sels, pids, first = [], [], []
    for a in product((False, True), repeat=n):
        s = [M.sel(a, k) for k in range(C)]
        p = [(s[k], s[k - 1] if k > 0 else None, s[k - 2] if k > 1 else None) for k in range(C)]
        f = C
        for k in range(C):
            if M.is_l3(k) and p[k] == (0, 0, 0):
                f = k
                break
        sels.append(s); pids.append(p); first.append(f)
    A = range(len(sels))
    cases = outside = hyps = fails = 0
    by_op = {"filtro": 0, "UP": 0}
    example = None

    def helly(P0, P, T, sigma, tag):
        nonlocal outside, hyps, fails, example
        inP = set(P)
        by_s = {}
        for a in P:
            by_s.setdefault(pids[a][sigma], []).append(a)
        for a0 in P0:
            if a0 in inP:
                continue
            outside += 1
            p0 = pids[a0]
            mask = {}
            for a in P:
                m = 0
                pa = pids[a]
                for k in range(T):
                    if pa[k] == p0[k]:
                        m |= 1 << k
                mask[a] = m
            allm = set(mask.values())
            for s, group in by_s.items():
                gm = {mask[a] for a in group}
                nb = [0] * T                      # vecinos de i: pasos que comparte con i alguna rama por s
                for m in gm:
                    k = 0
                    mm = m
                    while mm:
                        if mm & 1:
                            nb[k] |= m
                        mm >>= 1
                        k += 1
                for i in range(T):
                    ni = nb[i] & ~(1 << i)
                    j = i + 1
                    rest = ni >> j
                    while rest:
                        if rest & 1:
                            cand = ni & nb[j] & ~(1 << i) & ~(1 << j)
                            if cand:
                                hyps += 1
                                cover = 0
                                bij = (1 << i) | (1 << j)
                                for m in allm:
                                    if m & bij == bij:
                                        cover |= m
                                bad = cand & ~cover
                                if bad:
                                    fails += 1
                                    by_op[tag] += 1
                                    if example is None:
                                        l = (bad & -bad).bit_length() - 1
                                        example = (tag, T, sigma, s, (i, p0[i]), (j, p0[j]), (l, p0[l]))
                        rest >>= 1
                        j += 1

    ph_cases = ph_total = 0

    def phantom(P0, P, N, sigma):
        """Elementos de la mayor estructura cerrada (pasos 0..N-1) que no son de ninguna rama de P."""
        inP = set(P)
        # nodos del paso σ que anclan: toda rama de P0 que pasa por ellos es de P
        thru = {}
        for a in P0:
            thru.setdefault(pids[a][sigma], []).append(a)
        anchor = {w for w, lst in thru.items() if NO_ANCHOR or all(a in inP for a in lst)}
        ids = {}

        def nid(l, w):
            key = (l, w)
            if key not in ids:
                ids[key] = len(ids)
            return ids[key]

        def nodes_of(a):
            out = []
            for l in range(N):
                w = pids[a][l]
                if l == sigma and w not in anchor:
                    continue
                out.append(nid(l, w))
            return out

        def collect(family):
            V, R, G = set(), set(), set()
            for a in family:
                ns = nodes_of(a)                      # crecientes en paso, y por tanto no en id: se ordenan
                V.update(ns)
                for pr in combinations(ns, 2):
                    R.add(pr if pr[0] < pr[1] else (pr[1], pr[0]))
                for tr in combinations(ns, 3):
                    G.add(tuple(sorted(tr)))
            return V, R, G

        V1, R1, G1 = collect(P)
        V0, R0, G0 = collect(P0)
        Vs, Rs, Gs = V0 - V1, R0 - R1, G0 - G1
        step_of = {i: l for (l, _), i in ids.items()}
        at = {}
        for i, l in step_of.items():
            at.setdefault(l, []).append(i)
        inV = lambda x: x in V1 or x in Vs
        inR = lambda x, y: ((x, y) if x < y else (y, x)) in R1 or ((x, y) if x < y else (y, x)) in Rs
        def inG(x, y, z):
            t = tuple(sorted((x, y, z)))
            return t in G1 or t in Gs
        changed = True
        while changed:
            changed = False
            for y in list(Vs):
                for l in range(N):
                    if l == step_of[y]:
                        continue
                    if not any(inV(s) and inR(y, s) for s in at.get(l, ())):
                        Vs.discard(y); changed = True
                        break
            for (y, w) in list(Rs):
                ok = inV(y) and inV(w)
                if ok:
                    sy, sw = step_of[y], step_of[w]
                    for l in range(N):
                        if l == sy or l == sw:
                            continue
                        if not any(inV(s) and inR(y, s) and inR(w, s) and inG(y, w, s) for s in at.get(l, ())):
                            ok = False
                            break
                if not ok:
                    Rs.discard((y, w)); changed = True
            for (x, u, w) in list(Gs):
                ok = inR(x, u) and inR(x, w) and inR(u, w)
                if ok:
                    st = (step_of[x], step_of[u], step_of[w])
                    for l in range(N):
                        if l in st:
                            continue
                        if not any(inV(s) and inR(x, s) and inR(u, s) and inR(w, s) and inG(x, u, s)
                                   and inG(x, w, s) and inG(u, w, s) for s in at.get(l, ())):
                            ok = False
                            break
                if not ok:
                    Gs.discard((x, u, w)); changed = True
        return len(Vs) + len(Rs) + len(Gs)

    def both(P0, P, T, N, sigma, tag):
        nonlocal ph_cases, ph_total
        before = fails
        helly(P0, P, T, sigma, tag)
        if fails > before or PHANTOM_ALL:
            ph_cases += 1
            ph_total += phantom(P0, P, N, sigma)

    for T in range(1, C + 1):
        for ki in M.map_nodes(T - 1):
            base = [a for a in A if first[a] >= T and sels[a][T - 1] == ki]
            if not base:
                continue
            for (ds, di) in M.sons(T - 1, ki):
                cases += 1
                reqs = M.req(ds, di)
                for (rs, ri) in reqs:
                    both(base, [a for a in base if sels[a][rs] == ri], T, T, rs, "filtro")
                if T < C:
                    P0 = [a for a in base if all(sels[a][rs] == ri for (rs, ri) in reqs)]
                    P = [a for a in A if first[a] >= T + 1 and sels[a][T] == di and sels[a][T - 1] == ki]
                    both(P0, P, T, T + 1, T, "UP")
    name = path.split("/")[-1]
    print(f"{name}\tvars={n}\tclausulas={len(clauses)}\tcasos={cases}\tfuera={outside}\thipotesis={hyps}\tfallos={fails}\tfiltro={by_op['filtro']}\tUP={by_op['UP']}\tcasos_f={ph_cases}\tfantasmas={ph_total}")
    if example is not None:
        print("   primer fallo (operación, T, σ, nodo de σ, tres nodos (paso, ventana)):", example)
    return fails


PHANTOM_ALL = "--phantom-all" in sys.argv
# control del propio script: sin el ancla la estructura entera de P0 es cerrada y todo sospechoso sobrevive
NO_ANCHOR = "--no-anchor" in sys.argv

if __name__ == "__main__":
    total = sum(check(p) for p in sys.argv[1:] if not p.startswith("--"))
    sys.exit(1 if total else 0)
