#!/usr/bin/env python3
"""`WinPinFree` de ForbidOnWinPin.lean, por fuerza bruta sobre la fórmula (sin ejecutar la máquina).

    python3 scripts/win_pin_formula.py [--orden=cadena|inversa] [--tope=N] f1.cnf f2.cnf ...

Sobre las soluciones completas (`SolE φ stepCount k`), el lector fija ventanas una a una: la ventana de la cláusula `j`
son los tres ids `[abuelo, padre, hijo]` de su nodo del tercer paso (pasos `clauseStep j 0, 1, 2`), con los valores de
alguna solución que cumpla lo fijado antes. Para cada ventana y cada orden de sus tres ids se comprueba la condición
de `WinPinFree`: fijar cada id, con lo anterior fijado, no deja familias fantasma (`PhantomFree P0 P N σ`, N =
stepCount, σ = el paso del id), calculando la mayor estructura cerrada como `helly_formula.py`.

Las ventanas van en el orden de las cláusulas (`--orden=cadena`, el del primer paso con elección del lector) o al
revés (`--orden=inversa`). `--tope` corta el número de ventanas comprobadas por fórmula.

Por fórmula: ventanas comprobadas, cuántas cumplen en el orden natural `[abuelo, padre, hijo]`, cuántas en algún
orden (lo que pide `WinPinFree`), fantasmas en el peor caso, y el primer fallo si lo hay.
"""
import sys
import resource
from itertools import permutations, combinations

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from helly_formula import parse, Map  # noqa: E402

# tope de memoria: 3 GB (en macOS `RLIMIT_AS` no se aplica: se mira el pico, `ru_maxrss`, en bytes)
RAM_CAP = 3 << 30


def ram_guard():
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    if sys.platform != "darwin":
        rss *= 1024
    if rss > RAM_CAP:
        sys.exit(f"corte por memoria: pico {rss >> 20} MB")


def phantom(pids, P0, P, N, sigma, L=None, ret=False):
    """Elementos de la mayor estructura cerrada (pasos 0..N-1, ramas de P0) que no son de ninguna rama de P. Con `L`,
    la regla solo pide testigos en los pasos de `L` (para medir cuántos hacen falta)."""
    ram_guard()
    Ls = range(N) if L is None else L
    inP = set(P)
    if len(inP) == len(P0):
        return (set(), set(), set(), {}) if ret else 0
    thru = {}
    for a in P0:
        thru.setdefault(pids[a][sigma], []).append(a)
    anchor = {w for w, lst in thru.items() if NO_ANCHOR or all(a in inP for a in lst)}
    ids = {}

    def nodes_of(a):
        out = []
        for l in range(N):
            w = pids[a][l]
            if l == sigma and w not in anchor:
                continue
            key = (l, w)
            if key not in ids:
                ids[key] = len(ids)
            out.append(ids[key])
        return out

    nodesP = {}
    mP = {}
    for a in P:
        ns = nodes_of(a)
        nodesP[a] = ns
        bit = 1 << a
        for x in ns:
            mP[x] = mP.get(x, 0) | bit
    sus = [a for a in P0 if a not in inP]
    Vs, Rs, Gs = set(), set(), set()
    for a in sus:
        ns = nodes_of(a)
        for x in ns:
            if not mP.get(x, 0):
                Vs.add(x)
        for x, y in combinations(ns, 2):
            if not (mP.get(x, 0) & mP.get(y, 0)):
                Rs.add((x, y) if x < y else (y, x))
        for t in combinations(ns, 3):
            x, y, z = t
            if not (mP.get(x, 0) & mP.get(y, 0) & mP.get(z, 0)):
                Gs.add(tuple(sorted(t)))
    step_of = {i: l for (l, _), i in ids.items()}
    at = {}
    for i, l in step_of.items():
        at.setdefault(l, []).append(i)
    inV = lambda x: x in mP or x in Vs

    def inR(x, y):
        if mP.get(x, 0) & mP.get(y, 0):
            return True
        return ((x, y) if x < y else (y, x)) in Rs

    def inG(x, y, z):
        if mP.get(x, 0) & mP.get(y, 0) & mP.get(z, 0):
            return True
        return tuple(sorted((x, y, z))) in Gs

    changed = True
    while changed:
        changed = False
        for y in list(Vs):
            for l in Ls:
                if l == step_of[y]:
                    continue
                if not any(inV(s) and inR(y, s) for s in at.get(l, ())):
                    Vs.discard(y); changed = True
                    break
        for (y, w) in list(Rs):
            ok = inV(y) and inV(w)
            if ok:
                sy, sw = step_of[y], step_of[w]
                for l in Ls:
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
                for l in Ls:
                    if l in st:
                        continue
                    if not any(inV(s) and inR(x, s) and inR(u, s) and inR(w, s) and inG(x, u, s)
                               and inG(x, w, s) and inG(u, w, s) for s in at.get(l, ())):
                        ok = False
                        break
            if not ok:
                Gs.discard((x, u, w)); changed = True
    if ret:
        key_of = {i: kw for kw, i in ids.items()}
        return Vs, Rs, Gs, key_of
    return len(Vs) + len(Rs) + len(Gs)


def helly4_fails(pids, P0, P, T, sigma):
    """Fallos de `Helly4 P0 P T σ`: una rama a0 de P0 \\ P por tres nodos (pasos i, j, l < T) y tres ramas de P por
    cada dos de ellos y por un mismo nodo del paso σ, sin ninguna rama de P por los tres."""
    inP = set(P)
    by_s = {}
    for a in P:
        by_s.setdefault(pids[a][sigma], []).append(a)
    fails = 0
    example = None
    for a0 in P0:
        if a0 in inP:
            continue
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
            nb = [0] * T
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
                            cover = 0
                            bij = (1 << i) | (1 << j)
                            for m in allm:
                                if m & bij == bij:
                                    cover |= m
                            bad = cand & ~cover
                            if bad:
                                fails += 1
                                if example is None:
                                    l = (bad & -bad).bit_length() - 1
                                    example = (sigma, s, (i, p0[i]), (j, p0[j]), (l, p0[l]))
                    rest >>= 1
                    j += 1
    return fails, example


def check(path, order, cap):
    n, clauses = parse(path)
    M = Map(n, clauses)
    C = M.count
    sols, pids = [], []
    from itertools import product
    for a in product((False, True), repeat=n):
        s = [M.sel(a, k) for k in range(C)]
        p = [(s[k], s[k - 1] if k > 0 else None, s[k - 2] if k > 1 else None) for k in range(C)]
        if any(M.is_l3(k) and p[k] == (0, 0, 0) for k in range(C)):
            continue
        sols.append(s); pids.append(p)
    name = path.split("/")[-1]
    if not sols:
        print(f"{name}\tvars={n}\tclausulas={len(clauses)}\tinsatisfacible: WinPinFree vacía")
        return 0
    clist = list(range(len(clauses)))
    if order == "inversa":
        clist.reverse()
    stats = {"ventanas": 0, "natural": 0, "alguno": 0, "peor": 0}
    first_fail = [None]
    cache = {}

    h4 = {"pins": 0, "fallos": 0, "ej": None}
    h4cache = {}
    hw = {"casos": 0, "fallos": 0, "ej": None, "fantasmas": 0}

    def pin_h4(F, fixed, r):
        key = (F, fixed, r)
        if key in h4cache:
            return
        P0 = [a for a in F if all(sols[a][st] == v for st, v in fixed)]
        P = [a for a in P0 if sols[a][r[0]] == r[1]]
        f, ex = helly4_fails(pids, P0, P, C, r[0])
        h4cache[key] = f
        h4["pins"] += 1
        if f:
            h4["fallos"] += 1
            if h4["ej"] is None:
                h4["ej"] = ex

    def pin_ok(F, fixed, r):
        """Fijar el id `r = (paso, nodo)` sobre las ramas de F que cumplen `fixed`."""
        key = (F, fixed, r)
        if key not in cache:
            P0 = [a for a in F if all(sols[a][st] == v for st, v in fixed)]
            P = [a for a in P0 if sols[a][r[0]] == r[1]]
            cache[key] = phantom(pids, P0, P, C, r[0])
        return cache[key]

    def go(F, idx):
        if idx == len(clist) or stats["ventanas"] >= cap:
            return
        j = clist[idx]
        k = M.mid + 1 + 3 * j + 2           # el tercer paso de la cláusula j
        steps = (k - 2, k - 1, k)
        vals = sorted({tuple(sols[a][st] for st in steps) for a in F})
        for v in vals:
            if stats["ventanas"] >= cap:
                return
            stats["ventanas"] += 1
            w = tuple(zip(steps, v))
            res = {}
            for perm in permutations(w):
                worst = 0
                for i, r in enumerate(perm):
                    worst = max(worst, pin_ok(F, frozenset(perm[:i]), r))
                res[perm] = worst
            if HELLY:
                for i, r in enumerate(w):
                    pin_h4(F, frozenset(w[:i]), r)
                # la ventana entera de una vez, con el testigo en el paso del nodo de ventana
                P0w = sorted(F)
                Pw = [a for a in P0w if all(sols[a][st] == x for st, x in w)]
                f, ex = helly4_fails(pids, P0w, Pw, C, k)
                hw["casos"] += 1
                hw["fallos"] += bool(f)
                if f and hw["ej"] is None:
                    hw["ej"] = ex
                hw["fantasmas"] += phantom(pids, P0w, Pw, C, k)
            nat = res[w]
            best = min(res.values())
            stats["peor"] = max(stats["peor"], nat)
            if nat == 0:
                stats["natural"] += 1
            if best == 0:
                stats["alguno"] += 1
            elif first_fail[0] is None:
                first_fail[0] = (j, w, best)
            F2 = frozenset(a for a in F if all(sols[a][st] == x for st, x in w))
            go(F2, idx + 1)

    go(frozenset(range(len(sols))), 0)
    print(f"{name}\tvars={n}\tclausulas={len(clauses)}\tsoluciones={len(sols)}\torden={order}\t"
          f"ventanas={stats['ventanas']}\tnatural_ok={stats['natural']}\talgun_orden_ok={stats['alguno']}\t"
          f"fantasmas_max_natural={stats['peor']}" +
          (f"\thelly4_pins={h4['pins']}\thelly4_fallos={h4['fallos']}\tventana_helly4_fallos={hw['fallos']}"
           f"\tventana_fantasmas={hw['fantasmas']}" if HELLY else ""))
    if HELLY and hw["ej"] is not None:
        print("   primer fallo de Helly4 con la ventana entera:", hw["ej"])
    if HELLY and h4["ej"] is not None:
        print("   primer fallo de Helly4 (σ, nodo de σ, tres nodos (paso, ventana)):", h4["ej"])
    if first_fail[0] is not None:
        print("   primer fallo (cláusula, ventana [(paso, nodo)], fantasmas en el mejor orden):", first_fail[0])
    return stats["ventanas"] - stats["alguno"]


# control del propio script: sin el ancla los sospechosos tienen que sobrevivir
NO_ANCHOR = "--sin-ancla" in sys.argv
# además la condición de un paso (`Helly4`) en cada pin del orden natural
HELLY = "--helly" in sys.argv

if __name__ == "__main__":
    order = "cadena"
    cap = 10 ** 9
    files = []
    for a in sys.argv[1:]:
        if a.startswith("--orden="):
            order = a.split("=", 1)[1]
        elif a.startswith("--tope="):
            cap = int(a.split("=", 1)[1])
        elif a in ("--sin-ancla", "--helly"):
            pass
        else:
            files.append(a)
    total = sum(check(p, order, cap) for p in files)
    sys.exit(1 if total else 0)
