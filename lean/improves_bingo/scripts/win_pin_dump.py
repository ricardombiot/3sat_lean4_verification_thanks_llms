#!/usr/bin/env python3
"""Volcado de los fantasmas de una ventana y de qué segundo testigo λ los mata.

    python3 scripts/win_pin_dump.py [--orden=cadena|inversa] [--ventanas=N] f.cnf

Para la ventana entera (P0 = soluciones con las ventanas anteriores, P = además la ventana, σ = el paso del nodo de
ventana), los fantasmas de la estructura cerrada con testigos solo en σ. Para cada fantasma trío t = (x, u, w) y cada
paso λ ≠ σ:

  real       ¿sobrevive t en la estructura cerrada con testigos en {σ, λ}?
  predicción «el testigo de λ ve el conflicto»: las tres caras de t (las ramas de P que pasan por dos de sus nodos)
             no tienen ningún nodo común en el paso λ:  S_xu(λ) ∩ S_xw(λ) ∩ S_uw(λ) = ∅,  con
             S_yz(λ) = { pid_a(λ) : a ∈ P, a pasa por y y por z }.

Imprime la matriz de confusión (predicción frente a real) sobre todas las ventanas y, para las primeras, el volcado:
los nodos del fantasma (paso, lo que leen, sus valores) y, por cada λ, qué lee y qué valores de su variable dejan
las tres caras.
"""
import sys
from itertools import product

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from helly_formula import parse, Map  # noqa: E402
from win_pin_formula import phantom  # noqa: E402
from win_pin_witness import describe  # noqa: E402
from win_pin_rule import node_vars  # noqa: E402


def lit_val(M, k, sel):
    """La variable que lee el paso `k` y el valor que le da el nodo `sel` (None si no lee ninguna)."""
    if k <= 0 or k == M.mid or k >= M.top:
        return None
    if k < M.mid:
        v = (k - 1) // 2
        return v, bool(sel) if k % 2 == 1 else (not bool(sel))
    o = k - M.mid - 1
    v, pos = M.cl[o // 3][o % 3]
    return v, bool(sel) if pos else (not bool(sel))


def up_conflict(clauses, dec):
    """Propagación unitaria desde las decisiones `dec`; devuelve las cláusulas de la derivación del conflicto (o None)."""
    val = dict(dec)
    reason = {}
    changed = True
    conflict = None
    while changed and conflict is None:
        changed = False
        for ci, c in enumerate(clauses):
            if any(v in val and val[v] == pos for v, pos in c):
                continue
            free = [(v, pos) for v, pos in c if v not in val]
            if not free:
                conflict = ci
                break
            if len({v for v, _ in free}) == 1:
                v, pos = free[0]
                val[v] = pos
                reason[v] = ci
                changed = True
    if conflict is None:
        return None
    used, stack = set(), [conflict]
    while stack:
        ci = stack.pop()
        if ci in used:
            continue
        used.add(ci)
        for v, _ in clauses[ci]:
            if v in reason and reason[v] not in used:
                stack.append(reason[v])
    return used


def check(path, order, nshow):
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
    clist = list(range(len(clauses)))
    if order == "inversa":
        clist.reverse()
    conf = {(pk, rs): 0 for pk in (True, False) for rs in (True, False)}
    conf2 = dict(conf)
    conf3 = dict(conf)
    miss = []
    miss3 = []
    up_none = [0]
    tri_total = [0]
    tri_node_kill = [0]
    other = [0, 0]                           # fantasmas nodo / pareja (se esperan 0)
    shown = [0]
    var_of = lambda k: describe(M, k)

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
            other[0] += len(Vs); other[1] += len(Rs)
            if Gs:
                surv = {}
                for lam in range(C):
                    if lam != k:
                        surv[lam] = phantom(pids, P0, P, C, k, [k, lam], ret=True)[2]
                show = shown[0] < nshow
                if show:
                    shown[0] += 1
                    print(f"\n== cláusula {j} {clauses[j]}, ventana {v}, σ = {k}: {len(Gs)} tríos fantasma")
                for ti, t in enumerate(sorted(Gs)):
                    nodes = [key_of[x] for x in t]          # (paso, pid)
                    through = lambda a, y: pids[a][y[0]] == y[1]
                    faces = [[a for a in P if through(a, nodes[i]) and through(a, nodes[i2])]
                             for i, i2 in ((0, 1), (0, 2), (1, 2))]
                    if show and ti < 3:
                        print("  trío:", ", ".join(f"paso {st} {var_of(st)} pid={pid}" for st, pid in nodes),
                              f"| ramas de P por cada cara: {[len(f) for f in faces]}")
                    singles = [[a for a in P if through(a, y)] for y in nodes]
                    # la regla de propagación: decisiones = lo que leen los nodos del trío + lo constante en P0
                    # + la ventana; λ mata si su nodo lee dos variables de una cláusula de la derivación
                    dec = {x: asg[P0[0]][x] for x in range(n) if len({asg[a][x] for a in P0}) == 1}
                    for t2, x in zip(steps, v):
                        lv = lit_val(M, t2, x)
                        if lv:
                            dec[lv[0]] = lv[1]
                    for st_, pid_ in nodes:
                        for d, sv_ in zip((0, 1, 2), pid_):
                            if sv_ is not None:
                                lv = lit_val(M, st_ - d, sv_)
                                if lv:
                                    dec[lv[0]] = lv[1]
                    used = up_conflict(clauses, dec)
                    if used is None:
                        up_none[0] += 1
                    has_node_kill = False
                    for lam in surv:
                        if lam in (st for st, _ in nodes):
                            pass
                        N0 = [{pids[a][lam] for a in f} for f in singles]
                        if not (N0[0] & N0[1] & N0[2]):
                            has_node_kill = True
                    tri_total[0] += 1
                    tri_node_kill[0] += has_node_kill
                    for lam in surv:
                        S = [{pids[a][lam] for a in f} for f in faces]
                        pred_kill = not (S[0] & S[1] & S[2])
                        real_kill = t not in surv[lam]
                        conf[(pred_kill, real_kill)] += 1
                        # por nodos: un testigo s en λ necesita una rama de P por s y cada nodo del trío
                        N1 = [{pids[a][lam] for a in f} for f in singles]
                        nk = not (N1[0] & N1[1] & N1[2])
                        conf2[(nk, real_kill)] += 1
                        if used is not None:
                            nv = node_vars(M, lam)
                            uk = any(len(nv & {x for x, _ in clauses[ci]}) >= 2 for ci in used)
                            conf3[(uk, real_kill)] += 1
                            if uk != real_kill and len(miss3) < 12:
                                miss3.append((j, v, [(st, var_of(st)) for st, _ in nodes], lam, var_of(lam),
                                              'mata' if real_kill else 'vive', sorted(used)))
                        if nk != real_kill and len(miss) < 12:
                            miss.append((j, v, [(st, var_of(st)) for st, _ in nodes], lam, var_of(lam),
                                         'mata' if real_kill else 'vive'))
                        if show and ti < 3 and (pred_kill or real_kill):
                            vals = [sorted({sols[a][lam] for a in f}) for f in faces]
                            print(f"     λ={lam:2d} {var_of(lam):12s} real={'mata' if real_kill else 'vive'}"
                                  f" pred={'mata' if pred_kill else 'vive'}  valores de λ por cara: {vals}")
            go(frozenset(P), idx + 1)

    go(frozenset(range(len(sols))), 0)
    name = path.split("/")[-1]
    print(f"\n{name}\torden={order}\tnodos_fantasma={other[0]}\tparejas_fantasma={other[1]}\t"
          f"pred_mata_real_mata={conf[(True, True)]}\tpred_mata_real_vive={conf[(True, False)]}\t"
          f"pred_vive_real_mata={conf[(False, True)]}\tpred_vive_real_vive={conf[(False, False)]}")
    print(f"   por nodos:\tpred_mata_real_mata={conf2[(True, True)]}\tpred_mata_real_vive={conf2[(True, False)]}\t"
          f"pred_vive_real_mata={conf2[(False, True)]}\tpred_vive_real_vive={conf2[(False, False)]}")
    print(f"   propagación:\tpred_mata_real_mata={conf3[(True, True)]}\tpred_mata_real_vive={conf3[(True, False)]}\t"
          f"pred_vive_real_mata={conf3[(False, True)]}\tpred_vive_real_vive={conf3[(False, False)]}\t"
          f"tríos_sin_conflicto_por_UP={up_none[0]}")
    print(f"   tríos fantasma={tri_total[0]}\tcon algún λ que cumple la condición de nodos={tri_node_kill[0]}")
    for m in miss3:
        print("   fallo de la regla de propagación (cláusula, ventana, nodos, λ, lee, real, cláusulas usadas):", m)


if __name__ == "__main__":
    order = "cadena"
    nshow = 2
    files = []
    for a in sys.argv[1:]:
        if a.startswith("--orden="):
            order = a.split("=", 1)[1]
        elif a.startswith("--ventanas="):
            nshow = int(a.split("=", 1)[1])
        else:
            files.append(a)
    for p in files:
        check(p, order, nshow)
