#!/usr/bin/env python3
"""¿Elige bien el segundo testigo la regla «λ separa el triángulo»?

    python3 scripts/win_pin_rule.py [--orden=cadena|inversa] f1.cnf ...

Para cada ventana entera (P0 = las soluciones con las ventanas anteriores, P = además la ventana, σ = el paso de su
nodo de ventana) se calcula la estructura cerrada con testigos solo en σ y sus fantasmas. Para cada fantasma (nodo,
pareja o trío) se miran las variables **libres** que leen sus nodos (un nodo del paso `k` lee las variables de los
pasos `k`, `k - 1`, `k - 2`; libre = no constante en P).

**La regla**: un paso λ separa el fantasma si, quitando las variables libres que lee el nodo de λ, las variables
libres del fantasma que quedan no están todas en una misma componente del grafo residual (variables libres, unidas
si comparten una cláusula que P no deja ya satisfecha por las variables fijadas).

Por ventana con fantasmas se mide:
  sin_sep     fantasmas sin ningún paso que los separe
  regla_ok    hay un λ que separa todos los fantasmas y {σ, λ} no deja fantasmas
  algun_sep   algún λ que separa algún fantasma deja {σ, λ} sin fantasmas
  sep_malo    pasos que separan todos los fantasmas pero {σ, λ} sí deja fantasmas
y, aparte, cuántos λ que funcionan (de la sonda de testigos) no separan nada.
"""
import sys
from itertools import product

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from helly_formula import parse, Map  # noqa: E402
from win_pin_formula import phantom  # noqa: E402


def step_vars(M, k):
    """Las variables que lee el paso `k` (ninguna en raíz, fusiones y final)."""
    if k <= 0 or k == M.mid or k >= M.top:
        return set()
    if k < M.mid:
        return {(k - 1) // 2}
    o = k - M.mid - 1
    return {M.cl[o // 3][o % 3][0]}


def node_vars(M, k):
    out = set()
    for d in (0, 1, 2):
        if k - d >= 0:
            out |= step_vars(M, k - d)
    return out


def check(path, order):
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
    name = path.split("/")[-1]
    clist = list(range(len(clauses)))
    if order == "inversa":
        clist.reverse()
    st = {"ventanas": 0, "con_fantasmas": 0, "fantasmas": 0, "sin_sep": 0, "regla_ok": 0, "algun_sep": 0,
          "sep_malo": 0, "lam_ok": 0, "lam_ok_no_sep": 0,
          "pares_sep": 0, "pares_sep_sobrevive": 0, "fantasma_muere_por_sep": 0, "sep_vacio": 0}
    ex = []

    def residual(P):
        free = {v for v in range(n) if len({asg[a][v] for a in P}) > 1}
        val = {v: asg[P[0]][v] for v in range(n) if v not in free}
        adj = {v: set() for v in free}
        for c in clauses:
            if any(v not in free and val[v] == pos for v, pos in c):
                continue
            vs = [v for v, _ in c if v in free]
            for x in vs:
                adj[x] |= set(vs) - {x}
        return free, adj

    def comps(free, adj, cut):
        comp = {}
        for v in free:
            if v in cut or v in comp:
                continue
            stack = [v]
            comp[v] = v
            while stack:
                x = stack.pop()
                for y in adj[x]:
                    if y not in cut and y not in comp:
                        comp[y] = v
                        stack.append(y)
        return comp

    def go(F, idx):
        if idx == len(clist):
            return
        j = clist[idx]
        k = M.mid + 1 + 3 * j + 2
        steps = (k - 2, k - 1, k)
        for v in sorted({tuple(sols[a][t] for t in steps) for a in F}):
            st["ventanas"] += 1
            P0 = sorted(F)
            P = [a for a in P0 if all(sols[a][t] == x for t, x in zip(steps, v))]
            Vs, Rs, Gs, key_of = phantom(pids, P0, P, C, k, [k], ret=True)
            objs = [(x,) for x in Vs] + list(Rs) + list(Gs)
            if objs:
                st["con_fantasmas"] += 1
                st["fantasmas"] += len(objs)
                free, adj = residual(P)
                ovars = [set().union(*(node_vars(M, key_of[x][0]) for x in o)) & free for o in objs]
                seps = []                         # por fantasma, los λ que lo separan
                for ov in ovars:
                    ls = set()
                    for lam in range(C):
                        if lam == k:
                            continue
                        cut = node_vars(M, lam) & free
                        rest = ov - cut
                        cm = comps(free, adj, cut)
                        if len({cm[x] for x in rest}) >= 2:
                            ls.add(lam)
                    seps.append(ls)
                st["sin_sep"] += sum(1 for ls in seps if not ls)
                cm0 = comps(free, adj, set())
                st["sep_vacio"] += sum(1 for ov in ovars if len({cm0[x] for x in ov}) >= 2)
                surv = {}
                for lam in range(C):
                    if lam == k:
                        continue
                    V2, R2, G2, _ = phantom(pids, P0, P, C, k, [k, lam], ret=True)
                    surv[lam] = {(x,) for x in V2} | R2 | G2
                works = {lam for lam in surv if not surv[lam]}
                # por fantasma: ¿todo λ que lo separa lo mata? (lo que usaría un descenso, fantasma a fantasma)
                for o, ls in zip(objs, seps):
                    for lam in ls:
                        st["pares_sep"] += 1
                        if o in surv[lam]:
                            st["pares_sep_sobrevive"] += 1
                    if any(o not in surv[lam] for lam in ls):
                        st["fantasma_muere_por_sep"] += 1
                all_sep = set.intersection(*seps) if seps else set()
                any_sep = set.union(*seps) if seps else set()
                if all_sep & works:
                    st["regla_ok"] += 1
                if any_sep & works:
                    st["algun_sep"] += 1
                st["sep_malo"] += len(all_sep - works)
                st["lam_ok"] += len(works)
                st["lam_ok_no_sep"] += len(works - any_sep)
                if len(ex) < 4:
                    ex.append((j, v, len(objs), sorted(all_sep), sorted(works)))
            go(frozenset(P), idx + 1)

    go(frozenset(range(len(sols))), 0)
    print(name + f"\torden={order}\t" + "\t".join(f"{a}={b}" for a, b in st.items()))
    for e in ex:
        print("   cláusula, ventana, fantasmas, λ que separan todos, λ que funcionan:", e)


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
