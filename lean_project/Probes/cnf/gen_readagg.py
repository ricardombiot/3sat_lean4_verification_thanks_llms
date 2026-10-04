"""Formulas for `join-borrow readagg` (report v116).

* sat/tseitin_*_even.cnf — the saved Tseitin formulas (ar/*_H.cnf, odd total charge, UNSAT) with the
  parity of their first vertex flipped: total charge even, so SAT, with the same parity structure.
* col/k4_3col.cnf — 3-colouring of K4 (UNSAT; pairwise consistency does not refute it).
  col/k4minus_3col.cnf — the same without one edge (SAT).
  Two-literal clauses are padded with one shared fresh variable z: (C or z) and (C or not z).
"""
import itertools, os

here = os.path.dirname(os.path.abspath(__file__))

def read(path):
    clauses, nv = [], 0
    for line in open(path):
        t = line.split()
        if not t or t[0] in ('c',):
            continue
        if t[0] == 'p':
            nv = int(t[2]); continue
        clauses.append([int(x) for x in t if x != '0'])
    return nv, clauses

def write(path, nv, clauses, comment):
    with open(path, 'w') as f:
        f.write(f"c {comment}\np cnf {nv} {len(clauses)}\n")
        for c in clauses:
            f.write(' '.join(map(str, c)) + ' 0\n')

for name in ['k4', 'k33', 'prism', 'cube', 'petersen']:
    nv, cl = read(os.path.join(here, 'ar', f'tseitin_{name}_H.cnf'))
    vs = sorted(abs(x) for x in cl[0])
    assert all(sorted(abs(x) for x in c) == vs for c in cl[:4])
    # parity constraint on the first vertex, flipped: forbid the assignments of the other parity
    signs = {tuple(x > 0 for x in sorted(c, key=abs)) for c in cl[:4]}
    flipped = []
    for bits in itertools.product([False, True], repeat=3):
        if bits not in signs:
            flipped.append([v if b else -v for v, b in zip(vs, bits)])
    assert len(flipped) == 4
    write(os.path.join(here, 'sat', f'tseitin_{name}_even.cnf'), nv, flipped + cl[4:],
          f'tseitin {name}, first vertex parity flipped: even total charge (SAT)')

def coloring(edges, n, k, path, comment):
    x = lambda v, c: v * k + c + 1
    z = n * k + 1
    cl = [[x(v, c) for c in range(k)] for v in range(n)]
    for (u, w) in edges:
        for c in range(k):
            cl.append([-x(u, c), -x(w, c), z])
            cl.append([-x(u, c), -x(w, c), -z])
    write(path, z, cl, comment)

k4 = list(itertools.combinations(range(4), 2))
coloring(k4, 4, 3, os.path.join(here, 'col', 'k4_3col.cnf'), '3-colouring of K4 (UNSAT)')
coloring(k4[1:], 4, 3, os.path.join(here, 'col', 'k4minus_3col.cnf'), '3-colouring of K4 minus an edge (SAT)')
