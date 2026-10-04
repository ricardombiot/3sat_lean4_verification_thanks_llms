#!/usr/bin/env python3
"""Genera fórmulas 3-SAT aleatorias pequeñas (cláusulas de 3 variables distintas).
Uso: scripts/gen_small.py DIR NVARS MMIN MMAX POR_M SEMILLA"""
import random, sys, os
d, n, mmin, mmax, k, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
rng = random.Random(seed)
os.makedirs(d, exist_ok=True)
for m in range(mmin, mmax + 1):
    for i in range(k):
        cls = []
        for _ in range(m):
            vs = rng.sample(range(1, n + 1), 3)
            cls.append(" ".join(str(v if rng.random() < .5 else -v) for v in vs) + " 0")
        with open(f"{d}/r_v{n}_c{m}_s{seed}_{i}.cnf", "w") as f:
            f.write(f"c random seed={seed}\np cnf {n} {m}\n" + "\n".join(cls) + "\n")
