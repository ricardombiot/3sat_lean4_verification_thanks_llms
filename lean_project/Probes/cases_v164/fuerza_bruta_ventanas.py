import itertools, sys
cls=[]; n=0
for line in open(sys.argv[1] if len(sys.argv)>1 else 'construido.cnf'):
    if line.startswith('c'): continue
    if line.startswith('p'): n=int(line.split()[2]); continue
    l=[int(t) for t in line.split()][:-1]
    if l: cls.append(l)
sols=[]
for bits in itertools.product([0,1],repeat=n):
    if all(any((bits[abs(t)-1]==1)==(t>0) for t in c) for c in cls): sols.append(bits)
print('solutions',len(sols))
X={0:1}; V={2:1}; R={4:1}   # A=1, B=1, C=1 (0-indexed vars)
def ext(s,a): return all(s[k]==v for k,v in a.items())
print('triple sat:', any(ext(s,{**X,**V,**R}) for s in sols))
print('pairs:', any(ext(s,{**X,**V}) for s in sols), any(ext(s,{**X,**R}) for s in sols), any(ext(s,{**V,**R}) for s in sols))
# windows: var steps (x_k with x_{k-1}), negation steps (x_k), clause steps (clause j vars + clause j-1 vars)
wins=[]
for k in range(n):
    wins.append(('var',k,[k]+([k-1] if k>0 else [])))
    wins.append(('neg',k,[k]))
for j,c in enumerate(cls):
    vs=[abs(t)-1 for t in c]+([abs(t)-1 for t in cls[j-1]] if j>0 else [])
    wins.append(('clause',j,sorted(set(vs))))
bad=[]
for kind,idx,W in wins:
    pats=set(tuple(s[w] for w in W) for s in sols)
    ok=False
    for pat in pats:
        a=dict(zip(W,pat))
        if all(any(ext(s,{**a,**T}) for s in sols) for T in (X,V,R)):
            ok=True; break
    if not ok: bad.append((kind,idx))
print('windows without a node compatible with x, v and r:', bad)
