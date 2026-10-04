import itertools, sys
# roles -> var index (order of the map)
order=['A','t1','B','s1','C','y1','s2','s3','s4','t2','t3','t4','y2','q','n1','n2','n3']
V={r:i for i,r in enumerate(order)}; n=len(order)
L=lambda r,p=True:(V[r],p)
cls=[[L('A',0),L('s1'),L('y1')],[L('y1',0),L('s2'),L('y2')],[L('y2',0),L('s3'),L('s4')],
     [L('n1'),L('n2'),L('n3')]]
for t in ['t1','t2','t3','t4']:
    cls+= [[L('B',0),L(t,0),L('q')],[L('B',0),L(t,0),L('q',0)]]
cls+=[[L('n1'),L('n2'),L('n3')]]
for i in '1234': cls.append([L('C',0),L('s'+i,0),L('t'+i)])
LB=2*n; top=LB+1+len(cls)
def lit(b,l): return b[l[0]]==(1 if l[1] else 0)
def sel(b,k):
    if k<LB:
        u=k//2; return (k,b[u]) if k%2==0 else (k,1-b[u])
    if k==LB or k==top: return (k,0)
    c=cls[k-LB-1]; return (k,4*lit(b,c[0])+2*lit(b,c[1])+lit(b,c[2]))
def canon(b,k): return (sel(b,k), sel(b,k-1) if k>0 else None)
sols=[b for b in itertools.product([0,1],repeat=n) if all(any(lit(b,l) for l in c) for c in cls)]
print('vars',n,'clauses',len(cls),'solutions',len(sols))
A,B,C=V['A'],V['B'],V['C']
print('triple sat', any(b[A]==1 and b[B]==1 and b[C]==1 for b in sols))
steps=range(top+1)
paths=[tuple(canon(b,k) for k in steps) for b in sols]
compat=set()
for pth in paths:
    for i in range(len(pth)):
        for j in range(len(pth)):
            compat.add((pth[i],pth[j]))
x=canon([1]*n,2*A+1) if False else None
# x: node of "not A" at step 2A+1 with A=1 ; v: same for B ; r: map node of "not C" with C=1
def negnode(u,val): return ((2*u+1,1-val),(2*u,val))
x=negnode(A,1); v=negnode(B,1); rstep=2*C+1; rid=(rstep,0)
print('x~v',(x,v) in compat,'x~r',any((x,z) in compat for z in [negnode(C,1)]),'v~r',(v,negnode(C,1)) in compat)
# one-level witness (SemWitness hypothesis)
bystep={}
for pth in paths:
    for k,z in enumerate(pth): bystep.setdefault(k,set()).add(z)
rnodes=[z for z in bystep[rstep] if z[0]==rid]
ok1=all(any((x,z) in compat and (v,z) in compat and any((z,rr) in compat for rr in rnodes) for z in bystep[k]) for k in steps)
print('SemWitness hypothesis holds:', ok1)
# greatest closed family: compat pairs, pinned at r's step, closed under common nodes at every step
R=set(p for p in compat if not (p[1][0][0]==rstep and p[1][0]!=rid) and not (p[0][0][0]==rstep and p[0][0]!=rid))
changed=True; it=0
while changed:
    changed=False; it+=1
    nb={}
    for a,b in R: nb.setdefault(a,set()).add(b)
    rem=set()
    for a,b in R:
        na=nb.get(a,set()); nbb=nb.get(b,set())
        for k in steps:
            if not any(z in nbb for z in na if z[0][0]==k):
                rem.add((a,b)); break
    if rem:
        R-=rem; R-=set((b,a) for a,b in rem); changed=True
print('closure rounds',it,'pairs left',len(R),'| x→v in the greatest closed family:',(x,v) in R)
