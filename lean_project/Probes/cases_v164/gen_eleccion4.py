import sys, random, subprocess, time
S=sys.argv[1]; N=int(sys.argv[2]); seed=int(sys.argv[3])
roles=['A','B','C','s1','s2','s3','s4','t1','t2','t3','t4','y1','y2','z1','z2']
CL=[[('A',False),('s1',True),('y1',True)],[('y1',False),('s2',True),('y2',True)],[('y2',False),('s3',True),('s4',True)],
    [('B',True),('t1',True),('z1',True)],[('z1',False),('t2',True),('z2',True)],[('z2',False),('t3',True),('t4',True)]]
for i in (1,2,3,4):
  for j in (1,2,3,4):
    CL.append([(f's{i}',False),(f't{j}',False),('C',False)])
n=len(roles); m=len(CL)
def run(tag,order,corder):
    pos={r:i for i,r in enumerate(order)}
    lines=[f'p cnf {n} {m}']+[' '.join(str((pos[r]+1)*(1 if p else -1)) for r,p in CL[ci])+' 0' for ci in corder]
    f=f'{S}/wide4_{tag}.cnf'; open(f,'w').write('\n'.join(lines)+'\n')
    a,b,c=pos['A'],pos['B'],pos['C']; top=2*n+1+m
    args=['./.lake/build/bin/helly','splittracef',f,str(top),str(top),'0',
          str(2*a+1),'0',str(2*a),'1', str(2*b+1),'1',str(2*b),'0', str(2*c+1),'0']
    t0=time.time()
    out=subprocess.run(args,capture_output=True,text=True).stdout.split('\n')
    uni=[l for l in out if l.startswith('  [union]')]
    if not uni: print(tag,'no union line', out[:3]); return
    agg=[l for l in out if l.startswith('  [pin+aggressive]')][0]
    rho=[l for l in out if l.strip().startswith(f'{2*c+1}.0<')]
    sides=[l for l in out if l.startswith('  side') and 'keeps x→v true' in l]
    empty=[l.split(':')[0].strip().split()[1] for l in out if l.startswith('  step') and l.rstrip().endswith(':')]
    print(f'{tag}: vars {order} clauses {corder} ({time.time()-t0:.0f}s)')
    print('   union x→v', 'x→v true' in uni[0], '| after pin+review x→v', 'x→v true' in agg.split('gowners')[0], '| sides keeping', len(sides))
    for l in rho: print('   ', l.strip()[:200])
    print('    steps with NO common node owning r:', ' '.join(empty))
    sys.stdout.flush()
random.seed(seed)
run('w0',roles,list(range(m)))
for i in range(1,N):
    o=roles[:]; random.shuffle(o); c=list(range(m)); random.shuffle(c)
    run(f'w{i}',o,c)
