import sys, random, subprocess
S=sys.argv[1]
roles=['A','B','C','s1','s2','t1','t2']
# clauses as lists of (role, positive)
CL=[[('A',False),('s1',True),('s2',True)],
    [('B',True),('t1',True),('t2',True)],
    [('s1',False),('t1',False),('C',False)],
    [('s1',False),('t2',False),('C',False)],
    [('s2',False),('t1',False),('C',False)],
    [('s2',False),('t2',False),('C',False)]]
def run(tag,order,corder):
    pos={r:i for i,r in enumerate(order)}
    lines=['p cnf 7 6']
    for ci in corder:
        lines.append(' '.join(str((pos[r]+1)*(1 if p else -1)) for r,p in CL[ci])+' 0')
    f=f'{S}/case_{tag}.cnf'; open(f,'w').write('\n'.join(lines)+'\n')
    a,b,c=pos['A'],pos['B'],pos['C']
    top=2*7+1+6
    args=['./.lake/build/bin/helly','splittracef',f,str(top),str(top),'0',
          str(2*a+1),'0',str(2*a),'1', str(2*b+1),'1',str(2*b),'0', str(2*c+1),'0']
    out=subprocess.run(args,capture_output=True,text=True).stdout.split('\n')
    uni=[l for l in out if l.startswith('  [union]')][0]
    agg=[l for l in out if l.startswith('  [pin+aggressive]')][0]
    rho=[l for l in out if l.strip().startswith(f'{2*c+1}.0<')]
    sides=[l for l in out if l.startswith('  side') and 'keeps x→v true' in l]
    empty=[l.split(':')[0].strip() for l in out if l.startswith('  step') and l.rstrip().endswith(':')]
    print(f'{tag}: vars {order} clauses {corder}')
    print('   union x→v', 'x→v true' in uni, '| after pin+review x→v', 'x→v true' in agg.split('gowners')[0], '| sides keeping', len(sides))
    for l in rho: print('   ', l.strip())
    print('    steps with NO common node owning r (in the union):', empty[:12])
random.seed(7)
run('o0',['B','s1','A','t1','C','s2','t2'],[0,1,2,3,4,5])
run('o1',['A','B','C','s1','s2','t1','t2'],[0,1,2,3,4,5])
run('o2',['s1','A','s2','t1','B','t2','C'],[2,3,4,5,0,1])
run('o3',['A','s1','s2','B','t1','t2','C'],[2,5,3,4,0,1])
for i in range(4,12):
    o=roles[:]; random.shuffle(o); c=list(range(6)); random.shuffle(c)
    run(f'o{i}',o,c)
