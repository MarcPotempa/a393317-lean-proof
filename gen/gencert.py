# Produces the Lean certificate for one machine (structure `Cert` / `CertE` of A393317/Checker.lean and
# A393317/Expo.lean) and tests it with an independent Python copy of the Lean checker.
#
#   python3 gencert.py NUM,J,j[,c]     prints the certificate of machine NUM with automaton parameters (J, j)
#                                      and growth factor c (1: quadratic potentials, 2: exponential potentials)
import sys, itertools, re
from fractions import Fraction as Fr
from math import lcm
import numpy as np
from scipy.optimize import linprog
from automata import rule, make_delta, lfpD, lfpG, reach, Q0, Fail

PAIRS=[(0,0),(0,1),(1,0),(1,1)]          # (e,r) with 0=U, 1=D; code 2e+r
def pcode(a): return 2*a[0]+a[1]

class Machine:
    def __init__(s,num):
        s.num=num; s.tr=rule(num)
    def nxt(s,st,sym): return s.tr[(st,sym)][0]
    def wrt(s,st,sym): return s.tr[(st,sym)][1]
    def rgt(s,st,sym): return s.tr[(st,sym)][2]==1

def build(num,J,j,c=1):
    M=Machine(num); tr=M.tr; delta=make_delta(J,j)
    # states of the automaton
    states=[Q0]; idx={Q0:0}; k=0
    while k<len(states):
        q=states[k]; k+=1
        for a in PAIRS:
            q2=delta(q,a)
            if q2 not in idx: idx[q2]=len(states); states.append(q2)
    N=len(states)
    dl=[[idx[delta(q,a)] for a in PAIRS] for q in states]
    lo=[len(q[1]) if q[0] else J+1 for q in states]; ex=[bool(q[0]) for q in states]
    Din=lfpD(tr,delta,(0,1)); Dbl=lfpD(tr,delta,(0,))
    init=reach({(Q0,a) for a in ((0,0),(0,1)) if (Q0,a) in Din},delta)
    Gin,_=lfpG(tr,delta,init,(0,1),Din,c)
    initbl=reach(Gin&Dbl,delta)
    Gbl,_=lfpG(tr,delta,initbl,(0,),Dbl,c)
    def table(A): return [[(q,a) in A for a in PAIRS] for q in states]
    C=dict(num=num,c=c,N=N,dl=dl,lo=lo,ex=ex,adI=table(Din),adB=table(Dbl),agI=table(Gin),agB=table(Gbl))
    al=lambda T,q,a: T[q][pcode(a)]
    # forward products (nodes with state numbers)
    def fwd(A,bits):
        I=set(); B=set(); todo=[('I',(b,0,0)) for b in bits]
        while todo:
            kind,x=todo.pop()
            if kind=='I':
                if x in I: continue
                I.add(x)
                for e in (0,1): todo.append(('B',(e,e)+x))
            else:
                if x in B: continue
                B.add(x); e,s,sym,qa,qt=x
                if M.rgt(s,sym):
                    a=(e,M.nxt(s,sym))
                    if not al(A,qa,a): raise Fail('D not closed')
                    todo.append(('I',(M.wrt(s,sym),dl[qa][pcode(a)],qt)))
                else:
                    for rr in (0,1):
                        a=(M.nxt(s,sym),rr)
                        if al(A,qt,a): todo.append(('B',(e,rr,M.wrt(s,sym),qa,dl[qt][pcode(a)])))
        return sorted(I),sorted(B)
    C['fI'],C['fB']=fwd(C['adI'],(0,1)); C['gI'],C['gB']=fwd(C['adB'],(0,))
    # top-down products, one for each initial symbol of the cell
    def td(AG,AD,bits):
        tI={}; tB={}; tD=set(); E={}
        for b0 in bits:
            succ={}; todo=[('I',(b0,b0,0,0))]
            while todo:
                nd=todo.pop()
                if nd in succ: continue
                out=[]
                if nd[0]=='I':
                    _,sym,g,qt=nd[1]
                    for a in PAIRS:
                        if al(AG,g,a): out.append((('B',(b0,a[1],a[0],sym,dl[g][pcode(a)],qt)),-c))
                else:
                    _,r,s,sym,g,qt=nd[1]
                    if M.rgt(s,sym):
                        if M.nxt(s,sym)==r: out.append((('I',(b0,M.wrt(s,sym),g,qt)),0))
                    else:
                        for rr in (0,1):
                            a=(M.nxt(s,sym),rr)
                            if al(AD,qt,a): out.append((('B',(b0,r,rr,M.wrt(s,sym),g,dl[qt][pcode(a)])),1))
                succ[nd]=out
                for x,_ in out: todo.append(x)
            useful={nd for nd in succ if nd[0]=='I'}; ch=True
            while ch:
                ch=False
                for nd,out in succ.items():
                    if nd not in useful and any(x in useful for x,_ in out): useful.add(nd); ch=True
            start=('I',(b0,b0,0,0)); dist={start:0}
            for it in range(len(succ)+2):
                ch=False
                for nd,out in succ.items():
                    if nd not in dist or nd not in useful: continue
                    for x,w in out:
                        if x in useful and (x not in dist or dist[x]<dist[nd]+w): dist[x]=dist[nd]+w; ch=True
                if not ch: break
            else: raise Fail('positive cycle')
            for nd in succ:
                if nd in useful:
                    if nd[0]=='I':
                        tI[nd[1]]=dist[nd]; _,sym,g,qt=nd[1]; key=(b0,g,qt)
                        E[key]=max(E.get(key,-10**9),dist[nd])
                    else: tB[nd[1]]=dist[nd]
                else: tD.add(nd[1])
            # pairs consumed on useful paths have to lie in AG'
            for nd,out in succ.items():
                if nd[0]=='B' and nd in useful and not M.rgt(nd[1][2],nd[1][3]):
                    for x,w in out:
                        if x in useful:
                            a=(M.nxt(nd[1][2],nd[1][3]),x[1][2])
                            if not al(AG,nd[1][5],a): raise Fail('G not closed')
        return sorted(tI.items()),sorted(tB.items()),sorted(tD),sorted(E.items())
    C['tI'],C['tB'],C['tD'],C['eI']=td(C['agI'],C['adI'],(0,1))
    C['uI'],C['uB'],C['uD'],C['eB']=td(C['agB'],C['adB'],(0,))
    return C,M

# ---- polynomials as in Poly.lean ----
def q_eval(q,l,k): a20,a11,a02,a10,a01,a00=q; return a20*l*l+a11*l*k+a02*k*k+a10*l+a01*k+a00
def q_expand(q,l0,uc,sh):
    a20,a11,a02,a10,a01,a00=q
    return (a20*uc*uc, a11*uc, a02, (2*a20*l0+a11*sh+a10)*uc, a11*l0+2*a02*sh+a01,
            a20*l0*l0+a11*l0*sh+a02*sh*sh+a10*l0+a01*sh+a00)
def q_sub(p,q): return tuple(x-y for x,y in zip(p,q))
def q_nonneg(q): return all(x>=0 for x in q)
def q_mono(q,lo): return q[0]>=0 and q[1]>=0 and q[0]*(2*lo)+q[3]>=0
def edge_parts(lo,ex,lo2,ex2,D_):
    l0=lo if ex else max(lo,lo2-D_); uc=0 if ex else 1
    l1=lo2 if ex2 else l0+D_; uc2=0 if ex2 else uc
    vac=ex and (lo+D_<lo2)
    return l0,uc,l1,uc2,vac
def edgeOK(D,q,q2,lo,ex,lo2,ex2,Dl,sh):
    l0,uc,l1,uc2,vac=edge_parts(lo,ex,lo2,ex2,Dl)
    R=list(q_sub(q_expand(q,l0,uc,sh),q_expand(q2,l1,uc2,0)))
    R[3]-=2*D*uc; R[5]-=2*D*l0
    return vac or ((ex2 or q_mono(q2,lo2)) and q_nonneg(R))
def zeroOK(q,qb,lo,ex):
    uc=0 if ex else 1
    R=q_sub(q_expand(q,lo,uc,0),q_expand(qb,lo,uc,0))
    return R[0]>=0 and R[3]>=0 and R[5]>=0
def tgtOK(D,q):
    R=q_expand(q,1,0,1)
    return R[2]<=2*D and R[4]<=12*D and R[5]<=18*D

# ---- potentials by linear programming ----
def potentials(C):
    N=C['N']; lo=C['lo']; ex=C['ex']
    used=sorted({g for (b,g,g2),_ in C['eI']}|{g2 for (b,g,g2),_ in C['eI']}|{g for (b,g,g2),_ in C['eB']}|{g2 for (b,g,g2),_ in C['eB']})
    blcls={g for (b,g,g2),_ in C['eB']}|{g2 for (b,g,g2),_ in C['eB']}
    var={}
    def V(n):
        if n not in var: var[n]=len(var)
        return var[n]
    # for each class: Wi as 6 linear expressions, Wb as 6 (coefficients of k are 0)
    def lin(name): return {V(name):Fr(1)}
    ZERO={}
    def Wi(g):
        if g==0 or g not in used: return [ZERO]*6
        if ex[g]: return [ZERO,ZERO,lin(('i',g,2)),ZERO,lin(('i',g,4)),lin(('i',g,5))]
        return [lin(('i',g,t)) for t in range(6)]
    def Wb(g):
        if g==0 or g not in used: return [ZERO]*6
        if g not in blcls:
            w=Wi(g); return [w[0],ZERO,ZERO,w[3],ZERO,w[5]]
        if ex[g]: return [ZERO,ZERO,ZERO,ZERO,ZERO,lin(('b',g,5))]
        return [lin(('b',g,0)),ZERO,ZERO,lin(('b',g,3)),ZERO,lin(('b',g,5))]
    def ladd(a,b,f=1):
        r=dict(a)
        for k,v in b.items(): r[k]=r.get(k,0)+f*v
        return r
    def lscale(a,f): return {k:v*f for k,v in a.items()}
    def lconst(x): return {'c':Fr(x)} if x else {}
    def expand(q,l0,uc,sh):
        a20,a11,a02,a10,a01,a00=q
        e3=ladd(ladd(lscale(a20,2*l0),lscale(a11,sh)),a10)
        e5=ladd(ladd(ladd(ladd(ladd(lscale(a20,l0*l0),lscale(a11,l0*sh)),lscale(a02,sh*sh)),lscale(a10,l0)),lscale(a01,sh)),a00)
        return [lscale(a20,uc*uc),lscale(a11,uc),a02,lscale(e3,uc),ladd(ladd(lscale(a11,l0),lscale(a02,2*sh)),a01),e5]
    cons=[]
    def nonneg(R):
        for e in R:
            if e: cons.append(e)
    def mono(q,l):
        cons.append(q[0]); cons.append(q[1]); cons.append(ladd(lscale(q[0],2*l),q[3]))
    DV=None
    def edge(q,q2,g,g2,Dl,sh):
        l0,uc,l1,uc2,vac=edge_parts(lo[g],ex[g],lo[g2],ex[g2],Dl)
        if vac: return
        if not ex[g2]: mono(q2,lo[g2])
        R=[ladd(x,y,-1) for x,y in zip(expand(q,l0,uc,sh),expand(q2,l1,uc2,0))]
        R[3]=ladd(R[3],lconst(-2*uc)); R[5]=ladd(R[5],lconst(-2*l0))
        nonneg(R)
    for (b,g,g2),Dl in C['eI']: edge(Wi(g),Wi(g2),g,g2,Dl,1)
    for (b,g,g2),Dl in C['eB']: edge(Wb(g),Wb(g2),g,g2,Dl,0)
    for g in range(N):
        uc=0 if ex[g] else 1
        R=[ladd(x,y,-1) for x,y in zip(expand(Wi(g),lo[g],uc,0),expand(Wb(g),lo[g],uc,0))]
        for t in (0,3,5):
            if R[t]: cons.append(R[t])
    starts=[C['dl'][0][pcode((0,r))] for r in (0,1) if C['adI'][0][pcode((0,r))]]
    # target condition (tgtOK) as a hard constraint:  R = expand(Wi(g),1,0,1);  R.a02<=2, R.a01<=12, R.a00<=18
    for g in starts:
        R=expand(Wi(g),1,0,1)
        for t,lim in ((2,2),(4,12),(5,18)):
            e=ladd(lconst(lim),R[t],-1)
            if any(k!='c' for k in e): cons.append(e)
            elif e.get('c',0)<0: raise Fail('target unreachable')
    n=len(var)
    if n==0:
        return 1,[(0,)*6]*N,[(0,)*6]*N
    cons=[e for e in cons if any(k!='c' for k in e)] + []   # constraints without variables are tested separately
    A=np.zeros((len(cons),n)); bnd=np.zeros(len(cons))
    for i,e in enumerate(cons):
        for k,v in e.items():
            if k=='c': bnd[i]+=float(v)
            else: A[i,k]=-float(v)
    cost=np.zeros(n)
    for g in starts:
        R=expand(Wi(g),1,0,0)      # polynomial in k at l=1
        for nn in range(1,13):
            for t,p in ((2,nn*nn),(4,nn),(5,1)):
                for k,v in R[t].items():
                    if k!='c': cost[k]+=float(v)*p/nn**2
    # regularisation: keep the sum of the absolute values small (auxiliary variables t_i >= |x_i|)
    A2=np.zeros((len(cons)+2*n,2*n)); b2=np.zeros(len(cons)+2*n)
    A2[:len(cons),:n]=A; b2[:len(cons)]=bnd
    for i in range(n):
        A2[len(cons)+2*i,i]=1; A2[len(cons)+2*i,n+i]=-1          #  x_i - t_i <= 0
        A2[len(cons)+2*i+1,i]=-1; A2[len(cons)+2*i+1,n+i]=-1     # -x_i - t_i <= 0
    cost2=np.concatenate([cost,np.full(n,1e-3)])
    res=linprog(cost2,A_ub=A2,b_ub=b2,bounds=[(-10**5,10**5)]*n+[(0,10**5)]*n,method='highs')
    if res.status!=0: raise Fail('LP: '+res.message[:60])
    names=[None]*n
    for name,i in var.items(): names[i]=name
    for dmax in (1,2,3,4,6,12,24,60):
        solv=[Fr(float(res.x[i])).limit_denominator(dmax) for i in range(n)]
        D=1
        for v in solv: D=lcm(D,v.denominator)
        def conc(q): return tuple(int(sum((solv[k]*v if k!='c' else v) for k,v in e.items())*D) for e in q)
        wi=[conc(Wi(g)) for g in range(N)]; wb=[conc(Wb(g)) for g in range(N)]
        if check_pots(C,D,wi,wb): return D,wi,wb
    # fallback: integer program (integral coefficients, fixed scaling D)
    from scipy.optimize import milp, LinearConstraint, Bounds
    for D in (1,2,3,4,6):
        # constraints: A x <= bnd, where the constants (from the -2l terms) have to be scaled by D
        Am=A2[:len(cons),:n]; bm=bnd*D
        rows=[Am]; lo_=[-np.inf*np.ones(len(cons))]; hi_=[bm]
        Afull=np.zeros((len(cons)+2*n,2*n)); Afull[:len(cons),:n]=Am
        hi=np.concatenate([bm,np.zeros(2*n)])
        for i in range(n):
            Afull[len(cons)+2*i,i]=1; Afull[len(cons)+2*i,n+i]=-1
            Afull[len(cons)+2*i+1,i]=-1; Afull[len(cons)+2*i+1,n+i]=-1
        costm=np.concatenate([cost*100,np.full(n,1.0)])
        r=milp(c=costm,constraints=LinearConstraint(Afull,-np.inf*np.ones(len(hi)),hi),integrality=np.concatenate([np.ones(n),np.zeros(n)]),
               bounds=Bounds(np.concatenate([np.full(n,-10**4),np.zeros(n)]),np.full(2*n,10**4)),options={'time_limit':30})
        if r.x is None: continue
        solv=[Fr(int(round(r.x[i])),D) for i in range(n)]
        def conc(q): return tuple(int(sum((solv[k]*v if k!='c' else v) for k,v in e.items())*D) for e in q)
        wi=[conc(Wi(g)) for g in range(N)]; wb=[conc(Wb(g)) for g in range(N)]
        if check_pots(C,D,wi,wb): return D,wi,wb
    raise Fail('potentials: exact test fails')
def check_pots(C,D,wi,wb):
    N=C['N']; lo=C['lo']; ex=C['ex']
    if wi[0]!=(0,)*6 or wb[0]!=(0,)*6: return False
    for (b,g,g2),Dl in C['eI']:
        if not edgeOK(D,wi[g],wi[g2],lo[g],ex[g],lo[g2],ex[g2],Dl,1): return False
    for (b,g,g2),Dl in C['eB']:
        if not edgeOK(D,wb[g],wb[g2],lo[g],ex[g],lo[g2],ex[g2],Dl,0): return False
    for g in range(N):
        if not zeroOK(wi[g],wb[g],lo[g],ex[g]): return False
    for r in (0,1):
        if C['adI'][0][pcode((0,r))] and not tgtOK(D,wi[C['dl'][0][pcode((0,r))]]): return False
    return True

# ---- exponential potentials as in Expo.lean:  (al*l+ga)*2^k + be*l + de ----
def edge2_parts(lo,ex,lo2,ex2,Dl):
    l0=lo if ex else max(lo,(lo2-Dl+1)//2); uc=0 if ex else 1
    l1=lo2 if ex2 else 2*l0+Dl; uc2=0 if ex2 else 2*uc
    vac=ex and (2*lo+Dl<lo2)
    return l0,uc,l1,uc2,vac
def edgeOK2(D,q,q2,lo,ex,lo2,ex2,Dl,sh):
    l0,uc,l1,uc2,vac=edge2_parts(lo,ex,lo2,ex2,Dl)
    al,ga,be,de=q; al2,ga2,be2,de2=q2
    A0=2**sh*(al*l0+ga)-(al2*l1+ga2); A1=2**sh*al*uc-al2*uc2
    B0=be*l0+de-(be2*l1+de2)-2*D*l0; B1=be*uc-be2*uc2-2*D*uc
    return vac or ((ex2 or (al2>=0 and al2+be2>=0)) and A0>=0 and A1>=0 and A0+B0>=0 and A1+B1>=0)
def zeroOK2(q,qb,lo,ex):
    R1=(q[0]+q[2])-(qb[0]+qb[2]); R0=(q[1]+q[3])-(qb[1]+qb[3])
    return (ex or R1>=0) and R1*lo+R0>=0
def tgtOK2(D,q): return q[0]+q[1]<=4*D and 2*(q[0]+q[1])+q[2]+q[3]<=6*D
def check_pots2(C,D,we,wb):
    N=C['N']; lo=C['lo']; ex=C['ex']
    if we[0]!=(0,)*4 or wb[0]!=(0,)*4: return False
    for (b,g,g2),Dl in C['eI']:
        if not edgeOK2(D,we[g],we[g2],lo[g],ex[g],lo[g2],ex[g2],Dl,1): return False
    for (b,g,g2),Dl in C['eB']:
        if not edgeOK2(D,wb[g],wb[g2],lo[g],ex[g],lo[g2],ex[g2],Dl,0): return False
    for g in range(N):
        if not zeroOK2(we[g],wb[g],lo[g],ex[g]): return False
    for r in (0,1):
        if C['adI'][0][pcode((0,r))] and not tgtOK2(D,we[C['dl'][0][pcode((0,r))]]): return False
    return True
def potentials2(C):
    N=C['N']; lo=C['lo']; ex=C['ex']
    used=sorted({g for (b,g,g2),_ in C['eI']}|{g2 for (b,g,g2),_ in C['eI']}|{g for (b,g,g2),_ in C['eB']}|{g2 for (b,g,g2),_ in C['eB']})
    blcls={g for (b,g,g2),_ in C['eB']}|{g2 for (b,g,g2),_ in C['eB']}
    var={}
    def V(n):
        if n not in var: var[n]=len(var)
        return var[n]
    Z={}
    def lin(name): return {V(name):Fr(1)}
    def We(g):
        if g==0 or g not in used: return [Z]*4
        return [lin(('e',g,t)) for t in range(4)]
    def Wb(g):
        if g==0 or g not in used: return [Z]*4
        if g not in blcls:
            w=We(g); return [Z,Z,ladd(w[0],w[2]),ladd(w[1],w[3])]
        return [Z,Z,lin(('b',g,2)),lin(('b',g,3))]
    def ladd(a,b,f=1):
        r=dict(a)
        for k,v in b.items(): r[k]=r.get(k,0)+f*v
        return r
    def lscale(a,f): return {k:v*f for k,v in a.items()}
    def lconst(x): return {'c':Fr(x)} if x else {}
    cons=[]
    def edge(q,q2,g,g2,Dl,sh):
        l0,uc,l1,uc2,vac=edge2_parts(lo[g],ex[g],lo[g2],ex[g2],Dl)
        if vac: return
        al,ga,be,de=q; al2,ga2,be2,de2=q2
        if not ex[g2]: cons.append(al2); cons.append(ladd(al2,be2))
        A0=ladd(lscale(ladd(lscale(al,l0),ga),2**sh),ladd(lscale(al2,l1),ga2),-1)
        A1=ladd(lscale(al,2**sh*uc),lscale(al2,uc2),-1)
        B0=ladd(ladd(ladd(lscale(be,l0),de),ladd(lscale(be2,l1),de2),-1),lconst(-2*l0))
        B1=ladd(ladd(lscale(be,uc),lscale(be2,uc2),-1),lconst(-2*uc))
        cons.extend([A0,A1,ladd(A0,B0),ladd(A1,B1)])
    for (b,g,g2),Dl in C['eI']: edge(We(g),We(g2),g,g2,Dl,1)
    for (b,g,g2),Dl in C['eB']: edge(Wb(g),Wb(g2),g,g2,Dl,0)
    for g in range(N):
        q=We(g); qb=Wb(g)
        R1=ladd(ladd(q[0],q[2]),ladd(qb[0],qb[2]),-1); R0=ladd(ladd(q[1],q[3]),ladd(qb[1],qb[3]),-1)
        if not ex[g]: cons.append(R1)
        cons.append(ladd(lscale(R1,lo[g]),R0))
    for r in (0,1):
        if C['adI'][0][pcode((0,r))]:
            q=We(C['dl'][0][pcode((0,r))])
            cons.append(ladd(lconst(4),ladd(q[0],q[1]),-1)); cons.append(ladd(ladd(lconst(6),lscale(ladd(q[0],q[1]),2),-1),ladd(q[2],q[3]),-1))
    for e in cons:
        if not any(k!='c' for k in e) and e.get('c',0)<0: raise Fail('constant constraint violated')
    cons=[e for e in cons if any(k!='c' for k in e)]
    n=len(var)
    if n==0: return 1,[(0,)*4]*N,[(0,)*4]*N
    A2=np.zeros((len(cons)+2*n,2*n)); b2=np.zeros(len(cons)+2*n)
    for i,e in enumerate(cons):
        for k,v in e.items():
            if k=='c': b2[i]+=float(v)
            else: A2[i,k]=-float(v)
    for i in range(n):
        A2[len(cons)+2*i,i]=1; A2[len(cons)+2*i,n+i]=-1
        A2[len(cons)+2*i+1,i]=-1; A2[len(cons)+2*i+1,n+i]=-1
    cost2=np.concatenate([np.zeros(n),np.ones(n)])
    res=linprog(cost2,A_ub=A2,b_ub=b2,bounds=[(-10**5,10**5)]*n+[(0,10**5)]*n,method='highs')
    if res.status!=0: raise Fail('LP2: '+res.message[:60])
    for dmax in (1,2,3,4,6,12):
        solv=[Fr(float(res.x[i])).limit_denominator(dmax) for i in range(n)]
        D=1
        for v in solv: D=lcm(D,v.denominator)
        def conc(q): return tuple(int(sum((solv[k]*v if k!='c' else v) for k,v in e.items())*D) for e in q)
        we=[conc(We(g)) for g in range(N)]; wb=[conc(Wb(g)) for g in range(N)]
        if check_pots2(C,D,we,wb): return D,we,wb
    raise Fail('exponential potentials: exact test fails')

# ---- independent copy of Cert.check ----
def check_cert(C,M):
    N=C['N']; dl=C['dl']; lo=C['lo']; ex=C['ex']
    def lenCheck():
        if not (N>0 and lo[0]==0 and ex[0]): return False
        for q in range(N):
            for a in range(4):
                t=dl[q][a]
                if not (t<N and lo[t]<=lo[q]+1 and ((not ex[t]) or (ex[q] and lo[t]==lo[q]+1))): return False
        return True
    def fwdCheck(A,bits,I,B):
        I=set(I); B=set(B)
        if not all((b,0,0) in I for b in bits): return False
        if not all((0,0)+x in B and (1,1)+x in B for x in I): return False
        for (e,s,sym,qa,qt) in B:
            if M.rgt(s,sym):
                a=pcode((e,M.nxt(s,sym)))
                if not (A[qa][a] and (M.wrt(s,sym),dl[qa][a],qt) in I): return False
            else:
                for rr in (0,1):
                    a=pcode((M.nxt(s,sym),rr))
                    if A[qt][a] and (e,rr,M.wrt(s,sym),qa,dl[qt][a]) not in B: return False
        return True
    def tdCheck(AG,AD,AG2,bits,c,tI,tB,tD,E):
        tId=dict(tI); tBd=dict(tB); tDs=set(tD); Ed=dict(E)
        ge=lambda d,k,x: k in d and x<=d[k]
        if not all(ge(tId,(b,b,0,0),0) for b in bits): return False
        for (b0,sym,g,qt),pi in tI:
            for (e,r) in PAIRS:
                a=pcode((e,r))
                if AG[g][a]:
                    k=(b0,r,e,sym,dl[g][a],qt)
                    if not (k in tDs or ge(tBd,k,pi-c)): return False
        for (b0,r,s,sym,g,qt),pi in tB:
            if M.rgt(s,sym):
                if M.nxt(s,sym)==r and not ge(tId,(b0,M.wrt(s,sym),g,qt),pi): return False
            else:
                for rr in (0,1):
                    a=pcode((M.nxt(s,sym),rr))
                    if AD[qt][a]:
                        k=(b0,r,rr,M.wrt(s,sym),g,dl[qt][a])
                        if not (k in tDs or (AG2[qt][a] and ge(tBd,k,pi+1))): return False
        for (b0,r,s,sym,g,qt) in tD:
            if M.rgt(s,sym):
                if M.nxt(s,sym)==r: return False
            else:
                for rr in (0,1):
                    a=pcode((M.nxt(s,sym),rr))
                    if AD[qt][a] and (b0,r,rr,M.wrt(s,sym),g,dl[qt][a]) not in tDs: return False
        for (b0,sym,g,qt),pi in tI:
            if not ge(Ed,(b0,g,qt),pi): return False
        return True
    ok=lenCheck()
    ok=ok and fwdCheck(C['adI'],(0,1),C['fI'],C['fB']) and fwdCheck(C['adB'],(0,),C['gI'],C['gB'])
    ok=ok and tdCheck(C['agI'],C['adI'],C['agI'],(0,1),C['c'],C['tI'],C['tB'],C['tD'],C['eI'])
    ok=ok and tdCheck(C['agB'],C['adB'],C['agB'],(0,),C['c'],C['uI'],C['uB'],C['uD'],C['eB'])
    ok=ok and all((not (C['agI'][q][a] and C['adB'][q][a])) or C['agB'][q][a] for q in range(N) for a in range(4))
    ok=ok and all((not C['adI'][0][pcode((0,r))]) or C['agI'][0][pcode((0,r))] for r in (0,1))
    if C['c']==1: ok=ok and C['D']>=1 and len(C['wi'])==N and len(C['wb'])==N and check_pots(C,C['D'],C['wi'],C['wb'])
    else: ok=ok and C['D']>=1 and len(C['we'])==N and len(C['wbE'])==N and check_pots2(C,C['D'],C['we'],C['wbE'])
    return ok

# ---- Lean output ----
def B(x): return 'true' if x else 'false'
def SB(st): return 'true' if st==0 else 'false'      # machine state: 0=U -> true
def lst(xs): return '['+', '.join(xs)+']'
def lean_cert(C):
    f=[]
    f.append('N := %d'%C['N'])
    f.append('dl := '+lst(lst(str(x) for x in row) for row in C['dl']))
    f.append('lo := '+lst(str(x) for x in C['lo']))
    f.append('ex := '+lst(B(x) for x in C['ex']))
    for nm in ('adI','adB','agI','agB'): f.append(nm+' := '+lst(lst(B(x) for x in row) for row in C[nm]))
    fi=lambda x: '(%s, %d, %d)'%(B(x[0]),x[1],x[2])
    fb=lambda x: '(%s, %s, %s, %d, %d)'%(SB(x[0]),SB(x[1]),B(x[2]),x[3],x[4])
    f.append('fI := '+lst(fi(x) for x in C['fI'])); f.append('fB := '+lst(fb(x) for x in C['fB']))
    f.append('gI := '+lst(fi(x) for x in C['gI'])); f.append('gB := '+lst(fb(x) for x in C['gB']))
    ti=lambda x: '((%s, %s, %d, %d), %d)'%(B(x[0][0]),B(x[0][1]),x[0][2],x[0][3],x[1])
    tbk=lambda k: '(%s, %s, %s, %s, %d, %d)'%(B(k[0]),SB(k[1]),SB(k[2]),B(k[3]),k[4],k[5])
    tb=lambda x: '(%s, %d)'%(tbk(x[0]),x[1])
    ee=lambda x: '((%s, %d, %d), %d)'%(B(x[0][0]),x[0][1],x[0][2],x[1])
    f.append('tI := '+lst(ti(x) for x in C['tI'])); f.append('tB := '+lst(tb(x) for x in C['tB']))
    f.append('tD := '+lst(tbk(x) for x in C['tD'])); f.append('eI := '+lst(ee(x) for x in C['eI']))
    f.append('uI := '+lst(ti(x) for x in C['uI'])); f.append('uB := '+lst(tb(x) for x in C['uB']))
    f.append('uD := '+lst(tbk(x) for x in C['uD'])); f.append('eB := '+lst(ee(x) for x in C['eB']))
    f.append('D := %d'%C['D'])
    qq=lambda q: '⟨'+', '.join(str(x) for x in q)+'⟩'
    if C['c']==1: f.append('wi := '+lst(qq(q) for q in C['wi'])); f.append('wb := '+lst(qq(q) for q in C['wb']))
    else: f.append('we := '+lst(qq(q) for q in C['we'])); f.append('wbE := '+lst(qq(q) for q in C['wbE']))
    return '{ '+',\n    '.join(f)+' }'

def make(num,J,j,c=1):
    C,M=build(num,J,j,c)
    if c==1:
        D,wi,wb=potentials(C); C['D']=D; C['wi']=wi; C['wb']=wb
    else:
        D,we,wb=potentials2(C); C['D']=D; C['we']=we; C['wbE']=wb
    if not check_cert(C,M): raise Fail('certificate fails the Python test')
    return C

if __name__=='__main__':
    for a in sys.argv[1:]:
        p=[int(x) for x in a.split(',')]
        num,J,j=p[:3]; c=p[3] if len(p)>3 else 1
        C=make(num,J,j,c)
        print('-- machine %d  (J=%d, j=%d, c=%d)  N=%d  nodes: %d'%(num,J,j,c,C['N'],len(C['fI'])+len(C['fB'])+len(C['gI'])+len(C['gB'])+len(C['tI'])+len(C['tB'])+len(C['tD'])+len(C['uI'])+len(C['uB'])+len(C['uD'])))
        print(lean_cert(C))
