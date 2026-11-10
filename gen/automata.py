# Automata on crossing sequences ("histories") and the least fixed points used for the certificates.
#
#   state of the automaton = (exact?, tuple): the exact prefix of the history up to length J,
#                            afterwards the first J pairs and the last j pairs
#   lfpD : forward invariant  (which histories a tape part can produce at all), least fixed point
#   lfpG : top-down invariant (which histories arise below the initial history [(U, r)]), least fixed point
#
# Machine states: 0 = U (start state), 1 = D.  A pair (e, r) = (state on entry, state on exit).
import sys
sys.setrecursionlimit(1000000)
class Fail(Exception): pass
def rule(num):
    d=[(num//8**i)%8 for i in (3,2,1,0)]; r={}
    for (st,sym),x in zip([(0,1),(0,0),(1,1),(1,0)],d): r[(st,sym)]=(x//4,(x//2)%2,x%2)
    return r
Q0=(True,())
def make_delta(J,j):
    # state: (True, t) as long as len(t)<=J (exact); otherwise (False, first J pairs, last j pairs)
    def delta(q,a):
        if q[0]:
            t2=q[1]+(a,)
            if len(t2)<=J: return (True,t2)
            return (False,t2[:J],t2[len(t2)-j:] if j>0 else ())
        t2=q[2]+(a,)
        return (False,q[1],t2[len(t2)-j:] if j>0 else ())
    return delta

def product(tr,delta,Ah,bits,Ad,c):
    """Product graph. Nodes: ('I',g,sym,q) / ('B',g,r,s,sym,q). Returns edges[node]=[(node2, weight, transition of h' or None)]"""
    edges={}; todo=[('I',Q0,b,Q0) for b in bits]
    while todo:
        nd=todo.pop()
        if nd in edges: continue
        out=[]
        if nd[0]=='I':
            _,g,sym,q=nd
            for a in ((0,0),(0,1),(1,0),(1,1)):
                if (g,a) in Ah: out.append((('B',delta(g,a),a[1],a[0],sym,q),-c,None))
        else:
            _,g,r,s,sym,q=nd
            s2,w,d=tr[(s,sym)]
            if d:
                if s2==r: out.append((('I',g,w,q),0,None))
            else:
                for rr in (0,1):
                    a=(s2,rr)
                    if (q,a) in Ad: out.append((('B',g,r,rr,w,delta(q,a)),1,(q,a)))
        edges[nd]=out
        if len(edges)>40000: raise Fail('product too large')
        for x in out: todo.append(x[0])
    # useful nodes: those that can reach an I-node
    useful={nd for nd in edges if nd[0]=='I'}
    ch=True
    while ch:
        ch=False
        for nd,out in edges.items():
            if nd not in useful and any(x[0] in useful for x in out): useful.add(nd); ch=True
    return {nd:[x for x in out if x[0] in useful] for nd,out in edges.items() if nd in useful}

def lfpD(tr,delta,bits):
    A=set()
    while True:
        # forward: h' is restricted by A, h (at the cell) is arbitrary -> every exit has to be allowed
        changed=False
        S=set(); todo=[(b,Q0,Q0) for b in bits]
        while todo:
            ps=todo.pop()
            if ps in S: continue
            S.add(ps); sym,qa,qt=ps
            for e in (0,1):
                seen=set(); st=[(e,sym,qt)]
                while st:
                    nd=st.pop()
                    if nd in seen: continue
                    seen.add(nd); s,sy,q=nd
                    s2,w,d=tr[(s,sy)]
                    if d:
                        a=(e,s2)
                        if (qa,a) not in A: A.add((qa,a)); changed=True
                        todo.append((w,delta(qa,a),q))
                    else:
                        for rr in (0,1):
                            a=(s2,rr)
                            if (q,a) in A: st.append((rr,w,delta(q,a)))
        if not changed: return A

def lfpG(tr,delta,init,bits,Ad,c):
    """init: set of transitions allowed at the start; closure downwards (h -> h')"""
    A=set(init)
    while True:
        P=product(tr,delta,A,bits,Ad,c)
        new=set()
        for nd,out in P.items():
            for nd2,w,t in out:
                if t is not None and t not in A: new.add(t)
        if not new: return A,P
        A|=new
        if len(A)>1500: raise Fail('G too large')

def reach(A,delta):
    R=set(); todo=[Q0]; seen={Q0}
    while todo:
        q=todo.pop()
        for a in ((0,0),(0,1),(1,0),(1,1)):
            if (q,a) in A:
                R.add((q,a)); q2=delta(q,a)
                if q2 not in seen: seen.add(q2); todo.append(q2)
    return R
