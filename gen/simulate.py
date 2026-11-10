#!/usr/bin/env python3
"""Plain simulator for Wolfram's 2-state 2-symbol Turing machines (numbering 0..4095), independent of Lean.

Set-up as in OEIS A392245 / A393317: the binary digits of the input are on the tape, the head starts
on the least significant digit in state U; the machine halts as soon as the head moves right from the
start cell.  The halting time is the number of steps.

  python3 simulate.py          a few spot checks and A393317(1..8) by exhaustive search
"""
import sys
def rule(num):
    d=[(num//8**i)%8 for i in (3,2,1,0)]            # cases (U,1), (U,0), (D,1), (D,0)
    cases=[(1,1),(1,0),(2,1),(2,0)]
    return {c:((x//4)+1,(x//2)%2,1 if x%2 else -1) for c,x in zip(cases,d)}   # (new state, new symbol, direction: +1 = right)
def run(num,n,maxsteps=10**7):
    r=rule(num); tape={}; i=0
    while n: tape[i]=n&1; n>>=1; i+=1               # position i = digit of weight 2^i (left = larger)
    pos=0; st=1; t=0
    while t<maxsteps:
        ns,nc,dr=r[(st,tape.get(pos,0))]
        tape[pos]=nc; st=ns; pos-=dr; t+=1          # right = pos-1
        if pos<0: return t, sum(v<<k for k,v in tape.items())
    return None,None
if __name__=='__main__':
    print('machine 1285, output (A392245):',[run(1285,n)[1] for n in range(1,17)])
    print('machine 3626, halting time (A393210):',[run(3626,n)[0] for n in range(1,33)])
    for m in (378,1351,1447):
        print('machine',m,'on 2^n-1:',[run(m,2**n-1)[0] for n in range(1,13)])
    print('2^(n+2)-3  :',[2**(n+2)-3 for n in range(1,13)]); print('2(n+2)^2-1 :',[2*(n+2)**2-1 for n in range(1,13)])
    # A393317: maximum over all 4096 machines and all n-bit inputs (halting runs only; by the theorem
    # no halting run on an input below 2^n is longer than max(2(n+2)^2-1, 2^(n+2)-3), so the cap is safe)
    for n in range(1,9):
        best=(0,None,None)
        for m in range(4096):
            for x in range(2**(n-1),2**n):
                t,_=run(m,x,maxsteps=5000)
                if t and t>best[0]: best=(t,m,x)
        print('n=%d max=%d (machine %s, input %s)'%(n,best[0],best[1],best[2]),flush=True)
