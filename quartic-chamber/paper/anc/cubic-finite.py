"""All cubic pairs below the explicit analytic threshold, by literal labeled recurrence and EGF."""
from hashlib import sha256
from math import comb, gcd
from pathlib import Path
import json

def primitive(poly):
    while poly and poly[-1]==0: poly.pop()
    g=gcd(*poly)
    return [v//g for v in poly]

def nrem(p,q):
    assert q[-1]>0
    while len(p)>=len(q):
        a=p[-1]
        off=len(p)-len(q)
        p=[v*q[-1] for v in p]
        for i,w in enumerate(q): p[i+off]-=a*w
        p=primitive(p)
    return [-v for v in p]

def checks(J=64):
    top=4*(J-1)
    choose=[[comb(n,r) for r in range(n+1)] for n in range(top+1)]
    bell=[1]
    for n in range(1,top+1):
        bell.append(sum(v*bell[n-r] for r,v in enumerate(choose[n]) if r))
    witness=sha256(); pairs=jumps=0
    for j in range(2,J):
        N=4*j
        rows=[[1]]
        for n in range(1,N+1):
            row=[0]*(n//j+1)
            for s in range(1,n+1):
                b=choose[n][s]
                off=int(s>=j)
                for h,v in enumerate(rows[n-s]): row[h+off]+=b*v
            rows.append(row)
        mark=[sum(choose[n][s]*bell[n-s] for s in range(j,n+1)) for n in range(N+1)]
        moments=[bell[:N+1]]
        for h in range(1,5):
            old=moments[-1]
            moments.append([sum(choose[n][s]*old[n-s]*mark[s] for s in range(j,n+1))
                            for n in range(N+1)])
        for n in range(3*j,N+1):
            for h in range(5):
                assert moments[h][n]==sum(comb(i,h)*v for i,v in enumerate(rows[n]) if i>=h)
        for n in range(3*j,N):
            p=rows[n];q=rows[n+1]
            assert len(p)==4 and len(q)==4+int(n+1==N) and min(p+q)>0
            R=nrem(q,p); assert len(R)==3 and R[-1]>0
            S=nrem(p,R); assert len(S)==2 and S[-1]>0
            T=nrem(R,S); assert len(T)==1 and T[0]>0
            for poly in [p,q,R,S,T]:
                for a in poly:
                    size=(abs(a).bit_length()+7)//8
                    witness.update(bytes([int(a<0)])+size.to_bytes(4,'big')+abs(a).to_bytes(size,'big'))
            pairs+=1;jumps+=int(n+1==N)
    return dict(first=2,last=J-1,pairs=pairs,quartic_jumps=jumps,sha256=witness.hexdigest())

if __name__=='__main__': print(json.dumps(checks(),indent=2))
