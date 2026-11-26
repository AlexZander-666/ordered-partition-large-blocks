"""Rational interval certificate. Inputs are only the inequalities in proof.md."""
from fractions import Fraction as F
from hashlib import sha256
import json


def check(J=64, u_cells=128, q_cells=6):
    minima = [None]*4
    total = jumps = 0
    records = sha256()
    for iq in range(q_cells):
        q=F(iq,J*q_cells)
        r=F(iq+1,J*q_cells)
        beta=F(69,100)*q/(1+q)
        M=1/(1-F(7,10)*r)
        eta=r/100
        d_upper=1+2*(M-1)+3*eta-beta
        d_lower=1+beta-3*eta
        for iu in range(u_cells):
            u=F(iu,u_cells)
            v=F(iu+1,u_cells)
            s=1+u
            S=1+v
            a=2+u+F(168,100)*q+beta*(2+u)-eta*r
            A=M*(2+v+F(172,100)*r)+eta*r
            b=s*s/2+F(252,100)*s*q+2*q*q+beta*s*s-eta*r*r
            B=M**2*(S*S/2+F(255,100)*S*r+F(286,100)*r*r)+eta*r*r
            e=s+3*q+2*beta*s-2*eta*r
            E=M**2*(S+F(354,100)*r)+2*eta*r
            f=u*u/2+F(387,100)*u*q+6*q*q-2*eta*r*r
            Fmax=M**3*(v*v/2+F(390,100)*v*r+F(730,100)*r*r)+2*eta*r*r
            for jump in [False,True]:
                if jump and (u>1-q or v<1-r):
                    continue
                correction=50*r**3 if jump else 0
                dd=d_lower-correction
                ee=e-correction*A
                ff=f-correction*B
                assert min(dd,ee,a,b,d_upper,E,Fmax)>0
                if jump:
                    C=M**3*(v**3/6+F(17,10)*v*v*r+F(484,100)*v*r*r+F(389,100)*r**3)+eta*r**3
                    assert ff>0
                    c_over_f=C/ff
                else:
                    c_over_f=M**3*(v+3*r)/3
                hmax=d_upper*Fmax/ee**2
                assert 0<=hmax<F(4,25)
                V=F(5,4)
                for _ in range(5):
                    assert hmax*V<1
                    V=1/(1-hmax*V)
                ad_minus_e=a*dd-E
                assert ad_minus_e>0
                near=ad_minus_e*ee - V*d_upper*max(0,B*d_upper-ff)
                far=1-V*A*Fmax/(b*ee)-c_over_f*E/b
                values=[F(4,25)-hmax,ad_minus_e,near,far]
                assert all(x>y for x,y in zip(values,map(F,['.021','.964','.035','.136'])))
                minima=[w if old is None else min(w,old) for old,w in zip(minima,values)]
                records.update(('|'.join(map(str,[iq,iu,jump,*values]))+'\n').encode())
                total+=1
                jumps+=int(jump)
    # Decimal lower bounds are rounded *down* with integer arithmetic.
    lower=[f'{(x*10**6).__floor__()/10**6:.6f}' for x in minima]
    return dict(J=J,u_cells=u_cells,q_cells=q_cells,ordinary=total-jumps,
                possible_quartic=jumps,total=total,lower_bounds=lower,certificate_sha256=records.hexdigest())


if __name__=='__main__':
    print(json.dumps(check(),indent=2))
