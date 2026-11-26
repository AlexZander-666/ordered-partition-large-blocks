"""Count by the last labeled block; independently enumerate ordered partitions through size 7."""
from collections import Counter
from fractions import Fraction
from math import comb
import json

def rows(j, top):
    result = [[1]]
    for n in range(1,top+1):
        row = [0]*(1+n//j)
        for size in range(1,n+1):
            for degree, value in enumerate(result[n-size]):
                row[degree+int(size>=j)] += comb(n,size)*value
        result.append(row)
    return result

def ordered_partitions(n):
    if n==0:
        yield ()
        return
    for parent in ordered_partitions(n-1):
        for pos in range(len(parent)+1):
            yield parent[:pos]+((n,),)+parent[pos:]
        for pos,block in enumerate(parent):
            yield parent[:pos]+(block+(n,),)+parent[pos+1:]

def run():
    direct = 0
    for n in range(8):
        dist = {j:Counter() for j in range(2,n+2)}
        for part in ordered_partitions(n):
            direct += 1
            for j,v in dist.items():
                v[sum(len(block)>=j for block in part)] += 1
        for j,v in dist.items():
            assert rows(j,n)[-1] == [v[d] for d in range(1+n//j)]
    assert rows(3,6)[3:]==[[12,1],[66,9],[450,91],[3690,973,20]]
    affine = jumps = 0
    for j in range(2,65):
        seq=rows(j,2*j)
        for n in range(j,2*j-1):
            u,v = seq[n]
            a,b = seq[n+1]
            assert a*v < u*b
            affine += 1
        u,v = seq[-2]
        a,b,c = seq[-1]
        assert c==comb(2*j,j)
        assert a*v*v-b*u*v+c*u*u<0
        mu0=Fraction(v,u+v)
        mu1=Fraction(b+2*c,a+b+c)
        assert mu0*(mu1-mu0)>Fraction(c,a+b+c)
        jumps += 1
    print(json.dumps(dict(j_range=[2,64],jump_pairs=jumps,affine_pairs=affine,
          direct_labeled_ordered_partitions=direct, direct_max_n=7,
          integer_witness="a*v^2-b*u*v+c*u^2 < 0"),indent=2))

if __name__=="__main__":
    run()
