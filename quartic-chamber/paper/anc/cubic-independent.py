"""Independent cubic-chamber audit, using Python integers and rational arithmetic."""

from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from math import comb


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def compositions_inserted(n):
    """Each labeled list is produced uniquely by reinserting its largest label."""
    if n == 0:
        yield ()
        return
    for sizes in compositions_inserted(n - 1):
        for k in range(len(sizes)):
            yield sizes[:k] + (sizes[k] + 1,) + sizes[k+1:]
        for k in range(len(sizes) + 1):
            yield sizes[:k] + (1,) + sizes[k:]


def rows_by_short_segments(j):
    """n! times the EGF coefficients of L^h/(1-S)^(h+1), with all orders 0..4."""
    top = 4 * j
    binom = [[comb(n, r) for r in range(n + 1)] for n in range(top + 1)]
    short = [1]
    for n in range(1, top + 1):
        short.append(sum(binom[n][r] * short[n-r] for r in range(1, min(n+1,j))))
    large_then_short = [
        sum(binom[n][r] * short[n-r] for r in range(j, n+1)) for n in range(top+1)
    ]
    coefficients = [short]
    for h in range(1, 5):
        before = coefficients[-1]
        coefficients.append([
            sum(binom[n][r] * large_then_short[r] * before[n-r]
                for r in range(j, n-(h-1)*j+1))
            for n in range(top+1)
        ])
    return [[coefficients[h][n] for h in range(1+n//j)] for n in range(top+1)]


def bezoutian(upper, lower):
    """Coefficient matrix of (upper(x)lower(y)-upper(y)lower(x))/(x-y)."""
    d = len(upper)-1
    p = lower + [0]*(len(upper)-len(lower))
    matrix = [[0]*d for _ in range(d)]
    for i in range(1, d+1):
        for k in range(i):
            value = upper[i]*p[k] - upper[k]*p[i]
            for h in range(i-k):
                matrix[i-1-h][k+h] += value
    return matrix


def positive_bareiss_pivots(matrix):
    """Sylvester criterion using exact fraction-free elimination."""
    work = [row[:] for row in matrix]
    d = len(work)
    previous, pivots = 1, []
    for k in range(d):
        pivot = work[k][k]
        require(pivot > 0, ("nonpositive leading principal minor", k))
        pivots.append(pivot)
        for i in range(k+1, d):
            for j in range(k+1, d):
                quotient, remainder = divmod(pivot*work[i][j]-work[i][k]*work[k][j], previous)
                require(remainder == 0, ("nonexact elimination", i, j))
                work[i][j] = quotient
        previous = pivot
    return pivots


def finite():
    literal = {
        j: [[0]*(1+n//j) for n in range(9)]
        for j in range(2, 5)
    }
    for n in range(9):
        for sizes in compositions_inserted(n):
            for j, table in literal.items():
                table[n][sum(s>=j for s in sizes)] += 1
    witness = sha256()
    pairs = jumps = 0
    for j in range(2, 64):
        rows = rows_by_short_segments(j)
        if j in literal:
            require(rows[:9] == literal[j], ("literal ordered lists", j))
        for n in range(3*j, 4*j):
            p, q = rows[n], rows[n+1]
            jump = n+1 == 4*j
            require(len(p) == 4 and len(q) == 4+jump and min(p+q) > 0, (j,n))
            pivots = positive_bareiss_pivots(bezoutian(q,p))
            witness.update(f"{j},{n}:".encode())
            for value in p+q+pivots:
                size = (value.bit_length()+7)//8
                witness.update(size.to_bytes(2, "big")+value.to_bytes(size, "big"))
            pairs += 1
            jumps += int(jump)
    require(pairs == 2015 and jumps == 62, "coverage")
    return dict(cutoffs=[2,63], pairs=pairs, quartic_entries=jumps, literal_max_n=8,
                rows_and_bezout_pivots_sha256=witness.hexdigest())


def coeff_bounds(q_lo, q_hi, u_lo, u_hi):
    """Endpoint substitutions after normalizing by j, j^2 or j^3."""
    q, r, u, v = q_lo, q_hi, u_lo, u_hi
    beta = F("0.69")*q/(1+q)
    M = 1/(1-F("0.70")*r)
    eta = r/100
    linear_lo, linear_hi = 2+u, 2+v
    square_lo, square_hi = 1+u, 1+v
    a = (linear_lo*(1+beta) + F("1.68")*q - eta*r,
         M*(linear_hi+F("1.72")*r)+eta*r)
    b = (square_lo**2*(F(1,2)+beta) + F("2.52")*square_lo*q + 2*q*q-eta*r*r,
         M*M*(square_hi**2/2 + F("2.55")*square_hi*r + F("2.86")*r*r)+eta*r*r)
    d = (1+beta-3*eta, 2*M-1-beta+3*eta)
    e = (square_lo*(1+2*beta)+3*q-2*eta*r,
         M*M*(square_hi+F("3.54")*r)+2*eta*r)
    f = (u*u/2+F("3.87")*u*q+6*q*q-2*eta*r*r,
         M**3*(v*v/2+F("3.90")*v*r+F("7.30")*r*r)+2*eta*r*r)
    c_upper = M**3*(v**3/6+F("1.70")*v*v*r+F("4.84")*v*r*r+F("3.89")*r**3) + eta*r**3
    return a,b,d,e,f,c_upper,M**3*(v+3*r)/3


def box_margins(bounds, correction):
    a,b,d,e,f,c_hi,cf_ordinary = bounds
    d_lo = d[0]-correction
    e_lo = e[0]-correction*a[1]
    f_lo = f[0]-correction*b[1]
    require(min(a[0],b[0],d_lo,e_lo)>0, "box positivity")
    if correction:
        require(f_lo>0, "quartic corrected f")
    cf = c_hi/f_lo if correction else cf_ordinary
    H = d[1]*f[1]/(e_lo*e_lo)
    require(0 <= H < F(4,25), "separator discriminant")
    V = F(5,4)
    for _ in range(5):
        # At the actual near root, v (1-hv)=1. Positive denominator enables
        # monotone substitution of H >= h and V >= v.
        require(H*V < 1, "near-root reciprocal denominator")
        new = 1/(1-H*V)
        require(1 <= new <= V, "near-root iterates")
        V = new
    first = a[0]*d_lo-e[1]
    near = first*e_lo-V*d[1]*max(F(0),b[1]*d[1]-f_lo)
    far = 1-(V*a[1]*f[1]/(b[0]*e_lo)+cf*e[1]/b[0])
    return F(4,25)-H, first, near, far


def decimal_floor(x):
    numerator = x.numerator * 10**6 // x.denominator
    return f"{numerator//10**6}.{numerator%10**6:06d}"


def boxes():
    minima = []
    count = quartic = 0
    jump_cells = []
    for k,l in product(range(6),range(128)):
        q,r = F(k,384),F(k+1,384)
        u,v = F(l,128),F(l+1,128)
        values = coeff_bounds(q,r,u,v)
        corrections = [F(0)]
        # The Minkowski sum of the two closed intervals must contain 1.
        if u+q <= 1 <= v+r:
            corrections.append(50*r**3)
            jump_cells.append((k,l))
        for correction in corrections:
            margins = box_margins(values, correction)
            require(all(x>0 for x in margins), (k,l,correction))
            minima = [min(x,y) for x,y in zip(minima,margins)] if minima else list(margins)
            count += 1
            quartic += bool(correction)
    require(count == 777 and quartic == 9, "box coverage")
    for j in range(64, 4097):
        # Integer boundary guard in addition to closed real-cell coverage.
        require(any(F(k,384)<=F(1,j)<=F(k+1,384)
                    and F(l,128)<=F(j-1,j)<=F(l+1,128)
                    for k,l in jump_cells), ("quartic coverage", j))
    return dict(total=count, ordinary=count-quartic, quartic=quartic,
                lower_bounds=[decimal_floor(x) for x in minima], quartic_cells=jump_cells)


def rational_constants():
    rho_lo, rho_hi = F(69,100), F(7,10)
    term_error = F(1,1024)+rho_hi/64 + F(11,6)*rho_hi**2/16 + rho_hi**3/2
    require(term_error<F(".24"), "K4 coefficient error")
    require(F(11,6)+3*rho_lo+F(11,6)*rho_lo**2>0, "K4 lower coefficient")
    require(F(11,6)+3*rho_hi+F(11,6)*rho_hi**2<F("4.84"), "K4 linear upper")
    require(1+2*rho_hi+F(11,6)*rho_hi**2+rho_hi**3+F(".24")<F("3.89"), "K4 constant upper")
    require(F(5,2)+2*rho_lo>=F("3.87") and F(5,2)+2*rho_hi<=F("3.90"), "K4 increments")
    require(3+4*rho_lo+F(11,6)*rho_lo**2-F(".48")>6, "K4 increment lower")
    require(3+4*rho_hi+F(11,6)*rho_hi**2+F(".48")<F("7.30"), "K4 increment upper")
    eta = F(1,6400)
    ratio_coefficients = [18-6*eta-3*(F("3.89")+eta),
                          3*F("3.87")+6-2*eta-3*F("4.84"),
                          3*F(1,2)+F("3.87")-3*F("1.70")]
    require(min(ratio_coefficients)>0, "ordinary c/f comparison")
    require(F(63,64)**3/6-eta/F(64)**3>F(6,50), "quartic old cubic lower")
    require((2*rho_hi)**5/(1-F(1,2*8**256))<6, "quartic new leading coefficient")
    require(200*100*107**3<8**100 and F(101,100)**4<8, "normalization geometric bound")
    return dict(k4_error_upper=str(term_error),
                c_over_f_polynomial=[str(x) for x in ratio_coefficients])


if __name__ == "__main__":
    print(json.dumps(dict(constants=rational_constants(), boxes=boxes(), finite=finite()), indent=2))
