"""Exact two-track certificate for the entire finite remainder 2 <= j < 50."""
from math import comb
from hashlib import sha256

TOP = 147
binom = [[comb(n, r) for r in range(n + 1)] for n in range(TOP + 1)]
bell = [1]
for n in range(1, TOP + 1):
    bell.append(sum(binom[n][r] * bell[n-r] for r in range(1, n+1)))

def product(a, b, top):
    return [sum(binom[n][i] * a[i] * b[n-i] for i in range(n+1))
            for n in range(top+1)]

def raw_rows(j, top):
    rows = [[1]]
    for n in range(1, top+1):
        row = [0] * (1+n//j)
        for r in range(1, n+1):
            for d, value in enumerate(rows[n-r]):
                row[d + (r >= j)] += binom[n][r] * value
        rows.append(row)
    return rows

pairs = jumps = 0
hashes = sha256()
for j in range(2, 50):
    top = 3*j
    rows = raw_rows(j, top)
    marked_block = [int(s >= j) for s in range(top+1)]
    tail = product(marked_block, bell, top)
    moments = [bell[:top+1]]
    for h in range(3):
        moments.append(product(moments[-1], tail, top))
    for n in range(2*j, top+1):
        for h in range(4):
            assert sum(comb(d,h) * v for d,v in enumerate(rows[n]) if d >= h) == moments[h][n]
    for n in range(2*j, top):
        a,b,c = rows[n]
        d,e,f,*last = rows[n+1]
        g = last[0] if last else 0
        assert (g > 0) == (n+1 == top)
        u = c*c*e-c*g*a-(c*f-g*b)*b
        v = c*c*d-(c*f-g*b)*a
        sign = a*u*u-b*u*v+c*v*v
        assert u < 0 and sign < 0 and min(a,b,c,d,e,f)>0
        hashes.update(f'{j},{n},{u},{v},{sign}\n'.encode())
        pairs += 1
        jumps += int(g > 0)
print('PASS', pairs,'original adjacent pairs including',jumps,'quadratic-to-cubic jumps')
print('Two independent counts: last-block recurrence; marked ordered subsequence EGF.')
print('SHA256 of deterministically ordered integer witnesses',hashes.hexdigest())
