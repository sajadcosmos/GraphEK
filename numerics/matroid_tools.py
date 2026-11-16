import math
from fractions import Fraction

def qint(k, q): return (q**k - 1)//(q - 1)
def pg_f(r, q):
    n = qint(r, q); f = [1]
    for k in range(r): f.append(f[-1]*(n - qint(k, q))//(k+1))
    return f
def ag_f(r, q):
    n = q**(r-1); f = [1, n]
    for k in range(1, r): f.append(f[-1]*(n - q**(k-1))//(k+1))
    return f

def forests_Kp(p):
    U = [Fraction(0)] + [Fraction(j**(j-2) if j>=2 else 1, math.factorial(j)) for j in range(1, p+1)]
    # number of forests with c trees on p vertices = p! [x^p] U^c / c!
    res = []
    powc = [Fraction(1)] + [Fraction(0)]*p
    out = {}
    for c in range(1, p+1):
        new = [Fraction(0)]*(p+1)
        for i, a in enumerate(powc):
            if a == 0: continue
            for j in range(1, p+1-i): new[i+j] += a*U[j]
        powc = new
        out[c] = powc[p]*math.factorial(p)/math.factorial(c)
    # edges k = p - c
    return [int(out[p-k]) for k in range(0, p)]
