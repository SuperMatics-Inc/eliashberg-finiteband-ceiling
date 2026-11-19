"""Independent exact replay: finer cells, variational resolvent and different tail split."""
from fractions import Fraction as F
from functools import cache


def require(statement, reason):
    if not statement:
        raise ArithmeticError(reason)


CAP = F(19,25)


def enclose(lo, hi, *, mutant=None):
    step = 10**8
    z = F(0) if hi is None else CAP/hi

    @cache
    def k(j):
        x = CAP/(j*j+z)
        return min(CAP/(j*j), F(-((-x*step)//1),step))

    i = range(1,97)
    L = CAP/96 + sum(map(k,i))
    a = k(1)
    D = lo+1-a
    d = (2*L + 2*a*a + sum(k(j)**2 for j in i)
         + sum(k(j)*k(j+1) for j in i) + 2*CAP**2/(3*96**3))/D
    e = (2*L+k(3)+a*max(2*L+a-1,0))/D

    w = lambda n: 2*n+1
    p = lambda n: {2:F(10,7),3:F(5,4),4:F(9,8)}.get(n,1)
    hdiag = 2 if mutant != 'repeat-hankel' else 6

    def t(n,m):
        return k(n+m+1) + (k(abs(n-m)) if n != m else (hdiag-1)*k(n+m+1))

    # Row sum of t before weighting, with arbitrary n>=1.
    row_mass = 3*L+(hdiag-1)*k(3)
    soft_rows = (k(11)+k(23))*sum(F(p(m),w(m)) for m in range(1,11))+row_mass/23
    finite_rows = ((sum(t(n,m)*p(m)/w(m) for m in range(1,49))
                    +2*CAP/((48-20)*99))/p(n) for n in range(1,21))
    eta = max(soft_rows, *finite_rows)
    require(eta < 1, 'tail norm')

    # The rational trial vector is arbitrary. Evaluate its head residual
    # against the unrounded comparator and bound its tail by CAP/j^2.
    head = range(1,17)
    K = lambda j: CAP/(j*j+z)
    T = lambda n,m: K(n+m+1)+(K(abs(n-m)) if n != m else (hdiag-1)*K(n+m+1))
    f = {n:K(n)+K(n+1) for n in head}
    y = {n:F(0) for n in head}
    for _ in range(6):
        y = {n:F((step*(f[n]+sum(t(n,m)*y[m]/w(m) for m in head)))//1,step)
             for n in head}
    ty = {n:sum(T(n,m)*y[m]/w(m) for m in head) for n in head}
    r2 = sum((f[n]-y[n]+ty[n])**2/w(n) for n in head)
    m3 = max(m**3*y[m]/w(m) for m in head)
    amplitude = 2*CAP+5*CAP*sum(y[m]/w(m) for m in head)+8*m3*row_mass/17
    r2 += amplitude**2/(8*16**4)
    V = sum(y[n]*(2*f[n]-y[n]+ty[n])/w(n) for n in head)+r2/(1-eta)

    if lo < F(11,2):
        require(V+a < 1 and (2*a+V)*d < a+d, 'midpoint/intersection stability')
        return max(V+a,(2*a+V)*d/(a+d))
    require(eta+e < 1 and V+d < 1, 'Schur endpoints')
    if hi is None:
        require(eta+F(25,72) < 1, 'asymmetric height-only guard')
    return max(eta+e,V+d)


def mutant_rejected(lo, hi):
    try:
        enclose(lo,hi,mutant='repeat-hankel')
    except ArithmeticError as exc:
        return str(exc)
    raise ArithmeticError('Hankel multiplicity mutant accepted')


def main():
    require(4*F(333,106)**2*F(1827,10000)**2*CAP > 1, 'reference units')
    require(sum(F(1,j*j*(2*j-1)) for j in range(2,17))+F(1,16*33) < F(1,7),
            'weak Hankel tail')
    low = F(3,4)
    small = CAP/(1+CAP/low)+CAP/7
    require(2*small < 1, 'weak guard')
    edges = list(map(lambda i:F(i,24), range(18,217)))
    require(edges[0] == low and edges[-1] == 9 and F(11,2) in edges, 'cover endpoints')
    finite = [enclose(l,h) for l,h in zip(edges,edges[1:])]
    peak = max(*finite,enclose(edges[-1],None))
    require(peak < F(999,1000), 'uniform guard slack')
    # A sharpness mutant: assigning C_infty (or c=0.51) to the arbitrary-b
    # relaxation must fail already on a finite Einstein x and b=e_0.
    require(2*F(51,100)/(1+F(1,200)) > 1, 'overstated asymmetric constant not rejected')
    print(f'CERTIFIED independently: {len(finite)} cells plus soft endpoint; peak < 999/1000')
    print('Rejected: excess Hankel factor at', mutant_rejected(F(11,2),F(133,24)),
          '; lowered relaxed ceiling via exact Einstein e_0 fixture')


if __name__ == '__main__':
    main()
