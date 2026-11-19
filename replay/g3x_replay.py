"""Exact scalar guard replay for RIGOR.md. No witness files or external packages."""
from fractions import Fraction as F

C = F(19, 25)
CUT = F(11, 2)
LAST = F(9)
Q = 10**10
J = 64
N = 24


def check(ok, label):
    if not ok:
        raise ValueError(label)


def compute(lo, hi):
    def upper(j):
        r = C/(j*j + (C/hi if hi is not None else 0))
        return F(-(-r.numerator*Q//r.denominator), Q)

    k = [None]+[upper(j) for j in range(1, 2*J+2)]
    L = sum(k[1:J+1])+C/J
    weighted0 = 2*L + sum(k[j]*(k[j]+k[j+1]) for j in range(1,J+1))
    weighted0 += 2*C*C/(3*J**3)+2*k[1]**2
    denominator = lo+1-k[1]
    d = weighted0/denominator
    e = (2*L+k[3]+max(2*L+k[1]-1, 0)*k[1])/denominator
    w = lambda n: 2*n+1
    g = lambda n: {2:F(7,5), 3:F(6,5), 4:F(11,10)}.get(n, 1)
    t = lambda n,m: k[abs(n-m)]+k[n+m+1] if n != m else 2*k[2*n+1]
    # All n>=17 are covered separately; there g_n=1 and the row mass is <=4L.
    eta = max((k[9]+k[19])*sum(F(g(m),w(m)) for m in range(1,9))+4*L/19,
              max((sum(t(n,m)*g(m)/w(m) for m in range(1,J+1))
                   +2*C/((J-16)*(2*J+3)))/g(n) for n in range(1,17)))
    check(eta < 1, 'tail Schur stability')
    f = [None]+[k[n]+k[n+1] for n in range(1,N+1)]
    u = [None]+[sum(t(n,m)*f[m]/w(m) for m in range(1,N+1))
                +4*L*C/(N+1)**3 for n in range(1,N+1)]
    G = F(15,2)*C*C+32*C*L/(N+1)
    norm_f = sum(f[n]**2/w(n) for n in range(1,N+1))+C*C/(2*N**4)
    inner = sum(f[n]*u[n]/w(n) for n in range(1,N+1))+C*G/(4*N**4)
    norm_u = sum(u[n]**2/w(n) for n in range(1,N+1))+G*G/(8*N**4)
    return k[1], d, e, eta, norm_f+inner+norm_u/(1-eta)


def guards(lo, hi, strong, *, mutant=None):
    k, d, e, eta, V = compute(lo,hi)
    if mutant == 'omit-normal-hankel' and strong:
        e += k
    if strong:
        check(e+eta < 1, 'strong tail comparison')
        check(d+V < 1, 'strong Schur endpoint')
        return max(e+eta, d+V)
    if mutant == 'double-off-diagonal':
        V *= 2
    check(k+V < 1, 'middle beta=1')
    check((2*k+V)*d < k+d, 'middle branch intersection')
    return max(k+V, (2*k+V)*d/(k+d))


def cover(edges, *, mutant=None):
    check(edges[0] == F(3,4) and edges[-1] == LAST and CUT in edges, 'window endpoints')
    check(all(hi-lo == F(1,16) for lo,hi in zip(edges,edges[1:])), 'window coverage')
    peak = max(guards(lo,hi,lo>=CUT,mutant=mutant) for lo,hi in zip(edges,edges[1:]))
    peak = max(peak,guards(LAST,None,True,mutant=mutant))
    return peak


def rejected(run):
    try:
        run()
    except ValueError as exc:
        return str(exc)
    raise ValueError('mutant accepted')


def main():
    # The lower inputs pi>333/106 and C_inf>1827/10000 are used only here.
    check(4*F(333,106)**2*F(1827,10000)**2*C > 1, 'moment scaling')
    check(sum(F(1,j*j*(2*j-1)) for j in range(2,9))+F(1,136) < F(1,7), 'Hankel tail')
    check(2*(C/(1+C/F(3,4))+C/7) < 1, 'weak coupling')
    soft = compute(LAST,None)
    check(soft[3] + F(25,72) < 1, 'height-only asymmetric guard')
    edges = [F(i,16) for i in range(12,145)]
    peak = cover(edges)
    check(peak < F(999,1000), 'strict peak')
    errors = [rejected(lambda:cover(edges[:3]+edges[4:])),
              rejected(lambda:guards(F(5),F(81,16),False,mutant='double-off-diagonal')),
              rejected(lambda:guards(CUT,CUT+F(1,16),True,mutant='omit-normal-hankel'))]
    print(f'CERTIFIED {len(edges)-1} finite cells plus soft infinite cell, peak < 999/1000')
    print('Rejected:', '; '.join(errors))


if __name__ == '__main__':
    main()
