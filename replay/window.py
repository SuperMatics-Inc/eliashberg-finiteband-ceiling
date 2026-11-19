"""Rational parameter-box guards for the Window section of RIGOR.md."""
from fractions import Fraction as F
from functools import cache
from math import isqrt

CAP = F(19, 25)
ROOT_SCALE = 10**9


def sqrt_up(x):
    if x == 0:
        return F(0)
    return F(1+isqrt(x.numerator*ROOT_SCALE**2//x.denominator), ROOT_SCALE)


def q2(beta):
    # t cot(t) is decreasing; evaluate the Taylor quotient at t <= pi*beta/2.
    x = (F(333, 212)*beta)**2
    cos_hi = 1-x/2+x*x/24-x**3/720+x**4/40320
    sinc_lo = 1-x/6+x*x/120-x**3/5040
    return min(cos_hi/sinc_lo, 5*(1-beta))


def w(n):
    return 2*n+1


@cache
def transfers(hi):
    cap = CAP

    @cache
    def k(j):
        return cap/(j*j+(cap/hi if hi is not None else 0))
    lsum = sum(k(j) for j in range(1, 65))+cap/64
    # Exact finite Toeplitz/Hankel triangle sums; all displayed coefficients >= 0.
    b = max((4*n*(lsum-k(n+1))+2*sum(w(j)*k(j) for j in range(1, n+1))
             -k(n)-k(1)+(2*n)*k(n+1))/w(n)-k(n)+k(w(n))
            for n in range(1, 13))
    h13 = sum(F(1, j) for j in range(1, 14))
    b = max(b, 2*lsum+4*cap*(h13+1)/w(13))
    return k, lsum, b


def a_bounds(k, lsum, blo, bhi):
    lower = 1-(1+k(3)+(1-blo)*k(1))/3
    upper = max(F(1), 1+(2*lsum+bhi*k(1)-1)/w(7),
                *(1+(2*sum(k(j) for j in range(1, n+1))
                      +k(w(n))+bhi*k(1)-1)/w(n) for n in range(1, 7)))
    return lower, upper


def shift_box(lo, hi, blo, bhi, k, b, amax):
    """Bounds on the zeroth-row-anchored normal differences."""
    if hi is None:
        q = sqrt_up(q2(blo))
        rb = b/lo*q
    else:
        q_per = sqrt_up(q2(blo)/((lo+1/bhi-k(1))*(lo+3-k(3))))
        q = hi*sqrt_up(q2(blo)/((hi+1/bhi-k(1))*(hi+3-k(3))))
        rb = b*q_per
    if q+rb >= 1:
        return None
    e = rb*amax/(1-q-rb)
    return q, e


def ellipse(q, e, amin, amax):
    den = 1-q*q
    # Lower bound on Delta s/w; upper bound on |Delta x|/w when b_n <= beta.
    ymin = (amin-q*sqrt_up(amin*amin+e*e))/den
    xmax = (e+q*sqrt_up(e*e+den*amax*amax))/den
    return ymin, xmax


def eigen2(a, b, x):
    """Upper bound on the top eigenvalue of [[a,x],[x,b]]."""
    return (a+b+sqrt_up((a-b)**2+4*x*x))/2


def flat_slack(lo, hi, blo, bhi, k, lsum, b, eta, v, mu=F(1)):
    """Upper bounds for the branch-uniform tail and normalized head costs."""
    if 2*k(1)*bhi < 1:
        return 2*k(1)*bhi
    amin, amax = a_bounds(k, lsum, blo, bhi)
    shifts = shift_box(lo, hi, blo, bhi, k, b, amax)
    if shifts is None:
        return None
    ymin, x = ellipse(*shifts, amin, amax)
    inward = max(-ymin, 0)
    slope = eigen2(amax, x*x+inward*(1+inward), x)/(1+(lo-k(1))*blo)
    etail, e0 = slope*(2*lsum+k(3)), slope*(2*lsum+k(1))
    # Dominate E by alpha(I-F), keeping the actual flat Schur complement.
    ar = max(2*lsum/w(7), max((2*sum(k(j) for j in range(1, n+1))+k(w(n)))/w(n)
                            for n in range(1, 7)))
    alpha = max(etail/(1-eta), (ar+etail)/(ar+1-eta))
    tail = alpha*(1-blo)
    if tail >= 1:
        return None
    klow = 1/(2*bhi)
    mixed = max(e0*(1-alpha*(1-beta))+alpha*(1-beta*klow) for beta in (blo, bhi))
    score = min(max(eta+etail, v+e0), max(tail, mixed))
    if mu < 1:
        # Multiply the head gap by the strictly positive 1-alpha*(1-beta).
        a = alpha*(e0-klow)
        b1 = (1-alpha)*(e0-klow)+alpha*(1-e0)-(mu-klow)
        betas = [blo, bhi]
        if a > 0 and blo < -b1/(2*a) < bhi:
            betas.append(-b1/(2*a))
        gap = min((1-alpha)*(1-e0)+beta*(b1+beta*a) for beta in betas)
        score = min(score, max(tail, 1-gap))
    return score


def weak_slack(lo, hi, blo, bhi, k, lsum, b, eta):
    """Upper bound on the head Schur cost, retaining the negative normal row."""
    k1 = k(1)
    if 2*k1*bhi <= 1:
        return 2*k1*bhi
    # For K1 below this value the height-only Schur test already succeeds.
    klow = 1/(2*bhi)
    _, amax = a_bounds(k, lsum, blo, bhi)
    shifts = shift_box(lo, hi, blo, bhi, k, b, amax)
    if shifts is None:
        return None
    q, e = shifts
    s0 = 1+(lo-k1)*blo
    d0 = 1-blo
    linear = quadratic = F(0)
    for n in range(1, 9):
        wn = w(n)
        alow = (wn-1-k(wn)-(1-blo)*k1)/wn
        ahigh = (wn-1+2*sum(k(j) for j in range(1, n+1))+k(wn)+bhi*k1)/wn
        qn = hi*sqrt_up(q2(blo)/((hi+1/bhi-k1)*(hi+wn-k(wn))))
        ymin, x = ellipse(min(q, qn), e, alow, ahigh)
        off = x*wn
        s_lo = max(F(wn), s0+ymin*wn)
        for _ in range(2):
            s_ratio = ((1+hi)/(1+hi+ymin*wn) if ymin >= 0 else
                       min((1+hi)/s_lo, 1-ymin*wn/s_lo))
            rho = max(F(1), eigen2(1+ahigh*wn/s0, s_ratio+off*off/(s_lo*s0), off/s0))
            bn = max(F(0), 1-d0*rho)
            s_lo = max(s_lo, wn+max(lo-k(wn), 0)*bn)
        ratio = CAP*(F(4, w(n)**2)+F(1, n*n*(n+1)**2))
        coefficient = (1-bhi*ratio/(1-eta))*bn
        if n == 1:
            linear = coefficient
        else:
            quadratic += coefficient*w(n)/(CAP*n*n*(n+1)**2)
    # Keep K1 symbolic in both the positive and the negative normal terms.
    # The maximum is at an endpoint or at the vertex of this concave quadratic.
    vertices = [klow, k1]
    if quadratic > 0 and klow < (2*bhi-linear)/(2*quadratic) < k1:
        vertices.append((2*bhi-linear)/(2*quadratic))
    return max((2*bhi-linear)*u+linear*k(2)-quadratic*u*u for u in vertices)


@cache
def flat_cap(hi):
    """Enclose the flat Einstein top via its finite block and cross norm."""
    k, lsum, _ = transfers(hi)
    nhead = 16
    rows = [[((k(w(n))-2*sum(k(j) for j in range(1, n+1))) if n == m
              else (k(abs(n-m))+k(n+m+1)))/w(n) for m in range(nhead)]
            for n in range(nhead)]
    # Floating arithmetic only proposes positive weights; every row is checked exactly.
    approximate = [[float(b) for b in row] for row in rows]
    y = [1/(m+1)**3 for m in range(nhead)]
    for _ in range(48):
        z = [y[m]+sum(b*p for b,p in zip(row, y)) for m,row in enumerate(approximate)]
        y = [p/z[0] for p in z]
    trial = [max(1, round(p*10**8)) for p in y]
    head = max(sum(b*p for b,p in zip(row, trial))/trial[m] for m,row in enumerate(rows))
    tail = 3*lsum/w(nhead)
    cross_sq = tail*(4*CAP/nhead+3*lsum/(nhead+1))
    return min(F(1), (head+tail+sqrt_up((head-tail)**2+4*cross_sq))/2)


WEAK = F(75, 32)
STRONG = F(17)
SOFT = F(56)
BETA_MIN = F(25, 38)
BETA_LOW = F(222, 323)
BETA_HIGH = F(15, 16)


def betas(start):
    return [start]+[F(i, 256) for i in range(257) if start < F(i, 256)]


def grid(lo, hi, den):
    return [lo]+[F(i, den) for i in range(int(lo*den)+1, int(hi*den)+1) if F(i, den) < hi]+[hi]


def verify_window(compute):
    """Run the exact rectangle proof and reject four strengthened claims."""
    @cache
    def data(lo, hi):
        *_, eta, v = compute(lo, hi)
        if eta+25*CAP/36 >= 1:
            raise ValueError('height estimate')
        return *transfers(hi), eta, v

    def scores(lo, hi, u, v, weak_only=False):
        k, lsum, b, eta, schur = data(lo, hi)
        first = None
        if not weak_only:
            mu = flat_cap(hi) if hi is not None and hi <= 13 else F(1)
            first = flat_slack(lo, hi, u, v, k, lsum, b, eta, schur, mu)
        if hi is None or (first is not None and first < 1):
            return first
        second = weak_slack(lo, hi, u, v, k, lsum, b, eta)
        return min((x for x in (first, second) if x is not None), default=None)

    def cover(xs, ys, weak_only=False):
        if (not all(b is None or a < b for a,b in zip(xs, xs[1:]))
                or not all(a < b for a,b in zip(ys, ys[1:]))):
            raise ValueError('nonincreasing window partition')
        peak = F(0)
        for lo,hi in zip(xs, xs[1:]):
            for u,v in zip(ys, ys[1:]):
                val = scores(lo, hi, u, v, weak_only)
                if val is None or val >= 1:
                    raise ValueError(f'unproved cell [{lo}, {hi}] x [{u}, {v}]')
                peak = max(peak, val)
        return (len(xs)-1)*(len(ys)-1), peak

    def low_beta(beta):
        k, _, _ = transfers(STRONG)
        if 2*beta*k(1) > 1:
            raise ValueError('low-beta threshold exceeds Jensen height limit')

    bgrid = betas(BETA_MIN)
    counts, peaks = zip(cover(grid(F(19, 13), WEAK, 64), bgrid, weak_only=True),
                        cover(grid(STRONG, SOFT, 4)+[None], bgrid),
                        cover(grid(F(9, 4), STRONG, 4), betas(BETA_HIGH)))
    low_beta(BETA_LOW)
    if max(peaks) >= F(999999, 1000000):
        raise ValueError('window certificate slack')

    # Each rejected cell is actually in the corresponding widened region.
    mutants = (
        ('raise weak cutoff', 'unproved cell', lambda: cover(
            [WEAK, WEAK+F(1,64)], [F(111,128), F(223,256)], weak_only=True)),
        ('lower strong cutoff', 'unproved cell', lambda: cover(
            [F(16), F(65,4)], [F(27,32), F(217,256)])),
        ('lower high-beta cutoff', 'unproved cell', lambda: cover(
            [F(5), F(21,4)], [F(9,10), F(231,256)])),
        ('raise low-beta cutoff', 'low-beta threshold', lambda: low_beta(F(7,10))),
    )
    for name, reason, attempt in mutants:
        try:
            attempt()
        except ValueError as exc:
            if not str(exc).startswith(reason):
                raise
            print(f'  Rejected {name}: {exc}')
        else:
            raise ValueError(f'accepted window mutant: {name}')

    ell, beta = F(4), F(17,20)
    k, lsum, b, eta, v = data(ell, ell)
    flat = flat_slack(ell, ell, beta, beta, k, lsum, b, eta, v, flat_cap(ell))
    weak = weak_slack(ell, ell, beta, beta, k, lsum, b, eta)
    if not (flat is not None and weak is not None and flat > F(13,10) and weak > F(103,100)):
        raise ValueError('point obstruction to the current guards')
    print(f'Window exact replay: {sum(counts)} rectangles; costs < 999999/1000000; '
          f'point ell={ell}, beta={beta}: flat > 13/10 and weak > 103/100 (inconclusive)')
