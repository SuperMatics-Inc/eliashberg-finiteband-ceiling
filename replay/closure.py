"""Exact strip-derivative and first-mode Schur guards for Closure attempt."""
from fractions import Fraction as F
from functools import cache

from window import BETA_HIGH, BETA_LOW, CAP, STRONG, WEAK, a_bounds, q2, sqrt_up, transfers, w

PI_LO = F(333, 106)


def round_up(x, scale=10**8):
    return F(-(-x.numerator*scale//x.denominator), scale)


def log_up(x):
    """For x>=1, log(x) <= (x-1/x)/2; bisect the range with log(2)<7/10."""
    extra = F(0)
    while x > 2:
        x /= 2
        extra += F(7, 10)
    return extra+(x-1/x)/2


def k_bounds(hi, k1lo, k1hi):
    def lower(j):
        return k1lo/(j*j-(j*j-1)*k1lo/hi)

    def upper(j):
        return CAP/(j*j-1+CAP/k1hi)

    return cache(lower), cache(upper)


def widths(lo, hi, blo, bhi, k, lsum, b, nhead=12):
    s0lo = 1+(lo-k(1))*blo
    s0hi = 1+hi*bhi+(1-bhi)*k(1)
    ntail = w(nhead+1)
    if ntail < s0hi:
        raise ValueError('width tail starts below s0')
    rtail = (ntail+hi+2*lsum+k(ntail))/s0lo
    tail_v = max(F(1), log_up(rtail))/ntail
    lower = [blo]+[F(0)]*nhead
    upper = [bhi]+[F(1)]*nhead
    for _ in range(3):
        slo = [s0lo]
        shi = [s0hi]
        for n in range(1, nhead+1):
            wn = w(n)
            slo.append(wn+(lo-k(wn))*lower[n])
            shi.append(wn+hi*upper[n]+2*sum(k(j) for j in range(1, n+1))+k(wn))
        broad = [max(s, s0lo) for s in slo]+[F(ntail)]
        if hi+b >= PI_LO*min(broad[1:]):
            break
        v = [F(0)]+[log_up(max(shi[n]/s0lo, s0hi/slo[n]))/w(n) for n in range(1, nhead+1)]
        M = max(c/(PI_LO-(hi+b)/s) for c, s in zip(v[1:]+[tail_v], broad[1:]))
        for n in range(1, nhead+1):
            wn = w(n)
            smax = broad[n]
            dg = (v[n]+b*M/smax)/(PI_LO-hi/smax)
            dx = wn*(hi*dg+b*M)
            ratio = max(shi[n]/s0lo, s0hi/slo[n])
            t = ratio+1/ratio-2+dx*dx/(s0lo*slo[n])
            rho = 1+(t+sqrt_up(t*(4+t)))/2
            lower[n] = 1-round_up(1-max(lower[n], 1-(1-blo)*rho, blo/rho))
            upper[n] = round_up(min(upper[n], bhi*rho, 1-(1-bhi)/rho))
    return lower, upper


def sinc_upper(beta):
    t = (PI_LO*beta)**2
    return 1-t/6+t*t/120-t**3/5040+t**4/362880


def strip_widths(lo, hi, blo, bhi, k, lsum, b, bmin, bmax):
    """Separate real and imaginary Schwarz–Pick gains."""
    _, amax = a_bounds(k, lsum, blo, bhi)
    s0lo = 1+(lo-k(1))*blo
    s0hi = 1+hi*bhi+(1-bhi)*k(1)
    sc, qi2 = sinc_upper(blo), q2(blo)
    den1 = (lo+1/bhi-k(1))*(lo+3-k(3))
    r0, i0 = sc/den1, hi*hi*qi2/den1
    if max((hi+b)**2*r0, i0) >= 1:
        return bmin, bmax
    ee = round_up(b*sqrt_up(r0*amax**2/((1-i0)*(1-(hi+b)**2*r0))))
    for n in range(1, len(bmin)):
        wn = w(n)
        al = (wn-1-k(wn)-(1-blo)*k(1))/wn
        ah = (wn-1+2*sum(k(j) for j in range(1, n+1))+k(wn)+bhi*k(1))/wn
        den = (lo+1/bhi-k(1))*(lo+wn/bmax[n]-k(wn))
        r2 = hi*hi*sc*sinc_upper(bmin[n])/den
        i2 = hi*hi*qi2*sinc_upper(bmin[n])/den
        yl = (al-sqrt_up(i2*(al*al+(1-i2)*ee*ee/(1-r2))))/(1-i2)
        yh = (ah+sqrt_up(i2*(ah*ah+(1-i2)*ee*ee/(1-r2))))/(1-i2)
        for _ in range(3):
            sl = max(wn+(lo-k(wn))*bmin[n], s0lo+yl*wn)
            sh = min(wn+hi*bmax[n]+2*sum(k(j) for j in range(1, n+1))+k(wn), s0hi+yh*wn)
            for cutoff in (False, True):
                # Test all b_n <= a midpoint at once, rather than assuming b_n <= beta.
                limit = (bmin[n]+blo)/2 if cutoff else bmax[n]
                deficit = max(F(0), lo*(blo-limit)/wn)
                yu = min(yh, ah-deficit) if cutoff else yh
                if yu < yl:
                    bmin[n] = max(bmin[n], 1-round_up(1-limit))
                    continue
                core = min(ah*ah/(1-i2), max(yu*yu, yl*yl)-deficit*deficit/i2)
                disc = r2*(ee*ee+(1-r2)*core)
                if disc < 0:
                    if not cutoff:
                        raise ArithmeticError('empty strip enclosure')
                    bmin[n] = max(bmin[n], 1-round_up(1-limit))
                    continue
                x = (ee+sqrt_up(disc))*wn/(1-r2)
                sup = min(sh, s0hi+yu*wn, wn+hi*limit+2*sum(k(j) for j in range(1, n+1))+k(wn))
                ratio = max(F(1), sup/s0lo, s0hi/sl)
                t = ratio+1/ratio-2+x*x/(s0lo*sl)
                rho = 1+(t+sqrt_up(t*(4+t)))/2
                base_lo = max(F(0), 1-(1-blo)*rho, blo/rho)
                if not cutoff:
                    bmax[n] = round_up(min(bmax[n], bhi*rho, 1-(1-bhi)/rho))
                    bmin[n] = max(bmin[n], 1-round_up(1-base_lo))
                elif base_lo > limit:
                    bmin[n] = max(bmin[n], 1-round_up(1-limit))
    return bmin, bmax


def rows(trial, bmin, bmax, kl, ku):
    """Schur row upper bounds for y_m=trial[m], with a constant tail."""
    nhead = len(trial)-1
    for n, yn in enumerate(trial):
        wn = w(n)
        # Both sides of the diagonal are Hankel-only on the plateau.
        total = 2*CAP*trial[-1]/(n+nhead)
        if n < nhead:
            total += 2*ku(wn)*bmax[n]*yn
        for m in range(nhead):
            if m == n:
                continue
            ym = trial[m]
            j, p = abs(n-m), n+m+1
            t = (ym-yn)*(ku(j) if ym >= yn else kl(j))+(ym+yn)*ku(p)
            total += t*(bmax[m] if t >= 0 else bmin[m])
        yield total/(wn*yn)


TRIAL = (1000000, 225000, 70000, 28000, 13200, 7000, 4200, 2700, 1800)
HEIGHT = F(9999, 10000)


def shape(lo, hi, blo, bhi, k, lsum, b):
    lsum, b = round_up(lsum), round_up(b)
    bmin, bmax = widths(lo, hi, blo, bhi, k, lsum, b)
    return strip_widths(lo, hi, blo, bhi, k, lsum, b, bmin, bmax)


def row_cost(hi, a, h, bmin, bmax, pieces=16, trial=TRIAL):
    cost = F(0)
    for i in range(pieces):
        kl, ku = k_bounds(hi, a+(h-a)*i/pieces, a+(h-a)*(i+1)/pieces)
        cost = max(cost, max(rows(trial, bmin, bmax, kl, ku)))
    return cost


def guard(lo, hi, blo, bhi, pieces=16):
    k, lsum, b = transfers(hi)
    limit = HEIGHT/(2*bhi)
    if k(1) < limit:
        return 2*bhi*k(1), F(0)
    bmin, bmax = shape(lo, hi, blo, bhi, k, lsum, b)
    return HEIGHT, row_cost(hi, limit, k(1), bmin, bmax, pieces)


def partition(lo, hi, count):
    return [lo+(hi-lo)*j/count for j in range(count+1)]


def main():
    if min(TRIAL) <= 0 or min(TRIAL[:-1]) < TRIAL[-1]:
        raise ValueError('invalid plateau trial')
    xs, ys = partition(WEAK, STRONG, 30), partition(BETA_LOW, BETA_HIGH, 16)
    worst = F(0)
    schur_peak = F(0)
    count = 0
    for lo, hi in zip(xs, xs[1:]):
        for u, v in zip(ys, ys[1:]):
            height, schur = guard(lo, hi, u, v)
            cost = max(height, schur)
            if cost >= 1:
                raise ValueError(f'unproved box [{lo}, {hi}] x [{u}, {v}]')
            count += 1
            worst = max(worst, cost)
            schur_peak = max(schur_peak, schur)

    ell, beta = F(4), F(17, 20)
    k, lsum, b = transfers(ell)
    lower, upper = shape(ell, ell, beta, beta, k, lsum, b)
    limit = HEIGHT/(2*beta)
    point = row_cost(ell, limit, k(1), lower, upper)
    if point >= F(92, 100):
        raise ValueError('unproved old zero-width obstruction')
    mutants = (
        ('discard nonanchor lower weights',
         row_cost(ell, limit, k(1), [beta]+[F(0)]*(len(lower)-1), upper)),
        ('replace the plateau trial by unit weights',
         row_cost(ell, limit, k(1), lower, upper, trial=(1,)*len(TRIAL))),
        ('merge the K1 partition at the high-coupling corner',
         max(guard(STRONG, STRONG, BETA_HIGH, BETA_HIGH, pieces=1))),
    )
    for name, cost in mutants:
        if cost < 1:
            raise ValueError(f'accepted closure mutant: {name}')
        print(f'Rejected {name}; cost >= 1')
    print(f'Closure exact replay: {count} boxes; combined costs <= {round_up(worst)}; '
          f'row costs <= {round_up(schur_peak)}; old obstruction <= {round_up(point)}')


if __name__ == '__main__':
    main()
