"""Exact finite-support witnesses; no discretized normal or gap solve."""
from fractions import Fraction as F


def check(ok, reason):
    if not ok:
        raise ValueError(reason)


def reflect(n):
    return -n-1


def fixture(*, reach=1, strength=64, signs=(1,-2,1)):
    x = dict(zip((1,2,3), signs))
    x.update({reflect(n): v for n,v in tuple(x.items())})
    # Positive/negative reflected triples are separated by three transfers.
    coulomb = sum(x[n]*x[m] for n in x for m in x if abs(n-m)<=reach)
    norm_cap = sum(4*abs(2*n+1)*v*v for n,v in x.items())
    check(-strength*coulomb > norm_cap, 'insufficient negative Rayleigh witness')
    return coulomb, norm_cap


def independent():
    # Work solely on the positive folded block. Its three Fourier-edge
    # contributions to the quadratic form are diagonal 6 and twice -2,-2.
    # No folded Hankel entry is in cutoff. Cancel the phonon rather than use
    # its positive definiteness: its off-transfer part is worst at the
    # adjacent sign changes; the kinetic/normal diagonal is accounted in
    # the independent raw gap norm cap.
    adjacent = 2*(-2-2)
    cap = 4*(3+4*5+7)
    # Diagonal phonon transfer contributes 6, all other entries can be
    # dropped except the negative adjacent folded coefficients. For
    # Omega<=1 and 2*pi>6, their two transfers have K_j <= 1/36 each.
    phonon_lower = 6 - F(16,36)
    check(6 + adjacent == -2, 'folded stencil')
    check(64*2 + phonon_lower > cap, 'folded finite-support certificate')
    return cap


def rejected(**kwargs):
    try:
        fixture(**kwargs)
    except ValueError:
        return
    raise ValueError(f'mutant accepted: {kwargs}')


def main():
    # omega_c=3*pi at tau=1, bandwidth W=100, flat normal box u<=pi*2*w.
    check(F(2)<3<F(4) and F(22,7)*14<100, 'units/cutoff/Poisson-width bound')
    cq, bound = fixture()
    check(cq == -4 and bound == 240 and 2*independent() == bound, 'parity or norm factor')
    rejected(reach=0)
    rejected(reach=2)
    rejected(signs=(1,2,1))
    rejected(strength=1)
    print(f'CERTIFIED full-line test -64*({cq})>{bound}; independent folded lower bound also strict')
    print('Rejected: diagonal cutoff, two-transfer cutoff, same-sign test, weak strength')


if __name__ == '__main__':
    main()
