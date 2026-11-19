"""Numerical cross-check of the paper's two stated convention-dependent conversions."""
import math
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import ellipk

C = 0.18272624777232952

def square_dos(e):
    return ellipk(1.0 - (e / 4.0) ** 2) / (2.0 * math.pi ** 2)

def square_filling(mu):
    return quad(square_dos, -4.0, mu, epsabs=1e-11, epsrel=1e-11)[0]

mu_sq = brentq(lambda x: square_filling(x) - 0.3, -3.999999, -1e-8, xtol=1e-13)
dos = square_dos(mu_sq)
ratio_sq = 1.0 / (28.5 * C * math.sqrt(8 * dos * 0.25))

def triangle_filling(mu, tol):
    def fraction(x):
        denominator = 4.0 * math.cos(x / 2.0)
        if denominator < 1e-15:
            return float(mu >= 2.0)
        y = -(mu + 2.0 * math.cos(x)) / denominator
        return math.acos(max(-1.0, min(1.0, y))) / math.pi
    return quad(fraction, 0.0, math.pi, epsabs=tol, epsrel=tol, limit=500)[0] / math.pi

values = []
for tol in (1e-8, 1e-10, 1e-12):
    mu = brentq(lambda x: triangle_filling(x, tol) - 0.5, -1.0, 1.99, xtol=tol)
    ef = mu + 6.0
    ratio = 0.1 / (C * (0.3 * ef) * math.sqrt(0.4))
    values.append((mu, ef, ratio))
print('square mu/t, N(0)t, R:', mu_sq, dos, ratio_sq)
for tol, result in zip((1e-8, 1e-10, 1e-12), values):
    print('triangular tolerance, mu/t, EF/t, R:', tol, *result)
assert abs(dos - 0.139129) < 2e-6
assert abs(ratio_sq - 0.364) < 0.001
assert abs(values[-1][1] - 6.835) < 0.002
assert abs(values[-1][2] - 0.422) < 0.001
assert max(abs(values[-1][j] - values[-2][j]) for j in range(3)) < 2e-8
print('PASS numerical convention checks; tolerance comparison is not a rigorous error bound')
