"""Exact replay of the analytic Q2/Q3 sufficient inequalities."""
from fractions import Fraction as F


def require(condition, guard):
    if not condition:
        raise AssertionError(guard)


def q2(width=1000, notch=F(1, 10), fermi_vertex=0):
    coupling = F(8)
    k1 = coupling / 2
    require(0 < notch < width and fermi_vertex == 0, "zero-FS-moment premise")
    # pi > 3; first row gives 1 <= s_0 <= 1 + coupling at tau = 1.
    b0 = 1 - 2 * (1 + coupling) / width - 2 * notch / 9
    require(b0 > F(3, 4), "notched-band Poisson guard")
    margin = k1 * (2 * b0 - 1) - 1
    require(margin > 1, "one-mode margin")
    return margin


def q3(width=10**10, screening=F(4), blocks=16, tail_sign=-1):
    first = 32
    last = first * 2**blocks - 1
    coupling = screening + F(1, 8)
    width_add = 5 * coupling  # sum_{j>=1} j^-2 < 2
    require(99 * width < 100 * (width - 2 * (2 * last + 1 + width_add)),
            "finite-band Poisson guard")
    lowest_b = F(99, 100)
    require(3 * width_add < 2 * first + 1, "tail normal cost guard")
    require(1 + tail_sign * blocks * F(1, blocks) == 0, "exact static cancellation")
    head_pairing = screening * F(3, 2)  # Omega_screen = 2*pi*tau at witness
    head_normal = (1 + coupling) / lowest_b
    tail_normal = 4 / (blocks * lowest_b)
    cross_cost = 4 * coupling / first**2
    margin = head_pairing - head_normal - tail_normal - cross_cost
    require(margin > F(1, 2), "strict pairing margin")
    return margin


def reject(function, kwargs, guard):
    try:
        function(**kwargs)
    except AssertionError as exc:
        require(str(exc) == guard, f"unexpected failing guard: {exc}")
        print(f"mutant rejected: {kwargs} ({guard})")
    else:
        raise AssertionError(f"mutant accepted: {kwargs}")


if __name__ == "__main__":
    print(f"Q2 off-shell exact margin >= {q2()} > 1")
    print(f"Q3 screened exact margin >= {q3()} > 1/2")
    reject(q2, {"fermi_vertex": 1}, "zero-FS-moment premise")
    reject(q2, {"width": 60}, "notched-band Poisson guard")
    reject(q3, {"screening": F(0)}, "strict pairing margin")
    reject(q3, {"width": 100}, "finite-band Poisson guard")
    reject(q3, {"tail_sign": +1}, "exact static cancellation")
    reject(q3, {"blocks": 1}, "strict pairing margin")
