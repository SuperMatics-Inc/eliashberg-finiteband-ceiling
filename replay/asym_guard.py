"""Exact relaxed-case exclusions for the proposed sharp asymmetric ceiling."""
from fractions import Fraction as F
from g3x_replay import compute

C0 = F(19,25)


def check(ok, reason):
    if not ok:
        raise ValueError(reason)


def independent_eta():
    # Unshaped Schur weights 1/sqrt(2*n+1), not the primary tuned weights.
    k = lambda j: C0/(j*j)
    t = lambda n,m: k(n+m+1) + (k(abs(n-m)) if n != m else k(2*n+1))
    head = max(sum(t(n,m)/(2*m+1) for m in range(1,25))
               +2*C0/(16*51) for n in range(1,9))
    # L < 2*C0, row mass <= 3*L+K_3. Split m<=4 and m>=5.
    tail = (k(5)+k(11))*sum(F(1,2*m+1) for m in range(1,5))+(6*C0+k(3))/11
    return max(head,tail)


def guards(eta, *, ratio=F(25,36), coupling=F(19,13), first=F(25,38)):
    check(eta+ratio*C0 < 1, 'cross penalty cannot be canceled')
    check(2*C0/(1+C0/coupling) <= 1, 'weak-coupling endpoint')
    check(2*C0*first <= 1, 'low first-mode endpoint')


def main():
    check(4*F(333,106)**2*F(1827,10000)**2*C0 > 1, 'moment scaling')
    for eta in (compute(F(9),None)[3], independent_eta()):
        guards(eta)
    for mutation in ({'ratio':1}, {'coupling':F(3,2)}, {'first':F(2,3)}):
        try:
            guards(independent_eta(), **mutation)
        except ValueError:
            continue
        raise ValueError(f'mutant accepted: {mutation}')
    # Exact Einstein e0 fixture tests the relaxation, not a physical DOS.
    c, ell = F(3,4), F(2)
    check(2*c/(1+c/ell)>1, 'arbitrary-b counterexample fixture')
    print('CERTIFIED two independent tail guards; rejected inflated ratio, coupling, first-mode and arbitrary-b sharp claim')


if __name__=='__main__':
    main()
