"""
Python: Strengthening the Baillie-PSW primality test
https://homes.cerias.purdue.edu/~ssw/bfw.pdf
https://arxiv.org/abs/2006.14425
"""
import itertools
from collections.abc import Iterable
from typing import Optional


def isprime_miller_bases(n: int, bases: Iterable[int]) -> bool:
    """
    Miller-Rabin probable-prime test for all the specified bases.
    n must be odd and at least 3. Reduce each base modulo n and skip zero residues.
    Skipping a zero residue is a convention for fixed base lists, not a passed
    Miller-Rabin round. The BPSW wrapper uses base 2, which is nonzero for odd n >= 3.
    """
    assert n > 2 and (n & 1) == 1, 'value must be 3 or greater odd integer'
    n1 = n - 1
    s = (n1 & -n1).bit_length() - 1
    d = n1 >> s
    for a in bases:
        a %= n
        if a == 0:
            continue
        t = pow(a, d, n)
        if t == 1 or t == n1:
            continue
        for _ in range(s - 1):
            t = pow(t, 2, n)
            if t == n1:
                break
        else:
            return False
    return True


def isprime_miller_base2(n: int) -> bool:
    """
    Miller-Rabin probable-prime test to base 2.
    https://oeis.org/A001262 : Strong pseudoprimes to base 2.
    """
    return isprime_miller_bases(n, [2])


def isqrt(n: int) -> int:
    """Return floor(sqrt(n)) for nonnegative n."""
    assert n >= 0, 'square root of negative number is not supported'
    if n < 2:
        return n
    k = ((n - 1).bit_length() + 1) // 2
    s = 1 << k
    t = (s + (n >> k)) >> 1
    while s > t:
        s, t = t, (t + n // t) >> 1
    return s


def issq(n: int) -> bool:
    """
    Return whether n is a perfect square. Reject negative values, apply a
    quadratic-residue filter modulo 32, then test r * r == n for the integer square root r.
    """
    return n >= 0 and ((0x02030213 >> (n & 31)) & 1) > 0 and isqrt(n) ** 2 == n


def jacobi_symbol(a: int, n: int) -> int:
    """
    Return the Jacobi symbol (a/n) for integer a and positive odd n.
    The result is one of -1, 0, and 1.

    For positive odd n, this agrees with the Kronecker symbol.
    The result is 0 if and only if gcd(a, n) > 1.

    When n is prime, a result of 1 indicates a nonzero quadratic residue,
    and a result of -1 indicates a quadratic nonresidue.
    For composite n, a result of 1 does not necessarily imply a quadratic residue.
    """
    assert n > 0 and (n & 1) == 1, 'value must be positive odd integer'
    j = 1
    # a is an integer; n is positive and odd.
    # (-a/n) = (-1/n)(a/n),
    # (-1/n) = -1 iff n ≡ 3 (mod 4)
    if a < 0:
        a = -a
        if (n & 3) == 3:
            j = -j

    # a is nonnegative.
    while a != 0:
        # a is positive.
        # (2a/n) = (2/n)(a/n)
        #
        # (2/n) = -1 iff n ≡ 3, 5 (mod 8),
        # (2/n) =  1 iff n ≡ 1, 7 (mod 8)
        while (a & 1) == 0:
            a, j = (a >> 1), (-j if ((n + 2) & 5) == 5 else j)

        # Both a and n are positive and odd.
        #
        # (a/n)(n/a) = -1 iff a ≡ n ≡ 3 (mod 4),
        # (a/n)(n/a) =  1 otherwise
        # (a/n) = (a mod n/n)
        #
        # Use these identities to exchange a and n and reduce the new numerator.
        if (a & n & 3) == 3:
            j = -j
        a, n = n % a, a

    # If n == 1, then j * (0/1) = j because (0/1) = 1.
    # If n > 1, then j * (0/n) = 0 because (0/n) = 0.
    return j if n == 1 else 0


def kronecker_symbol(a: int, n: int) -> int:
    """
    Return the Kronecker symbol (a/n) for integers a and n.

    Handle a zero denominator, its sign, and its power-of-two factor first,
    then delegate the positive odd denominator to the Euclidean-style jacobi_symbol.
    """
    # (a/0) = 1 iff a = +/-1; otherwise it is 0.
    if n == 0:
        return int(a == 1 or a == -1)

    j = 1

    # Handle the factor (a/-1) from a negative denominator.
    if n < 0:
        n = -n
        if a < 0:
            j = -j

    # Extract the power-of-two factor from the denominator.
    t = (n & -n).bit_length() - 1
    if t != 0:
        if (a & 1) == 0:
            return 0
        if ((a + 2) & 5) == 5 and (t & 1) != 0:
            j = -j
        n >>= t

    # The remaining denominator is positive and odd (possibly 1).
    return j * jacobi_symbol(a, n)


SELFRIDGE_PREFIX = (5, 7, 9, 11, 13, 15, 17, 19, 23, 29)
SELFRIDGE_WHEEL30 = (1, 7, 11, 13, 17, 19, 23, 29)


def selfridge_abs_candidates():
    """Generate an unbounded sequence of Selfridge |D| candidates using a mod 30 wheel."""
    # BFW Method A scans every odd |D| starting at 5; Wheel30 is an extra optimization.
    # Keep 9 to detect a factor 3, and 15 to test the missing discriminant -3 via
    # -15 = (-3)*5 once (5/n) = 1. Beyond this prefix, multiplicativity shows that
    # a skipped multiple of 3 or 5 cannot be the first Jacobi value different from 1.
    # This preserves the first stop of the scan with BFW factor detection, not an
    # unrestricted search that ignores Jacobi-zero candidates.
    yield from SELFRIDGE_PREFIX

    for base in itertools.count(30, 30):
        for r in SELFRIDGE_WHEEL30:
            yield base + r


def lucas_selfridge_scan(n: int) -> tuple[int, int]:
    """
    Run the Selfridge scan with BFW factor detection and return (D, s).

    (0, 0): n is a perfect square.
    (D, -1): D was selected with Jacobi (D/n) = -1.
    (D, 0): n does not divide |D| and Jacobi (D/n) = 0 detects a nontrivial factor.
    """
    assert n > 2 and (n & 1) == 1, 'value must be 3 or greater odd integer'

    # BFW suggests a square check after several unsuccessful candidates.
    # Checking up front also makes this helper terminate when used without MR.
    if issq(n):
        return 0, 0

    for i in selfridge_abs_candidates():
        # The termination theorem guarantees that the scan stops before i reaches 2n.
        # For 0 < i < 2n, gcd(i, n) == n iff n divides i iff i == n,
        # so checking only i == n excludes every case with gcd(i, n) == n.
        # BFW states the general n-does-not-divide-|D| check; this simplification
        # relies on the separate first-stop bound, also preserved by Wheel30.
        if i == n:
            continue

        d = i if (i & 3) == 1 else -i
        j = jacobi_symbol(d, n)

        if j == -1:
            return d, -1

        if j == 0:
            # The termination theorem places the stopping candidate below 2n. Since i != n,
            # Jacobi == 0 implies 1 < gcd(i, n) < n.
            return d, 0


def lucas_selfridge_d(n: int) -> Optional[int]:
    """Return D for Lucas parameter selection only when s = -1."""
    d, s = lucas_selfridge_scan(n)
    return d if s == -1 else None


def lucas_params_a(n: int) -> Optional[tuple[int, int]]:
    """
    Return (P, Q) using Selfridge Method A.

    For the selected D, always use P = 1 and Q = (1 - D) // 4.
    In particular, D = 5 gives (P, Q) = (1, -1).
    """
    d = lucas_selfridge_d(n)
    if d is None:
        return None
    return 1, (1 - d) // 4


def lucas_params_a_star(n: int) -> Optional[tuple[int, int]]:
    """
    Return (P, Q) using Selfridge Method A*. n must be odd and at least 3.
    Return None if a perfect square or a nontrivial factor is detected.

    For D != 5, use P = 1 and Q = (1 - D) // 4, as in Method A.
    Only for D = 5, use (P, Q) = (5, 5), preserving D = P^2 - 4Q = 5.
    Use Wheel30 without an upper limit on the search range.
    """
    d = lucas_selfridge_d(n)
    if d is None:
        return None
    if d == 5:
        return 5, 5
    return 1, (1 - d) // 4

def div2_mod_odd(x: int, n: int) -> int:
    """
    Return x / 2 modulo positive odd n.

    If x is odd, add n to make it even before dividing by 2.
    Normalize the result to 0 <= r < n.
    """
    assert n > 0 and (n & 1) == 1
    return ((x + (x & 1) * n) >> 1) % n


def lucas_uvq_mod(n: int, p: int, q: int, k: int) -> tuple[int, int, int]:
    """
    For positive odd n and nonnegative k, compute the Lucas sequence values

        (U_k mod n, V_k mod n, Q^k mod n)

    using the binary method.

    Set D = P^2 - 4Q and use the following identities.

        U_{2k} = U_k V_k
        V_{2k} = V_k^2 - 2 Q^k
        Q^{2k} = (Q^k)^2

        U_{k+1} = (P U_k + V_k) / 2
        V_{k+1} = (D U_k + P V_k) / 2
        Q^{k+1} = Q Q^k
    """
    assert n > 0 and (n & 1) == 1
    assert k >= 0

    if k == 0:
        return 0, 2 % n, 1 % n

    d = p * p - 4 * q

    # Initialize the values corresponding to the leading 1 bit of the index.
    # U_1 = 1, V_1 = P, Q^1 = Q
    u, v, qk = 1 % n, p % n, q % n

    # The leading bit has already been processed; start with the next bit.
    for bit in range(k.bit_length() - 2, -1, -1):
        # Double the index.
        u, v, qk = (
            u * v % n,
            (v * v - 2 * qk) % n,
            qk * qk % n,
        )

        # If the current bit is 1, increment the index.
        if (k >> bit) & 1:
            old_u = u
            old_v = v

            u = div2_mod_odd(p * old_u + old_v, n)
            v = div2_mod_odd(d * old_u + p * old_v, n)
            qk = qk * q % n

    return u, v, qk


def isprime_lucas_strong_pq(n: int, p: int, q: int) -> bool:
    """Shared core testing the strong Lucas condition for fixed (P, Q)."""
    # The caller must supply an odd n >= 3 with Jacobi(P*P - 4*Q, n) == -1
    # for the BFW interpretation: delta(n) is then n + 1. This helper checks only
    # the congruences; it neither selects parameters nor verifies that hypothesis.
    # The prime-input guarantee also assumes gcd(n, Q) == 1, as in BFW Section 2.3.
    # n + 1 = odd_part * 2^s, where d = odd_part is odd.
    delta = n + 1
    s = (delta & -delta).bit_length() - 1
    # Compute U_d, V_d, and Q^d.
    u, v, qk = lucas_uvq_mod(n, p, q, delta >> s)

    # The strong Lucas condition holds if U_d == 0 or V_d == 0.
    if u == 0 or v == 0:
        return True

    # Test the remaining V_{d 2^r} values for 1 <= r < s.
    for _ in range(s - 1):
        v, qk = (
            (v * v - 2 * qk) % n,
            qk * qk % n,
        )
        if v == 0:
            return True

    return False


def isprime_lucas_strong_a(n: int) -> bool:
    """Strong Lucas probable-prime test using Method A."""
    assert n > 2 and (n & 1) == 1, 'value must be 3 or greater odd integer'
    params = lucas_params_a(n)
    if params is None:
        return False
    return isprime_lucas_strong_pq(n, *params)


def isprime_lucas_strong_a_star(n: int) -> bool:
    """
    Strong Lucas probable-prime test using Method A*.
    """
    assert n > 2 and (n & 1) == 1, 'value must be 3 or greater odd integer'
    params = lucas_params_a_star(n)
    if params is None:
        return False
    return isprime_lucas_strong_pq(n, *params)


def isprime_lucas_strengthened(n: int) -> bool:
    """
    Strengthened strong Lucas probable-prime test using Method A*.

    Test all three of the following conditions.
    These are BFW Section 6, steps 3-5; base-2 MR is performed by the BPSW wrapper.

    1. strong Lucas probable-prime condition
    2. V_{n+1} == 2Q mod n
    3. Q^((n+1)/2) == Q * jacobi_symbol(Q, n) mod n
    """
    assert n > 2 and (n & 1) == 1, 'value must be 3 or greater odd integer'

    params = lucas_params_a_star(n)
    if params is None:
        return False

    p, q = params

    # n + 1 = odd_part * 2^s, where d = odd_part is odd.
    delta = n + 1
    s = (delta & -delta).bit_length() - 1

    # Compute U_d, V_d, and Q^d.
    u, v, qk = lucas_uvq_mod(n, p, q, delta >> s)

    # Strong Lucas condition:
    #
    # U_d == 0
    #
    # or, for some 0 <= r < s,
    #
    # V_{d 2^r} == 0
    strong_ok = (u == 0)

    q_half = 0

    # Do not return immediately on strong Lucas success: steps 4 and 5 still
    # need V_{n+1} and Q^{(n+1)/2}. All congruences use residues modulo n.
    for r in range(s):
        # The current index is odd_part * 2^r.
        if v == 0:
            strong_ok = True

        # When r == s - 1, the current index is (n + 1) / 2.
        # Save this power before the final doubling to index n + 1.
        if r == s - 1:
            q_half = qk

        # Double the index.
        u, v, qk = (
            u * v % n,
            (v * v - 2 * qk) % n,
            qk * qk % n,
        )

    # The index is now n + 1.
    if not strong_ok:
        return False

    # Lucas-V probable-prime condition:
    #
    # V_{n+1} == 2Q mod n
    if v != (2 * q) % n:
        return False

    # Euler criterion for Q:
    #
    # Q^((n+1)/2) == Q * (Q/n) mod n
    # Use BFW's multiplied form directly; do not divide by Q modulo n.
    if q_half != (q * jacobi_symbol(q, n)) % n:
        return False

    return True


def isprime_bpsw(n: int) -> bool:
    """
    Standard strong Baillie-PSW probable-prime test.

    1. Base-2 strong Miller-Rabin
    2. Strong Lucas probable-prime test using Method A/A* (this wrapper uses A*)
    The BFW appendix proves Method A/A* equivalence for the strong Lucas test,
    not for the additional Lucas-V test in the strengthened variant.
    """
    return (
        n == 2
        or (
            n > 1
            and (n & 1) == 1
            and isprime_miller_base2(n)
            and isprime_lucas_strong_a_star(n)
        )
    )


def isprime_strengthened_bpsw(n: int) -> bool:
    """
    Strengthened Baillie-PSW probable-prime test.
    Implements the five steps in BFW Section 6 (called "enhanced" there).
    True means probable prime, not a primality certificate for arbitrary-size n.
    The suggested preliminary trial division by small primes is omitted here;
    it is an efficiency optimization, not an additional acceptance condition.

    1. Base-2 strong Miller-Rabin
    2. Lucas parameter selection using Method A*
    3. Strong Lucas probable-prime test
    4. Lucas-V probable-prime test
    5. Euler criterion for Q

    Return True for n == 2, and False for n < 2 or any other even n.
    """
    return (
        n == 2
        or (
            n > 1
            and (n & 1) == 1
            and isprime_miller_base2(n)
            and isprime_lucas_strengthened(n)
        )
    )


def main() -> None:
    import sys
    # Comparison/aggregation driver, not the five-step BFW test itself.
    # The 7- and 13-base MR results do not affect either BPSW return value;
    # agreement between these fixed lists is not a general primality certificate.
    BASES_7 = [2, 325, 9375, 28178, 450775, 9780504, 1795265022]
    BASES_13 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
    count = 0
    count_base2 = 0
    count_bases7 = 0
    count_bases13 = 0
    count_lucas = 0
    count_bpsw = 0
    count_strengthened = 0
    while True:
        line = sys.stdin.readline().rstrip()
        if not line:
            break
        n = int(line)
        assert n > 1 and (n & 1) == 1, 'value must be 3 or greater odd integer'
        f_base2 = isprime_miller_base2(n)
        f_bases7 = isprime_miller_bases(n, BASES_7)
        f_bases13 = isprime_miller_bases(n, BASES_13)
        f_lucas = isprime_lucas_strong_a_star(n)
        f_bpsw = isprime_bpsw(n)
        f_strengthened = isprime_strengthened_bpsw(n)
        count += 1
        count_base2 += f_base2
        count_bases7 += f_bases7
        count_bases13 += f_bases13
        count_lucas += f_lucas
        count_bpsw += f_bpsw
        count_strengthened += f_strengthened
        if f_bases7 and f_bases13 and not f_strengthened:
            print('bases7 and bases13 but not strengthened', n)
    print(
        count,
        count_base2,
        count_bases7,
        count_bases13,
        count_lucas,
        count_bpsw,
        count_strengthened,
    )


if __name__ == '__main__':
    main()
