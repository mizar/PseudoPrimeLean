// C++: Strengthening the Baillie-PSW primality test
// https://homes.cerias.purdue.edu/~ssw/bfw.pdf
// https://arxiv.org/abs/2006.14425
// BFW-* audit tasks are tracked in PseudoPrimeWork/BPSW_execution_alignment_plan.md.
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/multiprecision/integer.hpp>

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <iostream>
#include <limits>
#include <optional>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>

namespace bpsw_strengthened {

namespace mp = boost::multiprecision;
using bigint = mp::cpp_int;

// Return x modulo positive n, normalized to 0 <= r < n.
// Lean ReferenceArithmetic.referenceNormalize_eq proves this normalization equals emod.
bigint mod(bigint x, const bigint& n) {
    assert(n > 0);
    x %= n;
    if (x < 0) x += n;
    return x;
}

// Guard before Boost computes limb_index * limb_bits in msb/lsb.
// The supported domain requires this bound for every operand inspected for bits.
// Exceeding it is an execution error, never a composite/probable-prime result.
void require_bit_index_capacity(const bigint& x) {
    constexpr std::size_t max_limbs =
        std::numeric_limits<std::size_t>::max() / bigint::backend_type::limb_bits;
    if (x.backend().size() > max_limbs) {
        throw std::length_error("BPSW bit index exceeds size_t capacity");
    }
}

// Return the bit length of nonnegative x, or 0 if x is zero.
// Boost msb/lsb and all reference bit counters use size_t without narrowing.
std::size_t bit_length(const bigint& x) {
    assert(x >= 0);
    require_bit_index_capacity(x);
    return x == 0 ? 0 : mp::msb(x) + 1;
}

// Return the exponent of the largest power of 2 dividing positive x.
std::size_t v2(const bigint& x) {
    assert(x > 0);
    require_bit_index_capacity(x);
    return mp::lsb(x);
}

// Return whether integer x is odd, including negative values.
bool is_odd(const bigint& x) {
    return mod(x, bigint(2)) != 0;
}

// Miller-Rabin probable-prime test for all the specified bases.
// n must be odd and at least 3. Reduce each base modulo n and skip zero residues.
// Skipping a zero residue is a convention for fixed base lists, not a passed
// Miller-Rabin round. The BPSW wrapper uses base 2, which is nonzero for odd n >= 3.
template <class Range>
bool isprime_miller_bases(const bigint& n, const Range& bases) {
    assert(n > 2 && is_odd(n));
    require_bit_index_capacity(n);

    const bigint n1 = n - 1;
    const std::size_t s = v2(n1);
    const bigint d = n1 >> s;

    for (const auto& base : bases) {
        bigint a = mod(bigint(base), n);
        if (a == 0) continue;

        bigint t = mp::powm(a, d, n);
        if (t == 1) continue;

        for (std::size_t r = 0;; ++r) {
            // BFW Section 2.2 checks only r < s for strong acceptance. Its extra
            // square to exponent n-1 is unnecessary once this last check fails.
            if (t == n1) break;
            if (r == s - 1) return false;
            t = mod(t * t, n);
        }
    }
    return true;
}

// Miller-Rabin probable-prime test to base 2.
// https://oeis.org/A001262 : Strong pseudoprimes to base 2.
bool isprime_miller_base2(const bigint& n) {
    static constexpr std::array<std::uint64_t, 1> bases{2};
    return isprime_miller_bases(n, bases);
}

// Return floor(sqrt(n)) for nonnegative n.
// Lean ReferenceArithmetic.newtonSqrt_eq proves the Newton procedure equals Nat.sqrt.
bigint isqrt(const bigint& n) {
    assert(n >= 0);
    if (n < 2) return n;
    require_bit_index_capacity(n);

    const std::size_t bits = bit_length(n - 1);
    // ceil(bits / 2), without forming bits + 1 at the finite-width boundary.
    const std::size_t k = bits / 2 + bits % 2;
    bigint s = bigint(1) << k;
    bigint t = (s + (n >> k)) >> 1;
    while (s > t) {
        s = t;
        t = (t + n / t) >> 1;
    }
    return s;
}

// Return whether n is a perfect square. Reject negative values, apply a
// quadratic-residue filter modulo 8, then test r * r == n for the integer square root r.
// Lean ReferenceArithmetic.referenceSquare_eq proves the mask preserves the square test.
bool issq(const bigint& n) {
    if (n < 0) return false;
    const unsigned residue8 = mod(n, bigint(8)).convert_to<unsigned>();
    if (((std::uint32_t{0x13} >> residue8) & 1U) == 0) return false;
    const bigint r = isqrt(n);
    return r * r == n;
}

// Return the Jacobi symbol (a/n) for integer a and positive odd n.
// The result is one of -1, 0, and 1.
//
// For positive odd n, this agrees with the Kronecker symbol.
// The result is 0 if and only if gcd(a, n) > 1.
//
// When n is prime, a result of 1 indicates a nonzero quadratic residue,
// and a result of -1 indicates a quadratic nonresidue.
// For composite n, a result of 1 does not necessarily imply a quadratic residue.
int jacobi_symbol(bigint a, bigint n) {
    assert(n > 0 && is_odd(n));

    int j = 1;
    // a is an integer; n is positive and odd.
    // (-a/n) = (-1/n)(a/n),
    // (-1/n) = -1 iff n ≡ 3 (mod 4)
    if (a < 0) {
        a = -a;
        if (mod(n, bigint(4)) == 3) j = -j;
    }

    // a is nonnegative.
    while (a != 0) {
        // a is positive.
        // (2a/n) = (2/n)(a/n)
        //
        // (2/n) = -1 iff n ≡ 3, 5 (mod 8),
        // (2/n) =  1 iff n ≡ 1, 7 (mod 8)
        const std::size_t b = v2(a);
        // Python removes one factor of 2 per iteration; this batches the same
        // Jacobi(2, n)^b sign changes using only the parity of b.
        // Lean ReferenceArithmetic.jacobiCppBatch_eq proves the factored-input identity.
        a >>= b;

        if ((b & 1U) != 0) {
            const unsigned n8 = mod(n, bigint(8)).convert_to<unsigned>();
            if (n8 == 3 || n8 == 5) j = -j;
        }

        // Both a and n are positive and odd.
        //
        // (a/n)(n/a) = -1 iff a ≡ n ≡ 3 (mod 4),
        // (a/n)(n/a) =  1 otherwise
        // (a/n) = (a mod n/n)
        //
        // Use these identities to exchange a and n and reduce the new numerator.
        if (mod(a, bigint(4)) == 3 && mod(n, bigint(4)) == 3) {
            j = -j;
        }

        n = mod(n, a);
        n.swap(a);
    }

    // If n == 1, then j * (0/1) = j because (0/1) = 1.
    // If n > 1, then j * (0/n) = 0 because (0/n) = 0.
    return n == 1 ? j : 0;
}

// Return the Kronecker symbol (a/n) for integers a and n.
// Handle a zero denominator, its sign, and its power-of-two factor first,
// then delegate the positive odd denominator to the Euclidean-style jacobi_symbol.
int kronecker_symbol(bigint a, bigint n) {
    // (a/0) = 1 iff a = +/-1; otherwise it is 0.
    if (n == 0) return (a == 1 || a == -1) ? 1 : 0;

    int j = 1;

    // Handle the factor (a/-1) from a negative denominator.
    if (n < 0) {
        n = -n;
        if (a < 0) j = -j;
    }

    // Extract the power-of-two factor from the denominator.
    const std::size_t t = v2(n);
    if (t != 0) {
        if (!is_odd(a)) return 0;

        if ((t & 1U) != 0) {
            const unsigned a8 = mod(a, bigint(8)).convert_to<unsigned>();
            if (a8 == 3 || a8 == 5) j = -j;
        }
        n >>= t;
    }

    // The remaining denominator is positive and odd (possibly 1).
    return j * jacobi_symbol(a, n);
}

inline constexpr std::array<unsigned, 10> SELFRIDGE_PREFIX{
    5, 7, 9, 11, 13, 15, 17, 19, 23, 29
};
inline constexpr std::array<unsigned, 8> SELFRIDGE_WHEEL30{
    1, 7, 11, 13, 17, 19, 23, 29
};

// Generate Selfridge |D| candidates incrementally.
// After the initial candidates, add Wheel30 residues to base = 30, 60, ... .
// BFW Method A scans every odd |D| starting at 5; Wheel30 is an extra optimization.
// Keep 9 to detect a factor 3, and 15 to test the missing discriminant -3 via
// -15 = (-3)*5 once (5/n) = 1. Beyond this prefix, multiplicativity shows that
// a skipped multiple of 3 or 5 cannot be the first Jacobi value different from 1.
// This preserves the first stop of the scan with BFW factor detection, not an
// unrestricted search that ignores Jacobi-zero candidates.
class SelfridgeAbsCandidates {
public:
    bigint next() {
        if (prefix_index_ < SELFRIDGE_PREFIX.size()) {
            return bigint(SELFRIDGE_PREFIX[prefix_index_++]);
        }
        bigint candidate = base_ + SELFRIDGE_WHEEL30[wheel_index_];
        if (++wheel_index_ == SELFRIDGE_WHEEL30.size()) {
            wheel_index_ = 0;
            base_ += 30;
        }
        return candidate;
    }

private:
    std::size_t prefix_index_ = 0;
    std::size_t wheel_index_ = 0;
    bigint base_ = 30;
};

// Run the Selfridge scan with BFW factor detection and return (D, s).
// (0, 0): n is a perfect square.
// (D, -1): D was selected with Jacobi (D/n) = -1.
// (D, 0): n does not divide |D| and Jacobi (D/n) = 0 detects a nontrivial factor.
std::pair<bigint, int> lucas_selfridge_scan(const bigint& n) {
    assert(n > 2 && is_odd(n));

    // BFW suggests a square check after several unsuccessful candidates.
    // Checking up front also makes this helper terminate when used without MR.
    if (issq(n)) return {0, 0};

    // Here n >= 3 is odd and nonsquare. The relevant stop is firstStopNeOne:
    // the least candidate i with n not dividing i and Jacobi(D/n) != 1.
    // Lean: PrimeTest/Selfridge/WitnessBounds.lean,
    // classicalFirstStopNeOne_lt_of_odd_nonsquare_of_fifteen_lt gives i < n
    // unconditionally for n > 15. The remaining inputs 3, 5, 7, 11, 13, 15
    // stop at 5, 7, 5, 13, 5, 5, respectively, so i < 2*n holds throughout.
    // PrimeTest/Selfridge/Wheel30.lean: firstStopNeOne_wheel30_eq_classical
    // preserves this mathematical first stop, including factor detection.
    // PrimeTest/Selfridge/Composite.lean:
    // composite_minimal_classical_neOne_eq_nine_or_fifteen shows that a composite
    // first stopping candidate must be 9 or 15. Thus a stop with i > 15 is prime;
    // no composite candidate above 15 can be the first stop of this scan.
    // Accordingly, for i > 30 the generator skips residues modulo 30 that are
    // divisible by 2, 3, or 5 and hence composite. It tests only residues
    // 1, 7, 11, 13, 17, 19, 23, 29; the initial prefix retains 9 and 15.
    // Under GRH, PrimeTestBounds/Selfridge/LogGRH.lean:
    // classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_max_thirteen_log_sq_of_grh
    // gives i <= max(13, (log n)^2); for n >= 13 the bound is (log n)^2.
    // log is natural. These bounds concern i = |D|, not the iteration count.
    // This scan uses no GRH assumption or numerical cutoff; equivalence of these
    // Python/C++ programs to the Lean first-stop specification is not formalized.
    SelfridgeAbsCandidates candidates;
    for (bigint i = candidates.next(); ; i = candidates.next()) {
        // For 0 < i < 2*n, gcd(i, n) == n iff n divides i iff i == n,
        // so checking only i == n excludes every case with gcd(i, n) == n.
        // BFW states the general n-does-not-divide-|D| check; this simplification
        // relies on the separate first-stop bound, also preserved by Wheel30.
        // Lean EqualityScan proves equality and divisibility exclusions agree for
        // odd nonsquares at every fuel budget (BFW-L2); production keeps divisibility.
        if (i == n) continue;

        const bigint d = (mod(i, bigint(4)) == 1) ? i : -i;
        const int j = jacobi_symbol(d, n);

        if (j == -1) return {d, -1};

        if (j == 0) {
            // The unconditional bound places the stopping candidate below 2*n. Since i != n,
            // Jacobi == 0 implies 1 < gcd(i, n) < n.
            return {d, 0};
        }
    }
}

// Return D for Lucas parameter selection only when s = -1.
std::optional<bigint> lucas_selfridge_d(const bigint& n) {
    auto [d, s] = lucas_selfridge_scan(n);
    if (s != -1) return std::nullopt;
    return d;
}

// Return (P, Q) using Selfridge Method A.
// For the selected D, always use P = 1 and Q = (1 - D) / 4.
// In particular, D = 5 gives (P, Q) = (1, -1).
std::optional<std::pair<bigint, bigint>> lucas_params_a(const bigint& n) {
    const auto d = lucas_selfridge_d(n);
    if (!d) return std::nullopt;
    return std::pair<bigint, bigint>{1, (1 - *d) / 4};
}

// Return (P, Q) using Selfridge Method A*. n must be odd and at least 3.
// Return std::nullopt if a perfect square or a nontrivial factor is detected.
// For D != 5, use P = 1 and Q = (1 - D) / 4, as in Method A.
// Only for D = 5, use (P, Q) = (5, 5), preserving D = P^2 - 4Q = 5.
// Use Wheel30 without an upper limit on the search range.
std::optional<std::pair<bigint, bigint>> lucas_params_a_star(const bigint& n) {
    const auto d = lucas_selfridge_d(n);
    if (!d) return std::nullopt;
    if (*d == 5) return std::pair<bigint, bigint>{5, 5};
    return std::pair<bigint, bigint>{1, (1 - *d) / 4};
}

// Return x / 2 modulo positive odd n.
// If x is odd, add n to make it even before dividing by 2.
// Normalize the result to 0 <= r < n.
bigint div2_mod_odd(bigint x, const bigint& n) {
    assert(n > 0 && is_odd(n));
    if (is_odd(x)) x += n;
    // The numerator is now exactly even, including for negative x. Hence C++'s
    // truncating division agrees with Python's arithmetic right shift here.
    // Lean Lucas/ReferenceProcedure.lean: signedHalf_eq proves the raw parity-adjusted half
    // equals residue-first halving for odd n; signedHalf_division_modes covers negatives.
    return mod(x / 2, n);
}

// Lucas computation state holding (U_k mod n, V_k mod n, Q^k mod n).
struct LucasUVQ {
    bigint u;
    bigint v;
    bigint qk;
};

// For positive odd n and nonnegative k, compute the Lucas sequence values
// (U_k mod n, V_k mod n, Q^k mod n) using the binary method.
// Set D = P^2 - 4Q and use the following identities.
//
// U_{2k} = U_k V_k
// V_{2k} = V_k^2 - 2 Q^k
// Q^{2k} = (Q^k)^2
//
// U_{k+1} = (P U_k + V_k) / 2
// V_{k+1} = (D U_k + P V_k) / 2
// Q^{k+1} = Q Q^k
LucasUVQ lucas_uvq_mod(const bigint& n, const bigint& p,
                       const bigint& q, const bigint& k) {
    assert(n > 0 && is_odd(n));
    assert(k >= 0);
    require_bit_index_capacity(n);

    if (k == 0) {
        return {0, mod(2, n), mod(1, n)};
    }

    const bigint disc = p * p - 4 * q;

    // Initialize the values corresponding to the leading 1 bit of the index.
    // Lean lucasUVQ starts at index 0 and also processes this leading bit.
    // Lean Lucas/ReferenceProcedure.lean: leading_eq proves both triple initializations agree
    // for odd n and every index, including 0 and 1 (BFW-L3).
    // U_1 = 1, V_1 = P, Q^1 = Q
    bigint u = mod(1, n);
    bigint v = mod(p, n);
    bigint qk = mod(q, n);

    // The leading bit has already been processed; start with the next bit.
    // k > 0, so bits >= 1. Decrement before use: bits-2, ..., 0.
    // No signed conversion or unsigned wrap is needed, including the k == 1 case.
    for (std::size_t bit = bit_length(k) - 1; bit > 0;) {
        --bit;
        // For the processed binary prefix m, (u, v, qk) = (U_m, V_m, Q^m) mod n.
        // Double the index.
        u = mod(u * v, n);
        v = mod(v * v - 2 * qk, n);
        qk = mod(qk * qk, n);

        // If the current bit is 1, increment the index.
        if (((k >> bit) & 1) != 0) {
            const bigint old_u = u;
            const bigint old_v = v;

            u = div2_mod_odd(p * old_u + old_v, n);
            v = div2_mod_odd(disc * old_u + p * old_v, n);
            qk = mod(qk * q, n);
        }
    }

    return {std::move(u), std::move(v), std::move(qk)};
}

// Shared core testing the strong Lucas condition for fixed (P, Q).
// The caller must supply an odd n >= 3 with Jacobi(P*P - 4*Q, n) == -1
// for the BFW interpretation: delta(n) is then n + 1. This helper checks only
// the congruences; it neither selects parameters nor verifies that hypothesis.
// The prime-input guarantee also assumes gcd(n, Q) == 1, as in BFW Section 2.3.
bool isprime_lucas_strong_pq(const bigint& n, const bigint& p, const bigint& q) {
    assert(n > 2 && is_odd(n));

    // s = v_2(n + 1) is the 2-adic valuation of n + 1.
    // n + 1 = odd_part * 2^s, where d = odd_part is odd.
    const bigint delta = n + 1;
    const std::size_t s = v2(delta);

    // Compute U_d, V_d, and Q^d.
    auto [u, v, qk] = lucas_uvq_mod(n, p, q, delta >> s);

    // The strong Lucas condition holds if U_d == 0.
    if (u == 0) return true;

    // Test V_{d 2^r} for 0 <= r < s before doubling the index.
    for (std::size_t r = 0;; ++r) {
        if (v == 0) return true;
        if (r == s - 1) return false;
        v = mod(v * v - 2 * qk, n);
        qk = mod(qk * qk, n);
    }
}

// Strong Lucas probable-prime test using Method A.
bool isprime_lucas_strong_a(const bigint& n) {
    assert(n > 2 && is_odd(n));
    const auto params = lucas_params_a(n);
    if (!params) return false;
    return isprime_lucas_strong_pq(n, params->first, params->second);
}

// Strong Lucas probable-prime test using Method A*.
bool isprime_lucas_strong_a_star(const bigint& n) {
    assert(n > 2 && is_odd(n));
    const auto params = lucas_params_a_star(n);
    if (!params) return false;
    return isprime_lucas_strong_pq(n, params->first, params->second);
}

// Strengthened strong Lucas probable-prime test using Method A*.
// Test all three of the following conditions.
// These are BFW Section 6, steps 3-5; base-2 MR is performed by the BPSW wrapper.
// 1. strong Lucas probable-prime condition
// 2. V_{n+1} == 2Q mod n
// 3. Q^((n+1)/2) == Q * jacobi_symbol(Q, n) mod n
bool isprime_lucas_strengthened(const bigint& n) {
    assert(n > 2 && is_odd(n));

    const auto params = lucas_params_a_star(n);
    if (!params) return false;
    const auto& [p, q] = *params;

    // s = v_2(n + 1) is the 2-adic valuation of n + 1.
    // n + 1 = odd_part * 2^s, with odd_part odd and s >= 1.
    const bigint delta = n + 1;
    const std::size_t s = v2(delta);
    const bigint odd_part = delta >> s;

    // Compute U_d, V_d, and Q^d, where d = odd_part.
    auto [u, v, qk] = lucas_uvq_mod(n, p, q, odd_part);

    // Strong Lucas condition: U_d == 0, or for some 0 <= r < s,
    // V_{d 2^r} == 0.
    bool strong_ok = (u == 0);

    // Do not return immediately on strong Lucas success: steps 4 and 5 still
    // need V_{n+1} and Q^{(n+1)/2}. All congruences use residues modulo n.
    for (std::size_t r = 0;; ++r) {
        // At entry: v = V_(d * 2^r), qk = Q^(d * 2^r) mod n, d = odd_part.
        // strong_ok records U_d == 0 or a zero V at an earlier index d * 2^j, j < r.
        if (v == 0) strong_ok = true;
        // Double V first; retain the half-index Q power on the final iteration.
        v = mod(v * v - 2 * qk, n);
        if (r == s - 1) break;
        qk = mod(qk * qk, n);
    }

    // At exit: v = V_(n + 1), qk = Q^((n + 1) / 2) mod n.
    // strong_ok includes exactly the V checks for 0 <= r < s, excluding V_(n + 1).
    if (!strong_ok) return false;

    // Lucas-V probable-prime condition: V_{n+1} == 2Q mod n
    if (v != mod(2 * q, n)) return false;

    // With D = P*P - 4*Q and Jacobi(D, n) == -1, passing Lucas-V implies
    // gcd(Q, n) == 1, even for composite n; no Strong assumption is needed.
    // A common prime divisor ell would give Q == 0 mod ell and V_k == P^k
    // for k > 0. The unit discriminant forces P != 0 mod ell, contradicting
    // V_(n+1) == 2*Q == 0 mod ell. Thus no separate gcd check is needed here,
    // and the multiplied Euler form is equivalent to the unmultiplied form.
    // Lean: PseudoPrime.PrimeTest.lucasV_q_coprime (StrongLucas/NoGcd.lean).
    // Euler criterion for Q: Q^((n+1)/2) == Q * (Q/n) mod n
    // BFW Section 6, suggestion 4: this adds no strength after base-2 MR when
    // |Q| is a power of 2. Keep the check: this helper does not assume MR passed.
    // Use BFW's multiplied form directly; do not divide by Q modulo n.
    if (qk != mod(q * jacobi_symbol(q, n), n)) return false;

    return true;
}

// Standard strong Baillie-PSW probable-prime test.
// 1. Base-2 strong Miller-Rabin
// 2. Strong Lucas probable-prime test using Method A/A* (this wrapper uses A*)
// The BFW appendix proves Method A/A* equivalence for the strong Lucas test,
// not for the additional Lucas-V test in the strengthened variant.
// Return true for n == 2, and false for n < 2 or any other even n.
bool isprime_bpsw(const bigint& n) {
    return n == 2 ||
           (n > 1 && is_odd(n) && isprime_miller_base2(n) &&
            isprime_lucas_strong_a_star(n));
}

// Strengthened Baillie-PSW probable-prime test.
// Implements the five steps in BFW Section 6 (called "enhanced" there).
// True means probable prime, not a primality certificate for arbitrary-size n.
// The suggested preliminary trial division by small primes is omitted here;
// it is an efficiency optimization, not an additional acceptance condition.
// 1. Base-2 strong Miller-Rabin
// 2. Lucas parameter selection using Method A*
// 3. Strong Lucas probable-prime test
// 4. Lucas-V probable-prime test
// 5. Euler criterion for Q
// Return true for n == 2, and false for n < 2 or any other even n.
bool isprime_strengthened_bpsw(const bigint& n) {
    return n == 2 ||
           (n > 1 && is_odd(n) && isprime_miller_base2(n) &&
            isprime_lucas_strengthened(n));
}

}  // namespace bpsw_strengthened

#ifndef BPSW_STRENGTHENED_NO_MAIN
int main() {
    using bpsw_strengthened::bigint;
    using namespace bpsw_strengthened;

    // Comparison/aggregation driver, not the five-step BFW test itself.
    // The 7- and 13-base MR results do not affect either BPSW return value;
    // agreement between these fixed lists is not a general primality certificate.
    static constexpr std::array<std::uint64_t, 7> BASES_7{
        2, 325, 9375, 28178, 450775, 9780504, 1795265022
    };
    static constexpr std::array<std::uint64_t, 13> BASES_13{
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41
    };

    std::uint64_t count = 0;
    std::uint64_t count_base2 = 0;
    std::uint64_t count_bases7 = 0;
    std::uint64_t count_bases13 = 0;
    std::uint64_t count_lucas = 0;
    std::uint64_t count_bpsw = 0;
    std::uint64_t count_strengthened = 0;

    std::string line;
    while (std::getline(std::cin, line)) {
        if (line.empty()) break;

        bigint n(line);
        assert(n > 1 && is_odd(n));
        // All success counters are bounded by count; reject before any can wrap.
        if (count == std::numeric_limits<std::uint64_t>::max()) {
            throw std::overflow_error("BPSW CLI input count exceeds uint64_t capacity");
        }

        const bool f_base2 = isprime_miller_base2(n);
        const bool f_bases7 = isprime_miller_bases(n, BASES_7);
        const bool f_bases13 = isprime_miller_bases(n, BASES_13);
        const bool f_lucas = isprime_lucas_strong_a_star(n);
        const bool f_bpsw = isprime_bpsw(n);
        const bool f_strengthened = isprime_strengthened_bpsw(n);

        ++count;
        count_base2 += f_base2;
        count_bases7 += f_bases7;
        count_bases13 += f_bases13;
        count_lucas += f_lucas;
        count_bpsw += f_bpsw;
        count_strengthened += f_strengthened;

        if (f_bases7 && f_bases13 && !f_strengthened) {
            std::cout << "bases7 and bases13 but not strengthened " << n << '\n';
        }
    }

    std::cout << count << ' ' << count_base2 << ' ' << count_bases7 << ' '
              << count_bases13 << ' ' << count_lucas << ' '
              << count_bpsw << ' ' << count_strengthened << '\n';
}
#endif
