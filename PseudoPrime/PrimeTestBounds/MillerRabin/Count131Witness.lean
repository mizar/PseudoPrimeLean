/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.CountCandidate131
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareLocalCounting
public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeLocalCounting

/-! # Square and semiprime witness bounds at 131 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd prime square in the stated interval has a rejecting prime at most 131. The
degree-three repeated-product criterion uses the certified prime supply and logarithm bounds. -/
theorem exists_prime_reject_square_131 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hlo : (7312795984803 / 500000000000 : ℝ) < Real.log n)
    (hhi : Real.log n ≤ 2 * (1098307084793 / 125000000000 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 131 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_square_candidate hn ho hp hp2 hpow (by norm_num only) prime_count_131_ge_32
      count_131_degree_three_logs.1 hlo hhi count_131_degree_three_logs.2

/-- Under GRH, an odd product of distinct primes has a rejecting prime bounded by the
degree-three candidate at 131. Apply the local-or-counting criterion to its certified supply
and logarithm bounds. -/
theorem exists_prime_reject_semiprime_131 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤
          max 131
            (localFullEnvelope
              (max (7312795984803 / 500000000000) (Real.log n - (1098307084793 / 125000000000)))) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_candidate hn ho hp hq hpq hprod (by norm_num only)
      prime_count_131_ge_32 hGRH count_131_degree_three_logs.1 count_131_degree_three_logs.2.le

end PseudoPrime.PrimeTestBounds.MillerRabin
