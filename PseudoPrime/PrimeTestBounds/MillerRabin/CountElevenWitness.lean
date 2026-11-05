/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.CountCandidateEleven
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareLocalCounting
public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeLocalCounting

/-! # First square and semiprime repeated-product witness candidate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an odd prime square in the displayed logarithmic interval, a prime at
most eleven rejects the input. The certified five-prime supply and degree-two
logarithm bounds discharge the general repeated-product criterion. This is the
first square candidate in the planned coverage chain. -/
theorem exists_prime_reject_square_eleven {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hlo : (2397895272799 / 500000000000 : ℝ) < Real.log n)
    (hhi : Real.log n ≤ 2 * (3044522437723 / 1000000000000 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 11 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_square_candidate hn ho hp hp2 hpow (by norm_num only)
      prime_count_eleven_ge_five count_eleven_degree_two_logs.1 hlo hhi
      count_eleven_degree_two_logs.2

/-- Under GRH, an odd product of distinct primes has a rejecting prime bounded
by the first semiprime candidate, with cutoff eleven and the displayed local
threshold. Apply the general local-or-counting theorem to the certified supply
and degree-two logarithm bounds. This candidate participates in the finite
semiprime envelope. -/
theorem exists_prime_reject_semiprime_eleven {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤
          max 11
            (localFullEnvelope
              (max (2397895272799 / 500000000000) (Real.log n - (3044522437723 / 1000000000000)))) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_candidate hn ho hp hq hpq hprod (by norm_num only)
      prime_count_eleven_ge_five hGRH count_eleven_degree_two_logs.1
      count_eleven_degree_two_logs.2.le

set_option maxRecDepth 8192 in
/-- Every odd prime square with logarithm at most the first certified upper
endpoint has a rejecting prime at most eleven. Above the product-size threshold
use the degree-two count; below it, the prime factor itself is at most eleven.
This connects the first counting interval to the initial square range. -/
theorem exists_prime_reject_square_through_eleven {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hhi : Real.log n ≤ 2 * (3044522437723 / 1000000000000 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 11 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hlo : (2397895272799 / 500000000000 : ℝ) < Real.log n
  · exact exists_prime_reject_square_eleven hn ho hp hp2 hpow hlo hhi
  · have hcert : Analysis.preciseLogCheck 12 4 32 (12 / 5) 3 = true := by decide +kernel
    have hlog12 := (Analysis.preciseLogCheck_sound hcert).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog12
    have hp11 : p ≤ 11 := by
      by_contra hp11
      have hp12 : (12 : ℝ) ≤ p := by exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge hp11))
      have hpLog := Real.log_le_log (by norm_num only : (0 : ℝ) < 12) hp12
      have hnLog : Real.log n = 2 * Real.log p := by
        rw [hpow, Nat.cast_pow, Real.log_pow]
        norm_num only [Nat.cast_ofNat]
      linarith only [hlog12, hpLog, hnLog, le_of_not_gt hlo]
    have hdiv : p ∣ n := by
      rw [hpow]
      exact dvd_pow_self p (by decide : 2 ≠ 0)
    exact ⟨p, hp, hp11, PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hdiv⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
