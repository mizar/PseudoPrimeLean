/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.AnalyticPrimeSupplyData
public import PseudoPrime.Analysis.HighPrecisionLogBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareLocalCounting
public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeLocalCounting

/-! # Square and semiprime witness bounds at 1600 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, at least 189 primes are at most 1600. The first entry of the analytic supply
table provides the count independently of the repeated-product degree. -/
theorem prime_count_1600_ge_189 (hRH : RiemannHypothesis) : 189 ≤ (1600 : ℕ).primeCounting := by
  have hc : (⟨40, 189, 16, 11, 737777 / 100000⟩ : AnalyticPrimeSupply) ∈ analyticSupplies01 := by
    simp only [analyticSupplies01, List.mem_cons, true_or]
  have h := analyticSupplies01_sound hRH _ hc
  norm_num only at h
  exact h

set_option maxRecDepth 16384 in
/-- For cutoff 1600, supply 189 and degree 3, the displayed rational endpoints bound
`3 log 1600` above and `log (choose 192 3)` strictly below. Taylor certificates provide
the bounds used by the square and semiprime counting criteria. -/
theorem count_1600_degree_three_logs :
    (3 : ℝ) * Real.log 1600 ≤ (5533319181171 / 250000000000 : ℝ) ∧
      (3491258350751 / 250000000000 : ℝ) < Real.log (Nat.choose (189 + 3) 3 : ℝ) := by
  have hb : Analysis.preciseLogCheck 1600 11 64 7 (1844439727057 / 250000000000) = true := by
    decide +kernel
  have hc :
    Analysis.fineLogCheck 1161280 21 128 (3491258350751 / 250000000000 + 1 / 1000000000000000000)
        (13965033403009 / 1000000000000) =
      true := by
    decide +kernel
  have hb' := (Analysis.preciseLogCheck_sound hb).2
  have hc' := (Analysis.fineLogCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_add, Nat.reduceAdd, Nat.choose] at hb' hc' ⊢
  constructor
  · linarith only [hb']
  · linarith only [hc']

/-- Under RH, an odd prime square in the displayed logarithmic interval has a rejecting
prime at most 1600. Apply the degree-three criterion to the analytic supply and log bounds. -/
theorem exists_prime_reject_square_1600 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hRH : RiemannHypothesis)
    (hlo : (5533319181171 / 250000000000 : ℝ) < Real.log n)
    (hhi : Real.log n ≤ 2 * (3491258350751 / 250000000000 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 1600 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_square_candidate hn ho hp hp2 hpow (by norm_num only)
      (prime_count_1600_ge_189 hRH) count_1600_degree_three_logs.1 hlo hhi
      count_1600_degree_three_logs.2

/-- Under GRH, an odd product of distinct primes has a rejecting prime bounded by the
degree-three candidate at 1600. The RH supply and logarithm certificate discharge the
arithmetic hypotheses of the local-or-counting witness theorem. -/
theorem exists_prime_reject_semiprime_1600 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤
          max 1600
            (localFullEnvelope
              (max (5533319181171 / 250000000000) (Real.log n - (3491258350751 / 250000000000)))) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_candidate hn ho hp hq hpq hprod (by norm_num only)
      (prime_count_1600_ge_189 hGRH.riemann) hGRH count_1600_degree_three_logs.1
      count_1600_degree_three_logs.2.le

end PseudoPrime.PrimeTestBounds.MillerRabin
