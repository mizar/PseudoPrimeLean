/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.JointSurplusThresholds
public import PseudoPrime.PrimeTestBounds.MillerRabin.JointSurplusEnvelope

/-! # Gaussian entrance for the coefficient 0.4136 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- From logarithmic scale `3461/10`, the global Gaussian comparison is strictly below
`(517/1250) * L²`. A rational upper bound on the budget root certifies the endpoint,
and the existing normalized monotonicity transfers the estimate to larger scales. -/
theorem gaussian_global_lt_4136 {L : ℝ} (hL : (3461 / 10 : ℝ) ≤ L) :
    jointSurplusGlobal L < (517 / 1250 : ℝ) * L ^ 2 := by
  apply jointSurplus_threshold (T := 3461 / 10) (by norm_num only) hL
  apply
    jointSurplus_endpoint_cert (rho := 130) (R := 30) (B := 2478639 / 200000) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only [max_def, ite_false, ite_true])
  exact (min_le_right _ _).trans (min_le_left _ _)

/-- Under GRH, every odd composite with logarithm at least `3461/10` has a rejecting
prime within the coefficient `517/1250` bound. Apply the global Gaussian witness and
the certified high-scale coefficient estimate. -/
theorem exists_prime_reject_high_4136 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (3461 / 10 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (517 / 1250 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hf, hb, _⟩ := jointSurplus_least hn ho hc hGRH
  exact ⟨r, hr, hb.trans (gaussian_global_lt_4136 hL).le, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
