/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterIntersection200
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSmallInputs

/-! # Maximum cutoff and least witness through logarithmic scale 200 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, odd composites with logarithm at most 200 admit a rejecting prime
within the maximum quarter-square cutoff. The interval bounds cover the input. -/
theorem quarter_max_through200 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hU : Real.log n ≤ 200) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((1 / 4 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hN : n < 3000
  · exact exists_prime_reject_quarter_small hn ho hc hN
  have hn3000 : 3000 ≤ n := Nat.le_of_not_gt hN
  have hlog3000 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3000 12 12 8 (801 / 100) = true by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlog3000
  have ht := Real.log_le_log (by norm_num only : (0 : ℝ) < 3000) (Nat.cast_le.mpr hn3000)
  have h8 : (8 : ℝ) ≤ Real.log n := hlog3000.trans ht
  obtain ⟨p, hp, hb, hf⟩ := quarter_all_8_200 hn ho hc hGRH h8 hU
  exact ⟨p, hp, hb.trans (le_max_right _ _), hf⟩

/-- Under GRH, the least rejecting prime satisfies the maximum quarter-square bound
when the logarithm of an odd composite is at most 200. Extract it from the witness. -/
theorem quarter_least_through200 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hU : Real.log n ≤ 200) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((1 / 4 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject (quarter_max_through200 hn ho hc hGRH hU)

end PseudoPrime.PrimeTestBounds.MillerRabin
