/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ClippedLogRatio
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences

/-! # Scaled logarithmically weighted Mangoldt sums -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For positive scale x and u>=0, the clipped logarithmic atom at n/x is
log(xu/n) exactly when n is at most floor(xu), and zero otherwise. Compare the
real cutoff with its natural floor and cancel the scaling denominator.
This aligns continuous atoms with the project's finite arithmetic convention. -/
private theorem positiveLogRatio_nat {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) {n : ℕ} :
    Analysis.positiveLogRatio ((n : ℝ) / x) u =
      if n ≤ ⌊x * u⌋₊ then Real.log (x * u / n) else 0 := by
  have hxu : 0 ≤ x * u := mul_nonneg hx.le hu
  by_cases h : n ≤ ⌊x * u⌋₊
  · have hreal := (Nat.le_floor_iff hxu).mp h
    have hdiv : (n : ℝ) / x ≤ u := (div_le_iff₀ hx).mpr (by linarith only [hreal])
    rw [ite_eq_left h, Analysis.positiveLogRatio_eq_log hdiv, div_div_eq_mul_div]
    congr 2
    ring
  · have hreal : x * u ≤ (n : ℝ) := (le_of_not_ge (fun hb ↦ h ((Nat.le_floor_iff hxu).mpr hb)))
    have hdiv : u ≤ (n : ℝ) / x := (le_div_iff₀ hx).mpr (by linarith only [hreal])
    rw [ite_eq_right h, Analysis.positiveLogRatio_zero hdiv]

/-- For positive x and 0<=u<=y, express the logarithmically weighted sum at xu
as a finite combination of clipped logarithms on the common index set through floor(xy).
Pad with zero terms and apply the scaled atom identity.
This gives a fixed finite sum for interchanging summation and integration. -/
theorem logWeightedMangoldtSum_eq_clipped_scaled {x y u : ℝ} (hx : 0 < x) (hu : 0 ≤ u)
    (huy : u ≤ y) :
    logWeightedMangoldtSum (x * u) =
      ∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
        ArithmeticFunction.vonMangoldt n * Analysis.positiveLogRatio ((n : ℝ) / x) u := by
  rw [logWeightedMangoldtSum_eq_extended (mul_le_mul_of_nonneg_left huy hx.le)]
  apply Finset.sum_congr rfl
  intro n _
  rw [positiveLogRatio_nat hx hu, logWeightedMangoldtTerm]
  by_cases h : n ≤ ⌊x * u⌋₊
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h, mul_zero]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
