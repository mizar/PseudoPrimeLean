/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSignedEulerIntervals

/-! # Upper row bounds and exact prime-power support reindexing -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The rational upper Mangoldt allowance for an existing prime-power row
and any signed coefficient list. Reuse its logarithm and node intervals. -/
def GammaFiniteEulerRow.signedUpper (r : GammaFiniteEulerRow) (l : List (ℚ × ℚ)) : ℚ :=
  r.logUpper * finiteSignedEulerUpper l r.ratios

/-- A prime row with a successful parametric check bounds the actual signed
Mangoldt weight above. The nonnegative checked Euler lower endpoint supplies
the sign needed for the logarithm and Euler upper product. -/
theorem GammaFiniteEulerRow.le_signedUpper (r : GammaFiniteEulerRow) (l : List (ℚ × ℚ)) {d : ℕ}
    (hd : 0 < d) (hp : r.prime.Prime) (hc : r.signedCheck l d = true) :
    finiteSignedMangoldtWeight l r.index ≤ (r.signedUpper l : ℝ) := by
  obtain ⟨hb, hlo⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hpow, hlog⟩ := Bool.and_eq_true_iff.mp hb
  have he := finiteSigned_ratio_check_euler_bounds l hd hpow
  have hl := rationalLogIntervalCheck_sound hlog
  norm_num only [Rat.cast_natCast] at he hl
  have hw := ((Rat.cast_nonneg (K := ℝ)).mpr (of_decide_eq_true hlo)).trans he.1
  have hp0 := Real.log_natCast_nonneg r.prime
  have h := mul_le_mul hl.2 he.2 hw (hp0.trans hl.2)
  simpa only [GammaFiniteEulerRow.signedUpper, GammaFiniteEulerRow.index,
    finiteSignedMangoldtWeight, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Rat.cast_mul] using h

/-- A weight supported on prime powers has its exact finite prefix reindexed
by any row list whose distinct indices cover that support. This theorem is
independent of the coefficient list and the row representation. -/
theorem prime_power_supported_prefix_eq_rows {ι : Type*} (w : ℕ → ℝ)
    (hw : ∀ n, ¬IsPrimePow n → w n = 0) (rows : List ι) (idx : ι → ℕ) (hn : (rows.map idx).Nodup)
    (B : ℕ) (hc : (rows.map idx).toFinset = (Finset.Ioc 0 B).filter IsPrimePow) :
    (∑ n ∈ Finset.Ioc 0 B, w n) = (rows.map (fun r ↦ w (idx r))).sum := by
  have he : (∑ n ∈ (Finset.Ioc 0 B).filter IsPrimePow, w n) = ∑ n ∈ Finset.Ioc 0 B, w n :=
    Finset.sum_subset (Finset.filter_subset _ _)
      (fun n hn hnot ↦ hw n (fun h ↦ hnot (Finset.mem_filter.mpr ⟨hn, h⟩)))
  rw [← he, ← hc, List.sum_toFinset w hn, List.map_map]
  rfl

end PseudoPrime.Analysis
