/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows59
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalUpperRows

/-! # Principal upper bound at cutoff 59 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The certified upper weight at index `n`, with zero for an unlisted index. -/
def quarterWeight59 (n : ℕ) : ℚ :=
  (((quarterUpperRows59.find? (fun r ↦ r.index == n)).getD ⟨59, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩).weight :
      ℚ) /
    1000000

/-- Every prime power through the support endpoint occurs in the upper row table. -/
theorem quarter_rows59_cover :
    ∀ n ∈ Finset.Ioc 0 826, IsPrimePow n → ∃ r ∈ quarterUpperRows59, r.index = n := by
  decide +kernel

/-- Every row in the table has the common cutoff 59. -/
theorem quarter_rows59_cut : ∀ r ∈ quarterUpperRows59, r.cut = 59 := by decide +kernel

/-- Every prime power through the support endpoint has a checked logarithm row. -/
theorem quarter_rows59_euler :
    ∀ n ∈ Finset.Ioc 0 826, IsPrimePow n → n ∈ refinedEulerPrefixSet := by decide +kernel

/-- The selected rational upper weight is nonnegative at every index. -/
theorem quarter_weight59_nonneg (n : ℕ) : 0 ≤ quarterWeight59 n := by
  unfold quarterWeight59
  positivity

/-- The selected row bounds the principal weight at each supported prime power. -/
theorem quarter_weight59_upper {n : ℕ} (hn : n ∈ Finset.Ioc 0 826) (hp : IsPrimePow n) :
    refinedScaledWeight 59 n ≤ (quarterWeight59 n : ℝ) := by
  obtain ⟨s, hs, hsn⟩ := quarter_rows59_cover n hn hp
  have hsome : (quarterUpperRows59.find? (fun r ↦ r.index == n)).isSome = true :=
    List.find?_isSome.mpr ⟨s, hs, by simpa only [beq_iff_eq] using hsn⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
  have hmem := List.mem_of_find?_eq_some hr
  have hindex : r.index = n := by simpa only [beq_iff_eq] using List.find?_some hr
  have hcheck := List.all_eq_true.mp quarter_upper_rows59_check r hmem
  have h := QuarterUpperWeightRow.sound r hcheck
  rw [quarter_rows59_cut r hmem, hindex] at h
  simpa only [quarterWeight59, hr, Option.getD_some, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Nat.cast_ofNat] using h

set_option maxRecDepth 4096 in
-- Elaboration traverses the finite support endpoint 826 when applying its coverage theorem.
/-- The full principal series is bounded by its finite rational row sum at cutoff 59. -/
theorem quarter_principal_upper59 :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 59 n).re ≤
      ((∑ n ∈ Finset.Ioc 0 826, quarterPsiUpper n (refinedEulerData n) * quarterWeight59 n : ℚ) :
        ℝ) := by
  apply
    quarter_principal_rows_upper (by norm_num only) 826 (by norm_num only [Nat.floor_ofNat])
      refinedEulerData quarterWeight59
  · intro n hn hp
    have he : n ∈ refinedEulerPrefixSet := quarter_rows59_euler n hn hp
    exact refined_euler_prefix_check n he hp
  · intro n hn
    exact quarter_weight59_nonneg n
  · intro n hn hp
    exact quarter_weight59_upper hn hp

set_option maxRecDepth 10000 in
-- Kernel evaluation traverses the finite support and all rational row values.
/-- The exact rational upper-row sum is at most 2.4891. -/
theorem quarter_rows59_sum :
    (∑ n ∈ Finset.Ioc 0 826, quarterPsiUpper n (refinedEulerData n) * quarterWeight59 n : ℚ) ≤
      24891 / 10000 := by
  decide +kernel

/-- At cutoff 59 the full principal series is bounded above by 2.4891. -/
theorem quarter_principal_upper59_explicit :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 59 n).re ≤
      (24891 / 10000 : ℝ) := by
  have h := quarter_principal_upper59
  have hs := (Rat.cast_le (K := ℝ)).mpr quarter_rows59_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at hs
  exact h.trans hs

end PseudoPrime.PrimeTestBounds.MillerRabin
