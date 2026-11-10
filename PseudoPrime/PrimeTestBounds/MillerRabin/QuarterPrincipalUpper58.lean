/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows58
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalUpperRows

/-! # Principal upper bound at cutoff 58 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The certified upper weight at index `n`, with zero for an unlisted index. -/
def quarterWeight58 (n : ℕ) : ℚ :=
  (((quarterUpperRows58.find? (fun r ↦ r.index == n)).getD ⟨58, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩).weight :
      ℚ) /
    1000000

/-- Every prime power through the support endpoint occurs in the upper row table. -/
theorem quarter_rows58_cover :
    ∀ n ∈ Finset.Ioc 0 812, IsPrimePow n → ∃ r ∈ quarterUpperRows58, r.index = n := by
  decide +kernel

/-- Every row in the table has the common cutoff 58. -/
theorem quarter_rows58_cut : ∀ r ∈ quarterUpperRows58, r.cut = 58 := by decide +kernel

/-- Every prime power through the support endpoint has a checked logarithm row. -/
theorem quarter_rows58_euler :
    ∀ n ∈ Finset.Ioc 0 812, IsPrimePow n → n ∈ refinedEulerPrefixSet := by decide +kernel

/-- The selected rational upper weight is nonnegative at every index. -/
theorem quarter_weight58_nonneg (n : ℕ) : 0 ≤ quarterWeight58 n := by
  unfold quarterWeight58
  positivity

/-- The selected row bounds the principal weight at each supported prime power. -/
theorem quarter_weight58_upper {n : ℕ} (hn : n ∈ Finset.Ioc 0 812) (hp : IsPrimePow n) :
    refinedScaledWeight 58 n ≤ (quarterWeight58 n : ℝ) := by
  obtain ⟨s, hs, hsn⟩ := quarter_rows58_cover n hn hp
  have hsome : (quarterUpperRows58.find? (fun r ↦ r.index == n)).isSome = true :=
    List.find?_isSome.mpr ⟨s, hs, by simpa only [beq_iff_eq] using hsn⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
  have hmem := List.mem_of_find?_eq_some hr
  have hindex : r.index = n := by simpa only [beq_iff_eq] using List.find?_some hr
  have hcheck := List.all_eq_true.mp quarter_upper_rows58_check r hmem
  have h := QuarterUpperWeightRow.sound r hcheck
  rw [quarter_rows58_cut r hmem, hindex] at h
  simpa only [quarterWeight58, hr, Option.getD_some, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Nat.cast_ofNat] using h

set_option maxRecDepth 4096 in
-- Elaboration traverses the finite support endpoint 812 when applying its coverage theorem.
/-- The full principal series is bounded by its finite rational row sum at cutoff 58. -/
theorem quarter_principal_upper58 :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 58 n).re ≤
      ((∑ n ∈ Finset.Ioc 0 812, quarterPsiUpper n (refinedEulerData n) * quarterWeight58 n : ℚ) :
        ℝ) := by
  apply
    quarter_principal_rows_upper (by norm_num only) 812 (by norm_num only [Nat.floor_ofNat])
      refinedEulerData quarterWeight58
  · intro n hn hp
    have he : n ∈ refinedEulerPrefixSet := quarter_rows58_euler n hn hp
    exact refined_euler_prefix_check n he hp
  · intro n hn
    exact quarter_weight58_nonneg n
  · intro n hn hp
    exact quarter_weight58_upper hn hp

set_option maxRecDepth 10000 in
-- Kernel evaluation traverses the finite support and all rational row values.
/-- The exact rational upper-row sum is at most 2.465. -/
theorem quarter_rows58_sum :
    (∑ n ∈ Finset.Ioc 0 812, quarterPsiUpper n (refinedEulerData n) * quarterWeight58 n : ℚ) ≤
      2465 / 1000 := by
  decide +kernel

/-- At cutoff 58 the full principal series is bounded above by 2.465. -/
theorem quarter_principal_upper58_explicit :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 58 n).re ≤
      (2465 / 1000 : ℝ) := by
  have h := quarter_principal_upper58
  have hs := (Rat.cast_le (K := ℝ)).mpr quarter_rows58_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at hs
  exact h.trans hs

end PseudoPrime.PrimeTestBounds.MillerRabin
