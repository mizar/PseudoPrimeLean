/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUpperRows56
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalUpperRows

/-! # Principal upper bound at cutoff 56 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The certified upper weight at index `n`, with zero for an unlisted index. -/
def quarterWeight56 (n : ℕ) : ℚ :=
  (((quarterUpperRows56.find? (fun r ↦ r.index == n)).getD ⟨56, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩).weight :
      ℚ) /
    1000000

/-- Every prime power through the support endpoint occurs in the upper row table. -/
theorem quarter_rows56_cover :
    ∀ n ∈ Finset.Ioc 0 784, IsPrimePow n → ∃ r ∈ quarterUpperRows56, r.index = n := by
  decide +kernel

/-- Every row in the table has the common cutoff 56. -/
theorem quarter_rows56_cut : ∀ r ∈ quarterUpperRows56, r.cut = 56 := by decide +kernel

/-- Every prime power through the support endpoint has a checked logarithm row. -/
theorem quarter_rows56_euler :
    ∀ n ∈ Finset.Ioc 0 784, IsPrimePow n → n ∈ refinedEulerPrefixSet := by decide +kernel

/-- The selected rational upper weight is nonnegative at every index. -/
theorem quarter_weight56_nonneg (n : ℕ) : 0 ≤ quarterWeight56 n := by
  unfold quarterWeight56
  positivity

/-- The selected row bounds the principal weight at each supported prime power. -/
theorem quarter_weight56_upper {n : ℕ} (hn : n ∈ Finset.Ioc 0 784) (hp : IsPrimePow n) :
    refinedScaledWeight 56 n ≤ (quarterWeight56 n : ℝ) := by
  obtain ⟨s, hs, hsn⟩ := quarter_rows56_cover n hn hp
  have hsome : (quarterUpperRows56.find? (fun r ↦ r.index == n)).isSome = true :=
    List.find?_isSome.mpr ⟨s, hs, by simpa only [beq_iff_eq] using hsn⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
  have hmem := List.mem_of_find?_eq_some hr
  have hindex : r.index = n := by simpa only [beq_iff_eq] using List.find?_some hr
  have hcheck := List.all_eq_true.mp quarter_upper_rows56_check r hmem
  have h := QuarterUpperWeightRow.sound r hcheck
  rw [quarter_rows56_cut r hmem, hindex] at h
  simpa only [quarterWeight56, hr, Option.getD_some, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Nat.cast_ofNat] using h

set_option maxRecDepth 4096 in
-- Elaboration traverses the finite support endpoint 784 when applying its coverage theorem.
/-- The full principal series is bounded by its finite rational row sum at cutoff 56. -/
theorem quarter_principal_upper56 :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 56 n).re ≤
      ((∑ n ∈ Finset.Ioc 0 784, quarterPsiUpper n (refinedEulerData n) * quarterWeight56 n : ℚ) :
        ℝ) := by
  apply
    quarter_principal_rows_upper (by norm_num only) 784 (by norm_num only [Nat.floor_ofNat])
      refinedEulerData quarterWeight56
  · intro n hn hp
    have he : n ∈ refinedEulerPrefixSet := quarter_rows56_euler n hn hp
    exact refined_euler_prefix_check n he hp
  · intro n hn
    exact quarter_weight56_nonneg n
  · intro n hn hp
    exact quarter_weight56_upper hn hp

set_option maxRecDepth 10000 in
-- Kernel evaluation traverses the finite support and all rational row values.
/-- The exact rational upper-row sum is at most 2.415. -/
theorem quarter_rows56_sum :
    (∑ n ∈ Finset.Ioc 0 784, quarterPsiUpper n (refinedEulerData n) * quarterWeight56 n : ℚ) ≤
      2415 / 1000 := by
  decide +kernel

/-- At cutoff 56 the full principal series is bounded above by 2.415. -/
theorem quarter_principal_upper56_explicit :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 56 n).re ≤
      (2415 / 1000 : ℝ) := by
  have h := quarter_principal_upper56
  have hs := (Rat.cast_le (K := ℝ)).mpr quarter_rows56_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at hs
  exact h.trans hs

end PseudoPrime.PrimeTestBounds.MillerRabin
