/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalLower56
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows56Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows56Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows56Block2

/-! # Fine principal lower bound at cutoff 56 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The combined lower weight rows at cutoff 56. -/
def quarterFineRows56 : List QuarterFineWeightRow :=
  quarterFineRows56Block0 ++ quarterFineRows56Block1 ++ quarterFineRows56Block2

/-- All lower weight rows are certified by the independent block checks. -/
theorem quarter_fine_rows56_check : quarterFineRows56.all QuarterFineWeightRow.check = true := by
  simp only [quarterFineRows56, List.all_append, quarter_fine_rows56_block0_check,
    quarter_fine_rows56_block1_check, quarter_fine_rows56_block2_check, Bool.and_self]

/-- The matching row for a prefix index, with a zero default. -/
def quarterFineRow56 (n : ℕ) : QuarterFineWeightRow :=
  (quarterFineRows56.find? (fun r ↦ r.b == n)).getD ⟨56, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The rational lower principal weight selected at a prefix index. -/
def quarterFineWeight56 (n : ℕ) : ℚ :=
  ((quarterFineRow56 n).weight : ℚ) / 1000000

/-- Every prefix index selects a row with the matching index and cutoff. -/
theorem quarter_fine_rows56_select :
    ∀ n ∈ quarterPrefix56,
      quarterFineRow56 n ∈ quarterFineRows56 ∧
        (quarterFineRow56 n).b = n ∧ (quarterFineRow56 n).cut = 56 := by
  decide +kernel

/-- The principal lower weights are nonnegative. -/
theorem quarter_fine_weight56_nonneg (n : ℕ) : 0 ≤ quarterFineWeight56 n := by
  unfold quarterFineWeight56
  positivity

set_option maxRecDepth 4096 in
-- Elaboration traverses the finite prefix definition.
/-- Every selected lower weight is bounded by the actual principal weight. -/
theorem quarter_fine_weight56_sound {n : ℕ} (hn : n ∈ quarterPrefix56) :
    (quarterFineWeight56 n : ℝ) ≤ refinedScaledWeight 56 n := by
  obtain ⟨hm, hb, hc⟩ := quarter_fine_rows56_select n hn
  have hcheck := List.all_eq_true.mp quarter_fine_rows56_check (quarterFineRow56 n) hm
  have h := (quarterFineRow56 n).sound hcheck
  rw [hc, hb] at h
  simpa only [quarterFineWeight56, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Nat.cast_ofNat] using h

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 4096 in
/-- The rational row sum is a lower bound for the finite principal sum. -/
theorem quarter_principal_fine_lower56 :
    ((∑ n ∈ quarterPrefix56, refinedPsiLower n (refinedEulerData n) * quarterFineWeight56 n : ℚ) :
        ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(56 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 56 n).re := by
  apply target028_principal_rows_lower (by norm_num only) quarterPrefix56 quarterFineWeight56
  · intro n hn
    exact (Finset.mem_filter.mp hn).1
  · intro n hn
    have h := quarter_fine_rows56_select n hn
    have hc := List.all_eq_true.mp quarter_fine_rows56_check _ h.1
    simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  · intro n hn
    exact quarter_fine_weight56_nonneg n
  · intro n hn
    exact quarter_fine_weight56_sound hn

-- Kernel evaluation traverses the certified prime-power rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The selected rational principal row sum is greater than 1.7679. -/
theorem quarter_fine_rows56_sum :
    (17679 / 10000 : ℚ) <
      ∑ n ∈ quarterPrefix56, refinedPsiLower n (refinedEulerData n) * quarterFineWeight56 n := by
  decide +kernel

/-- The finite principal sum at cutoff 56 exceeds 1.7679. -/
theorem quarter_principal_fine_lower56_explicit :
    (17679 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(56 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 56 n).re := by
  have h := (Rat.cast_lt (K := ℝ)).mpr quarter_fine_rows56_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h.le.trans quarter_principal_fine_lower56

end PseudoPrime.PrimeTestBounds.MillerRabin
