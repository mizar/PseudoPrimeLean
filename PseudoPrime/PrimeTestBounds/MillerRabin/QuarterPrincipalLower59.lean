/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows59Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows59Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows59Block2

/-! # Principal and Euler lower bounds at cutoff 59 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The combined lower weight rows at cutoff 59. -/
def quarterFineRows59 : List QuarterFineWeightRow :=
  quarterFineRows59Block0 ++ quarterFineRows59Block1 ++ quarterFineRows59Block2

/-- All lower weight rows are certified by the independent block checks. -/
theorem quarter_fine_rows59_check : quarterFineRows59.all QuarterFineWeightRow.check = true := by
  simp only [quarterFineRows59, List.all_append, quarter_fine_rows59_block0_check,
    quarter_fine_rows59_block1_check, quarter_fine_rows59_block2_check, Bool.and_self]

/-- The certified Euler prefix restricted to the cutoff. -/
def quarterPrefix59 : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 59)

/-- The matching row for a prefix index, with a zero default. -/
def quarterFineRow59 (n : ℕ) : QuarterFineWeightRow :=
  (quarterFineRows59.find? (fun r ↦ r.b == n)).getD ⟨59, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The rational lower principal weight selected at a prefix index. -/
def quarterFineWeight59 (n : ℕ) : ℚ :=
  ((quarterFineRow59 n).weight : ℚ) / 1000000

/-- Every prefix index selects a row with the matching index and cutoff. -/
theorem quarter_fine_rows59_select :
    ∀ n ∈ quarterPrefix59,
      quarterFineRow59 n ∈ quarterFineRows59 ∧
        (quarterFineRow59 n).b = n ∧ (quarterFineRow59 n).cut = 59 := by
  decide +kernel

/-- The principal lower weights are nonnegative. -/
theorem quarter_fine_weight59_nonneg (n : ℕ) : 0 ≤ quarterFineWeight59 n := by
  unfold quarterFineWeight59
  positivity

set_option maxRecDepth 4096 in
-- Elaboration traverses the finite prefix definition.
/-- Every selected lower weight is bounded by the actual principal weight. -/
theorem quarter_fine_weight59_sound {n : ℕ} (hn : n ∈ quarterPrefix59) :
    (quarterFineWeight59 n : ℝ) ≤ refinedScaledWeight 59 n := by
  obtain ⟨hm, hb, hc⟩ := quarter_fine_rows59_select n hn
  have hcheck := List.all_eq_true.mp quarter_fine_rows59_check (quarterFineRow59 n) hm
  have h := (quarterFineRow59 n).sound hcheck
  rw [hc, hb] at h
  simpa only [quarterFineWeight59, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Nat.cast_ofNat] using h

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 4096 in
/-- The rational row sum is a lower bound for the finite principal sum. -/
theorem quarter_principal_lower59 :
    ((∑ n ∈ quarterPrefix59, refinedPsiLower n (refinedEulerData n) * quarterFineWeight59 n : ℚ) :
        ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(59 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 59 n).re := by
  apply target028_principal_rows_lower (by norm_num only) quarterPrefix59 quarterFineWeight59
  · intro n hn
    exact (Finset.mem_filter.mp hn).1
  · intro n hn
    have h := quarter_fine_rows59_select n hn
    have hc := List.all_eq_true.mp quarter_fine_rows59_check _ h.1
    simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  · intro n hn
    exact quarter_fine_weight59_nonneg n
  · intro n hn
    exact quarter_fine_weight59_sound hn

-- Kernel evaluation traverses the certified prime-power rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The selected rational principal row sum is greater than 1.8359. -/
theorem quarter_fine_rows59_sum :
    (18359 / 10000 : ℚ) <
      ∑ n ∈ quarterPrefix59, refinedPsiLower n (refinedEulerData n) * quarterFineWeight59 n := by
  decide +kernel

/-- The finite principal sum at cutoff 59 exceeds 1.8359. -/
theorem quarter_principal_lower59_explicit :
    (18359 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(59 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 59 n).re := by
  have h := (Rat.cast_lt (K := ℝ)).mpr quarter_fine_rows59_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h.le.trans quarter_principal_lower59

-- Kernel evaluation traverses the certified Euler-prefix rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The rational Euler prefix exceeds 1.7934. -/
theorem quarter_euler_rows59_sum :
    (8967 / 5000 : ℚ) < ∑ n ∈ quarterPrefix59, refinedEulerAtomLower n (refinedEulerData n) := by
  decide +kernel

set_option maxRecDepth 4096 in
-- Applying the finite prefix traverses the certified 193-row table.
/-- The Euler prefix through cutoff 59 exceeds 1.7934. -/
theorem quarter_euler_lower59_explicit :
    (8967 / 5000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(59 : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hsum :=
    refined_euler_prefix_sound quarterPrefix59 refinedEulerData
      (fun n hn ↦ refined_euler_prefix_check n (Finset.mem_filter.mp hn).1)
  have hrat := (Rat.cast_lt (K := ℝ)).mpr quarter_euler_rows59_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at hrat
  have hsub : quarterPrefix59 ⊆ Finset.Ioc 0 ⌊(59 : ℝ)⌋₊ := by
    intro n hn
    have h := quarter_fine_rows59_select n hn
    have hc := List.all_eq_true.mp quarter_fine_rows59_check _ h.1
    simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  have hpos :
    ∀ n ∈ Finset.Ioc 0 ⌊(59 : ℝ)⌋₊,
      n ∉ quarterPrefix59 → 0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    intro n hn hnot
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (refined_six_euler_weight_nonneg_all n)
  exact hrat.le.trans (hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hpos))

end PseudoPrime.PrimeTestBounds.MillerRabin
