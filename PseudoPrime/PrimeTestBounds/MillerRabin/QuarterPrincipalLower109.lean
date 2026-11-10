/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows109Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows109Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows109Block2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows109Block3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows109Block4

/-! # Principal and Euler lower bounds at cutoff 109 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The combined lower weight rows at cutoff 109. -/
def quarterFineRows109 : List QuarterFineWeightRow :=
  quarterFineRows109Block0 ++ quarterFineRows109Block1 ++ quarterFineRows109Block2 ++
    quarterFineRows109Block3 ++
    quarterFineRows109Block4

/-- All lower weight rows are certified by the independent block checks. -/
theorem quarter_fine_rows109_check : quarterFineRows109.all QuarterFineWeightRow.check = true := by
  simp only [quarterFineRows109, List.all_append, quarter_fine_rows109_block0_check,
    quarter_fine_rows109_block1_check, quarter_fine_rows109_block2_check,
    quarter_fine_rows109_block3_check, quarter_fine_rows109_block4_check, Bool.and_self]

/-- The certified Euler prefix restricted to the cutoff. -/
def quarterPrefix109 : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 109)

/-- The matching row for a prefix index, with a zero default. -/
def quarterFineRow109 (n : ℕ) : QuarterFineWeightRow :=
  (quarterFineRows109.find? (fun r ↦ r.b == n)).getD ⟨109, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The rational lower principal weight selected at a prefix index. -/
def quarterFineWeight109 (n : ℕ) : ℚ :=
  ((quarterFineRow109 n).weight : ℚ) / 1000000

/-- Every prefix index selects a row with the matching index and cutoff. -/
theorem quarter_fine_rows109_select :
    ∀ n ∈ quarterPrefix109,
      quarterFineRow109 n ∈ quarterFineRows109 ∧
        (quarterFineRow109 n).b = n ∧ (quarterFineRow109 n).cut = 109 := by
  decide +kernel

/-- The principal lower weights are nonnegative. -/
theorem quarter_fine_weight109_nonneg (n : ℕ) : 0 ≤ quarterFineWeight109 n := by
  unfold quarterFineWeight109
  positivity

set_option maxRecDepth 4096 in
-- Elaboration traverses the finite prefix definition.
/-- Every selected lower weight is bounded by the actual principal weight. -/
theorem quarter_fine_weight109_sound {n : ℕ} (hn : n ∈ quarterPrefix109) :
    (quarterFineWeight109 n : ℝ) ≤ refinedScaledWeight 109 n := by
  obtain ⟨hm, hb, hc⟩ := quarter_fine_rows109_select n hn
  have hcheck := List.all_eq_true.mp quarter_fine_rows109_check (quarterFineRow109 n) hm
  have h := (quarterFineRow109 n).sound hcheck
  rw [hc, hb] at h
  simpa only [quarterFineWeight109, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Nat.cast_ofNat] using h

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 4096 in
/-- The rational row sum is a lower bound for the finite principal sum. -/
theorem quarter_principal_lower109 :
    ((∑ n ∈ quarterPrefix109, refinedPsiLower n (refinedEulerData n) * quarterFineWeight109 n : ℚ) :
        ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(109 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 109 n).re := by
  apply target028_principal_rows_lower (by norm_num only) quarterPrefix109 quarterFineWeight109
  · intro n hn
    exact (Finset.mem_filter.mp hn).1
  · intro n hn
    have h := quarter_fine_rows109_select n hn
    have hc := List.all_eq_true.mp quarter_fine_rows109_check _ h.1
    simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  · intro n hn
    exact quarter_fine_weight109_nonneg n
  · intro n hn
    exact quarter_fine_weight109_sound hn

-- Kernel evaluation traverses the certified prime-power rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The selected rational principal row sum is greater than 2.6617. -/
theorem quarter_fine_rows109_sum :
    (26617 / 10000 : ℚ) <
      ∑ n ∈ quarterPrefix109, refinedPsiLower n (refinedEulerData n) * quarterFineWeight109 n := by
  decide +kernel

/-- The finite principal sum at cutoff 109 exceeds 2.6617. -/
theorem quarter_principal_lower109_explicit :
    (26617 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(109 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 109 n).re := by
  have h := (Rat.cast_lt (K := ℝ)).mpr quarter_fine_rows109_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h.le.trans quarter_principal_lower109

-- Kernel evaluation traverses the certified Euler-prefix rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The rational Euler prefix exceeds 2.0476. -/
theorem quarter_euler_rows109_sum :
    (5119 / 2500 : ℚ) < ∑ n ∈ quarterPrefix109, refinedEulerAtomLower n (refinedEulerData n) := by
  decide +kernel

set_option maxRecDepth 4096 in
-- Applying the finite prefix traverses the certified 193-row table.
/-- The Euler prefix through cutoff 109 exceeds 2.0476. -/
theorem quarter_euler_lower109_explicit :
    (5119 / 2500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(109 : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hsum :=
    refined_euler_prefix_sound quarterPrefix109 refinedEulerData
      (fun n hn ↦ refined_euler_prefix_check n (Finset.mem_filter.mp hn).1)
  have hrat := (Rat.cast_lt (K := ℝ)).mpr quarter_euler_rows109_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at hrat
  have hsub : quarterPrefix109 ⊆ Finset.Ioc 0 ⌊(109 : ℝ)⌋₊ := by
    intro n hn
    have h := quarter_fine_rows109_select n hn
    have hc := List.all_eq_true.mp quarter_fine_rows109_check _ h.1
    simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  have hpos :
    ∀ n ∈ Finset.Ioc 0 ⌊(109 : ℝ)⌋₊,
      n ∉ quarterPrefix109 → 0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    intro n hn hnot
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (refined_six_euler_weight_nonneg_all n)
  exact hrat.le.trans (hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hpos))

end PseudoPrime.PrimeTestBounds.MillerRabin
