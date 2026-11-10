/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows58Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows58Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows58Block2

/-! # Principal and Euler lower bounds at cutoff 58 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The combined lower weight rows at cutoff 58. -/
def quarterFineRows58 : List QuarterFineWeightRow :=
  quarterFineRows58Block0 ++ quarterFineRows58Block1 ++ quarterFineRows58Block2

/-- All lower weight rows are certified by the independent block checks. -/
theorem quarter_fine_rows58_check : quarterFineRows58.all QuarterFineWeightRow.check = true := by
  simp only [quarterFineRows58, List.all_append, quarter_fine_rows58_block0_check,
    quarter_fine_rows58_block1_check, quarter_fine_rows58_block2_check, Bool.and_self]

/-- The certified Euler prefix restricted to the cutoff. -/
def quarterPrefix58 : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 58)

/-- The matching row for a prefix index, with a zero default. -/
def quarterFineRow58 (n : ℕ) : QuarterFineWeightRow :=
  (quarterFineRows58.find? (fun r ↦ r.b == n)).getD ⟨58, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The rational lower principal weight selected at a prefix index. -/
def quarterFineWeight58 (n : ℕ) : ℚ :=
  ((quarterFineRow58 n).weight : ℚ) / 1000000

/-- Every prefix index selects a row with the matching index and cutoff. -/
theorem quarter_fine_rows58_select :
    ∀ n ∈ quarterPrefix58,
      quarterFineRow58 n ∈ quarterFineRows58 ∧
        (quarterFineRow58 n).b = n ∧ (quarterFineRow58 n).cut = 58 := by
  decide +kernel

/-- The principal lower weights are nonnegative. -/
theorem quarter_fine_weight58_nonneg (n : ℕ) : 0 ≤ quarterFineWeight58 n := by
  unfold quarterFineWeight58
  positivity

set_option maxRecDepth 4096 in
-- Elaboration traverses the finite prefix definition.
/-- Every selected lower weight is bounded by the actual principal weight. -/
theorem quarter_fine_weight58_sound {n : ℕ} (hn : n ∈ quarterPrefix58) :
    (quarterFineWeight58 n : ℝ) ≤ refinedScaledWeight 58 n := by
  obtain ⟨hm, hb, hc⟩ := quarter_fine_rows58_select n hn
  have hcheck := List.all_eq_true.mp quarter_fine_rows58_check (quarterFineRow58 n) hm
  have h := (quarterFineRow58 n).sound hcheck
  rw [hc, hb] at h
  simpa only [quarterFineWeight58, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Nat.cast_ofNat] using h

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 4096 in
/-- The rational row sum is a lower bound for the finite principal sum. -/
theorem quarter_principal_lower58 :
    ((∑ n ∈ quarterPrefix58, refinedPsiLower n (refinedEulerData n) * quarterFineWeight58 n : ℚ) :
        ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(58 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 58 n).re := by
  apply target028_principal_rows_lower (by norm_num only) quarterPrefix58 quarterFineWeight58
  · intro n hn
    exact (Finset.mem_filter.mp hn).1
  · intro n hn
    have h := quarter_fine_rows58_select n hn
    have hc := List.all_eq_true.mp quarter_fine_rows58_check _ h.1
    simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  · intro n hn
    exact quarter_fine_weight58_nonneg n
  · intro n hn
    exact quarter_fine_weight58_sound hn

-- Kernel evaluation traverses the certified prime-power rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The selected rational principal row sum is greater than 1.7818. -/
theorem quarter_fine_rows58_sum :
    (17818 / 10000 : ℚ) <
      ∑ n ∈ quarterPrefix58, refinedPsiLower n (refinedEulerData n) * quarterFineWeight58 n := by
  decide +kernel

/-- The finite principal sum at cutoff 58 exceeds 1.7818. -/
theorem quarter_principal_lower58_explicit :
    (17818 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(58 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 58 n).re := by
  have h := (Rat.cast_lt (K := ℝ)).mpr quarter_fine_rows58_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h.le.trans quarter_principal_lower58

-- Kernel evaluation traverses the certified Euler-prefix rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The rational Euler prefix exceeds 1.7645. -/
theorem quarter_euler_rows58_sum :
    (3529 / 2000 : ℚ) < ∑ n ∈ quarterPrefix58, refinedEulerAtomLower n (refinedEulerData n) := by
  decide +kernel

set_option maxRecDepth 4096 in
-- Applying the finite prefix traverses the certified 193-row table.
/-- The Euler prefix through cutoff 58 exceeds 1.7645. -/
theorem quarter_euler_lower58_explicit :
    (3529 / 2000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(58 : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hsum :=
    refined_euler_prefix_sound quarterPrefix58 refinedEulerData
      (fun n hn ↦ refined_euler_prefix_check n (Finset.mem_filter.mp hn).1)
  have hrat := (Rat.cast_lt (K := ℝ)).mpr quarter_euler_rows58_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at hrat
  have hsub : quarterPrefix58 ⊆ Finset.Ioc 0 ⌊(58 : ℝ)⌋₊ := by
    intro n hn
    have h := quarter_fine_rows58_select n hn
    have hc := List.all_eq_true.mp quarter_fine_rows58_check _ h.1
    simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  have hpos :
    ∀ n ∈ Finset.Ioc 0 ⌊(58 : ℝ)⌋₊,
      n ∉ quarterPrefix58 → 0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    intro n hn hnot
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (refined_six_euler_weight_nonneg_all n)
  exact hrat.le.trans (hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hpos))

end PseudoPrime.PrimeTestBounds.MillerRabin
