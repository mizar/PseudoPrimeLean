/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows141Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows141Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows141Block2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows141Block3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows141Block4
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows141Block5

/-! # Principal and Euler lower bounds at cutoff 141 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The combined lower weight rows at cutoff 141. -/
def quarterFineRows141 : List QuarterFineWeightRow :=
  quarterFineRows141Block0 ++ quarterFineRows141Block1 ++ quarterFineRows141Block2 ++
    quarterFineRows141Block3 ++
    quarterFineRows141Block4 ++
    quarterFineRows141Block5

/-- All lower weight rows are certified by the independent block checks. -/
theorem quarter_fine_rows141_check : quarterFineRows141.all QuarterFineWeightRow.check = true := by
  simp only [quarterFineRows141, List.all_append, quarter_fine_rows141_block0_check,
    quarter_fine_rows141_block1_check, quarter_fine_rows141_block2_check,
    quarter_fine_rows141_block3_check, quarter_fine_rows141_block4_check,
    quarter_fine_rows141_block5_check, Bool.and_self]

/-- The certified Euler prefix restricted to the cutoff. -/
def quarterPrefix141 : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 141)

/-- The matching row for a prefix index, with a zero default. -/
def quarterFineRow141 (n : ℕ) : QuarterFineWeightRow :=
  (quarterFineRows141.find? (fun r ↦ r.b == n)).getD ⟨141, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The rational lower principal weight selected at a prefix index. -/
def quarterFineWeight141 (n : ℕ) : ℚ :=
  ((quarterFineRow141 n).weight : ℚ) / 1000000

/-- Every prefix index selects a row with the matching index and cutoff. -/
theorem quarter_fine_rows141_select :
    ∀ n ∈ quarterPrefix141,
      quarterFineRow141 n ∈ quarterFineRows141 ∧
        (quarterFineRow141 n).b = n ∧ (quarterFineRow141 n).cut = 141 := by
  decide +kernel

/-- The principal lower weights are nonnegative. -/
theorem quarter_fine_weight141_nonneg (n : ℕ) : 0 ≤ quarterFineWeight141 n := by
  unfold quarterFineWeight141
  positivity

set_option maxRecDepth 4096 in
-- Elaboration traverses the finite prefix definition.
/-- Every selected lower weight is bounded by the actual principal weight. -/
theorem quarter_fine_weight141_sound {n : ℕ} (hn : n ∈ quarterPrefix141) :
    (quarterFineWeight141 n : ℝ) ≤ refinedScaledWeight 141 n := by
  obtain ⟨hm, hb, hc⟩ := quarter_fine_rows141_select n hn
  have hcheck := List.all_eq_true.mp quarter_fine_rows141_check (quarterFineRow141 n) hm
  have h := (quarterFineRow141 n).sound hcheck
  rw [hc, hb] at h
  simpa only [quarterFineWeight141, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Nat.cast_ofNat] using h

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 4096 in
/-- The rational row sum is a lower bound for the finite principal sum. -/
theorem quarter_principal_lower141 :
    ((∑ n ∈ quarterPrefix141, refinedPsiLower n (refinedEulerData n) * quarterFineWeight141 n : ℚ) :
        ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(141 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 141 n).re := by
  apply target028_principal_rows_lower (by norm_num only) quarterPrefix141 quarterFineWeight141
  · intro n hn
    exact (Finset.mem_filter.mp hn).1
  · intro n hn
    have h := quarter_fine_rows141_select n hn
    have hc := List.all_eq_true.mp quarter_fine_rows141_check _ h.1
    simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  · intro n hn
    exact quarter_fine_weight141_nonneg n
  · intro n hn
    exact quarter_fine_weight141_sound hn

-- Kernel evaluation traverses the certified prime-power rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The selected rational principal row sum is greater than 3.0371. -/
theorem quarter_fine_rows141_sum :
    (30371 / 10000 : ℚ) <
      ∑ n ∈ quarterPrefix141, refinedPsiLower n (refinedEulerData n) * quarterFineWeight141 n := by
  decide +kernel

/-- The finite principal sum at cutoff 141 exceeds 3.0371. -/
theorem quarter_principal_lower141_explicit :
    (30371 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(141 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 141 n).re := by
  have h := (Rat.cast_lt (K := ℝ)).mpr quarter_fine_rows141_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h.le.trans quarter_principal_lower141

-- Kernel evaluation traverses the certified Euler-prefix rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The rational Euler prefix exceeds 2.1261. -/
theorem quarter_euler_rows141_sum :
    (21261 / 10000 : ℚ) < ∑ n ∈ quarterPrefix141, refinedEulerAtomLower n (refinedEulerData n) := by
  decide +kernel

set_option maxRecDepth 4096 in
-- Applying the finite prefix traverses the certified 193-row table.
/-- The Euler prefix through cutoff 141 exceeds 2.1261. -/
theorem quarter_euler_lower141_explicit :
    (21261 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(141 : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hsum :=
    refined_euler_prefix_sound quarterPrefix141 refinedEulerData
      (fun n hn ↦ refined_euler_prefix_check n (Finset.mem_filter.mp hn).1)
  have hrat := (Rat.cast_lt (K := ℝ)).mpr quarter_euler_rows141_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at hrat
  have hsub : quarterPrefix141 ⊆ Finset.Ioc 0 ⌊(141 : ℝ)⌋₊ := by
    intro n hn
    have h := quarter_fine_rows141_select n hn
    have hc := List.all_eq_true.mp quarter_fine_rows141_check _ h.1
    simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  have hpos :
    ∀ n ∈ Finset.Ioc 0 ⌊(141 : ℝ)⌋₊,
      n ∉ quarterPrefix141 → 0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    intro n hn hnot
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (refined_six_euler_weight_nonneg_all n)
  exact hrat.le.trans (hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hpos))

end PseudoPrime.PrimeTestBounds.MillerRabin
