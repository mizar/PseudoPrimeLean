/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows184Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows184Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows184Block2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows184Block3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows184Block4
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows184Block5
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows184Block6

/-! # Principal and Euler lower bounds at cutoff 184 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The combined lower weight rows at cutoff 184. -/
def quarterFineRows184 : List QuarterFineWeightRow :=
  quarterFineRows184Block0 ++ quarterFineRows184Block1 ++ quarterFineRows184Block2 ++
    quarterFineRows184Block3 ++
    quarterFineRows184Block4 ++
    quarterFineRows184Block5 ++
    quarterFineRows184Block6

/-- All lower weight rows are certified by the independent block checks. -/
theorem quarter_fine_rows184_check : quarterFineRows184.all QuarterFineWeightRow.check = true := by
  simp only [quarterFineRows184, List.all_append, quarter_fine_rows184_block0_check,
    quarter_fine_rows184_block1_check, quarter_fine_rows184_block2_check,
    quarter_fine_rows184_block3_check, quarter_fine_rows184_block4_check,
    quarter_fine_rows184_block5_check, quarter_fine_rows184_block6_check, Bool.and_self]

/-- The certified Euler prefix restricted to the cutoff. -/
def quarterPrefix184 : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 184)

/-- The matching row for a prefix index, with a zero default. -/
def quarterFineRow184 (n : ℕ) : QuarterFineWeightRow :=
  (quarterFineRows184.find? (fun r ↦ r.b == n)).getD ⟨184, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The rational lower principal weight selected at a prefix index. -/
def quarterFineWeight184 (n : ℕ) : ℚ :=
  ((quarterFineRow184 n).weight : ℚ) / 1000000

/-- Every prefix index selects a row with the matching index and cutoff. -/
theorem quarter_fine_rows184_select :
    ∀ n ∈ quarterPrefix184,
      quarterFineRow184 n ∈ quarterFineRows184 ∧
        (quarterFineRow184 n).b = n ∧ (quarterFineRow184 n).cut = 184 := by
  decide +kernel

/-- The principal lower weights are nonnegative. -/
theorem quarter_fine_weight184_nonneg (n : ℕ) : 0 ≤ quarterFineWeight184 n := by
  unfold quarterFineWeight184
  positivity

set_option maxRecDepth 4096 in
-- Elaboration traverses the finite prefix definition.
/-- Every selected lower weight is bounded by the actual principal weight. -/
theorem quarter_fine_weight184_sound {n : ℕ} (hn : n ∈ quarterPrefix184) :
    (quarterFineWeight184 n : ℝ) ≤ refinedScaledWeight 184 n := by
  obtain ⟨hm, hb, hc⟩ := quarter_fine_rows184_select n hn
  have hcheck := List.all_eq_true.mp quarter_fine_rows184_check (quarterFineRow184 n) hm
  have h := (quarterFineRow184 n).sound hcheck
  rw [hc, hb] at h
  simpa only [quarterFineWeight184, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Nat.cast_ofNat] using h

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 4096 in
/-- The rational row sum is a lower bound for the finite principal sum. -/
theorem quarter_principal_lower184 :
    ((∑ n ∈ quarterPrefix184, refinedPsiLower n (refinedEulerData n) * quarterFineWeight184 n : ℚ) :
        ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(184 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 184 n).re := by
  apply target028_principal_rows_lower (by norm_num only) quarterPrefix184 quarterFineWeight184
  · intro n hn
    exact (Finset.mem_filter.mp hn).1
  · intro n hn
    have h := quarter_fine_rows184_select n hn
    have hc := List.all_eq_true.mp quarter_fine_rows184_check _ h.1
    simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  · intro n hn
    exact quarter_fine_weight184_nonneg n
  · intro n hn
    exact quarter_fine_weight184_sound hn

-- Kernel evaluation traverses the certified prime-power rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The selected rational principal row sum is greater than 3.5056. -/
theorem quarter_fine_rows184_sum :
    (2191 / 625 : ℚ) <
      ∑ n ∈ quarterPrefix184, refinedPsiLower n (refinedEulerData n) * quarterFineWeight184 n := by
  decide +kernel

/-- The finite principal sum at cutoff 184 exceeds 3.5056. -/
theorem quarter_principal_lower184_explicit :
    (2191 / 625 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(184 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 184 n).re := by
  have h := (Rat.cast_lt (K := ℝ)).mpr quarter_fine_rows184_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h.le.trans quarter_principal_lower184

-- Kernel evaluation traverses the certified Euler-prefix rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The rational Euler prefix exceeds 2.2114. -/
theorem quarter_euler_rows184_sum :
    (11057 / 5000 : ℚ) < ∑ n ∈ quarterPrefix184, refinedEulerAtomLower n (refinedEulerData n) := by
  decide +kernel

set_option maxRecDepth 4096 in
-- Applying the finite prefix traverses the certified 193-row table.
/-- The Euler prefix through cutoff 184 exceeds 2.2114. -/
theorem quarter_euler_lower184_explicit :
    (11057 / 5000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(184 : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hsum :=
    refined_euler_prefix_sound quarterPrefix184 refinedEulerData
      (fun n hn ↦ refined_euler_prefix_check n (Finset.mem_filter.mp hn).1)
  have hrat := (Rat.cast_lt (K := ℝ)).mpr quarter_euler_rows184_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at hrat
  have hsub : quarterPrefix184 ⊆ Finset.Ioc 0 ⌊(184 : ℝ)⌋₊ := by
    intro n hn
    have h := quarter_fine_rows184_select n hn
    have hc := List.all_eq_true.mp quarter_fine_rows184_check _ h.1
    simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  have hpos :
    ∀ n ∈ Finset.Ioc 0 ⌊(184 : ℝ)⌋₊,
      n ∉ quarterPrefix184 → 0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    intro n hn hnot
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (refined_six_euler_weight_nonneg_all n)
  exact hrat.le.trans (hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hpos))

end PseudoPrime.PrimeTestBounds.MillerRabin
