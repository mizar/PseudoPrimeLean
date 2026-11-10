/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows243Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows243Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows243Block2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows243Block3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows243Block4
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows243Block5
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows243Block6
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineRows243Block7

/-! # Principal and Euler lower bounds at cutoff 243 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The combined lower weight rows at cutoff 243. -/
def quarterFineRows243 : List QuarterFineWeightRow :=
  quarterFineRows243Block0 ++ quarterFineRows243Block1 ++ quarterFineRows243Block2 ++
    quarterFineRows243Block3 ++
    quarterFineRows243Block4 ++
    quarterFineRows243Block5 ++
    quarterFineRows243Block6 ++
    quarterFineRows243Block7

/-- All lower weight rows are certified by the independent block checks. -/
theorem quarter_fine_rows243_check : quarterFineRows243.all QuarterFineWeightRow.check = true := by
  simp only [quarterFineRows243, List.all_append, quarter_fine_rows243_block0_check,
    quarter_fine_rows243_block1_check, quarter_fine_rows243_block2_check,
    quarter_fine_rows243_block3_check, quarter_fine_rows243_block4_check,
    quarter_fine_rows243_block5_check, quarter_fine_rows243_block6_check,
    quarter_fine_rows243_block7_check, Bool.and_self]

/-- The certified Euler prefix restricted to the cutoff. -/
def quarterPrefix243 : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 243)

/-- The matching row for a prefix index, with a zero default. -/
def quarterFineRow243 (n : ℕ) : QuarterFineWeightRow :=
  (quarterFineRows243.find? (fun r ↦ r.b == n)).getD ⟨243, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The rational lower principal weight selected at a prefix index. -/
def quarterFineWeight243 (n : ℕ) : ℚ :=
  ((quarterFineRow243 n).weight : ℚ) / 1000000

/-- Every prefix index selects a row with the matching index and cutoff. -/
theorem quarter_fine_rows243_select :
    ∀ n ∈ quarterPrefix243,
      quarterFineRow243 n ∈ quarterFineRows243 ∧
        (quarterFineRow243 n).b = n ∧ (quarterFineRow243 n).cut = 243 := by
  decide +kernel

/-- The principal lower weights are nonnegative. -/
theorem quarter_fine_weight243_nonneg (n : ℕ) : 0 ≤ quarterFineWeight243 n := by
  unfold quarterFineWeight243
  positivity

set_option maxRecDepth 4096 in
-- Elaboration traverses the finite prefix definition.
/-- Every selected lower weight is bounded by the actual principal weight. -/
theorem quarter_fine_weight243_sound {n : ℕ} (hn : n ∈ quarterPrefix243) :
    (quarterFineWeight243 n : ℝ) ≤ refinedScaledWeight 243 n := by
  obtain ⟨hm, hb, hc⟩ := quarter_fine_rows243_select n hn
  have hcheck := List.all_eq_true.mp quarter_fine_rows243_check (quarterFineRow243 n) hm
  have h := (quarterFineRow243 n).sound hcheck
  rw [hc, hb] at h
  simpa only [quarterFineWeight243, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Nat.cast_ofNat] using h

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 4096 in
/-- The rational row sum is a lower bound for the finite principal sum. -/
theorem quarter_principal_lower243 :
    ((∑ n ∈ quarterPrefix243, refinedPsiLower n (refinedEulerData n) * quarterFineWeight243 n : ℚ) :
        ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(243 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 243 n).re := by
  apply target028_principal_rows_lower (by norm_num only) quarterPrefix243 quarterFineWeight243
  · intro n hn
    exact (Finset.mem_filter.mp hn).1
  · intro n hn
    have h := quarter_fine_rows243_select n hn
    have hc := List.all_eq_true.mp quarter_fine_rows243_check _ h.1
    simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  · intro n hn
    exact quarter_fine_weight243_nonneg n
  · intro n hn
    exact quarter_fine_weight243_sound hn

-- Kernel evaluation traverses the certified prime-power rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The selected rational principal row sum is greater than 4.067. -/
theorem quarter_fine_rows243_sum :
    (4067 / 1000 : ℚ) <
      ∑ n ∈ quarterPrefix243, refinedPsiLower n (refinedEulerData n) * quarterFineWeight243 n := by
  decide +kernel

/-- The finite principal sum at cutoff 243 exceeds 4.067. -/
theorem quarter_principal_lower243_explicit :
    (4067 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(243 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 243 n).re := by
  have h := (Rat.cast_lt (K := ℝ)).mpr quarter_fine_rows243_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h.le.trans quarter_principal_lower243

-- Kernel evaluation traverses the certified Euler-prefix rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The rational Euler prefix exceeds 2.2951. -/
theorem quarter_euler_rows243_sum :
    (22951 / 10000 : ℚ) < ∑ n ∈ quarterPrefix243, refinedEulerAtomLower n (refinedEulerData n) := by
  decide +kernel

set_option maxRecDepth 4096 in
-- Applying the finite prefix traverses the certified 193-row table.
/-- The Euler prefix through cutoff 243 exceeds 2.2951. -/
theorem quarter_euler_lower243_explicit :
    (22951 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(243 : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hsum :=
    refined_euler_prefix_sound quarterPrefix243 refinedEulerData
      (fun n hn ↦ refined_euler_prefix_check n (Finset.mem_filter.mp hn).1)
  have hrat := (Rat.cast_lt (K := ℝ)).mpr quarter_euler_rows243_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at hrat
  have hsub : quarterPrefix243 ⊆ Finset.Ioc 0 ⌊(243 : ℝ)⌋₊ := by
    intro n hn
    have h := quarter_fine_rows243_select n hn
    have hc := List.all_eq_true.mp quarter_fine_rows243_check _ h.1
    simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  have hpos :
    ∀ n ∈ Finset.Ioc 0 ⌊(243 : ℝ)⌋₊,
      n ∉ quarterPrefix243 → 0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    intro n hn hnot
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (refined_six_euler_weight_nonneg_all n)
  exact hrat.le.trans (hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hpos))

end PseudoPrime.PrimeTestBounds.MillerRabin
