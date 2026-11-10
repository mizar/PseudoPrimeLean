/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterLowerRows56Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterLowerRows56Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterLowerRows56Block2

/-! # Principal and Euler lower bounds at cutoff 56 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The combined lower weight rows at cutoff 56. -/
def quarterLowerRows56 : List Target028GeneralWeightRow :=
  quarterLowerRows56Block0 ++ quarterLowerRows56Block1 ++ quarterLowerRows56Block2

/-- All lower weight rows are certified by the independent block checks. -/
theorem quarter_lower_rows56_check :
    quarterLowerRows56.all Target028GeneralWeightRow.check = true := by
  simp only [quarterLowerRows56, List.all_append, quarter_lower_rows56_block0_check,
    quarter_lower_rows56_block1_check, quarter_lower_rows56_block2_check, Bool.and_self]

/-- The certified Euler prefix restricted to the cutoff. -/
def quarterPrefix56 : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 56)

/-- The matching row for a prefix index, with a zero default. -/
def quarterLowerRow56 (n : ℕ) : Target028GeneralWeightRow :=
  (quarterLowerRows56.find? (fun r ↦ r.b == n)).getD ⟨56, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The rational lower principal weight selected at a prefix index. -/
def quarterLowerWeight56 (n : ℕ) : ℚ :=
  ((quarterLowerRow56 n).weight : ℚ) / 1000000

/-- Every prefix index selects a row with the matching index and cutoff. -/
theorem quarter_lower_rows56_select :
    ∀ n ∈ quarterPrefix56,
      quarterLowerRow56 n ∈ quarterLowerRows56 ∧
        (quarterLowerRow56 n).b = n ∧ (quarterLowerRow56 n).cut = 56 := by
  decide +kernel

/-- The principal lower weights are nonnegative. -/
theorem quarter_lower_weight56_nonneg (n : ℕ) : 0 ≤ quarterLowerWeight56 n := by
  unfold quarterLowerWeight56
  positivity

set_option maxRecDepth 4096 in
-- Elaboration traverses the finite prefix definition.
/-- Every selected lower weight is bounded by the actual principal weight. -/
theorem quarter_lower_weight56_sound {n : ℕ} (hn : n ∈ quarterPrefix56) :
    (quarterLowerWeight56 n : ℝ) ≤ refinedScaledWeight 56 n := by
  obtain ⟨hm, hb, hc⟩ := quarter_lower_rows56_select n hn
  have hcheck := List.all_eq_true.mp quarter_lower_rows56_check (quarterLowerRow56 n) hm
  have h := (quarterLowerRow56 n).sound hcheck
  rw [hc, hb] at h
  simpa only [quarterLowerWeight56, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Nat.cast_ofNat] using h

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 4096 in
/-- The rational row sum is a lower bound for the finite principal sum. -/
theorem quarter_principal_lower56 :
    ((∑ n ∈ quarterPrefix56, refinedPsiLower n (refinedEulerData n) * quarterLowerWeight56 n : ℚ) :
        ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(56 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 56 n).re := by
  apply target028_principal_rows_lower (by norm_num only) quarterPrefix56 quarterLowerWeight56
  · intro n hn
    exact (Finset.mem_filter.mp hn).1
  · intro n hn
    have h := quarter_lower_rows56_select n hn
    have hc := List.all_eq_true.mp quarter_lower_rows56_check _ h.1
    simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  · intro n hn
    exact quarter_lower_weight56_nonneg n
  · intro n hn
    exact quarter_lower_weight56_sound hn

-- Kernel evaluation traverses the certified prime-power rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The selected rational principal row sum is greater than 1.761. -/
theorem quarter_lower_rows56_sum :
    (1761 / 1000 : ℚ) <
      ∑ n ∈ quarterPrefix56, refinedPsiLower n (refinedEulerData n) * quarterLowerWeight56 n := by
  decide +kernel

/-- The finite principal sum at cutoff 56 exceeds 1.761. -/
theorem quarter_principal_lower56_explicit :
    (1761 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(56 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 56 n).re := by
  have h := (Rat.cast_lt (K := ℝ)).mpr quarter_lower_rows56_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h.le.trans quarter_principal_lower56

-- Kernel evaluation traverses the certified Euler-prefix rows and their rational values.
set_option maxRecDepth 4096 in
-- Exact rational reduction checks the finite row sum.
/-- The rational Euler prefix exceeds 1.7645. -/
theorem quarter_euler_rows56_sum :
    (3529 / 2000 : ℚ) < ∑ n ∈ quarterPrefix56, refinedEulerAtomLower n (refinedEulerData n) := by
  decide +kernel

set_option maxRecDepth 4096 in
-- Applying the finite prefix traverses the certified 193-row table.
/-- The Euler prefix through cutoff 56 exceeds 1.7645. -/
theorem quarter_euler_lower56_explicit :
    (3529 / 2000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(56 : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hsum :=
    refined_euler_prefix_sound quarterPrefix56 refinedEulerData
      (fun n hn ↦ refined_euler_prefix_check n (Finset.mem_filter.mp hn).1)
  have hrat := (Rat.cast_lt (K := ℝ)).mpr quarter_euler_rows56_sum
  simp only [Rat.cast_div, Rat.cast_ofNat] at hrat
  have hsub : quarterPrefix56 ⊆ Finset.Ioc 0 ⌊(56 : ℝ)⌋₊ := by
    intro n hn
    have h := quarter_lower_rows56_select n hn
    have hc := List.all_eq_true.mp quarter_lower_rows56_check _ h.1
    simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨by simpa only [h.2.1] using hc.2.1, (Finset.mem_filter.mp hn).2⟩
  have hpos :
    ∀ n ∈ Finset.Ioc 0 ⌊(56 : ℝ)⌋₊,
      n ∉ quarterPrefix56 → 0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    intro n hn hnot
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (refined_six_euler_weight_nonneg_all n)
  exact hrat.le.trans (hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hpos))

end PseudoPrime.PrimeTestBounds.MillerRabin
