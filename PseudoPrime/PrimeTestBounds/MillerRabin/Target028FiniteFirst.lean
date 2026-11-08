/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028WeightRows

/-! # Certified principal prefix at the first finite cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Select the first checked interval endpoint at or above `n`. For indices at
most 252, the last row guarantees that the search succeeds. -/
def target028RowFor (n : ℕ) : Target028WeightRow :=
  (target028WeightRows.find? (fun r ↦ n ≤ r.b)).getD ⟨252, 0, -2, 2, 2838, 15875, 58542634, 5606⟩

/-- The proposed rational lower weight associated with a prime-power index.
The selected endpoint is to its right, so monotonicity transfers the bound. -/
def target028RowWeight (n : ℕ) : ℚ :=
  ((target028RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the filtered 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each index is matched against the 51 checked endpoint rows.
/-- Every retained prime-power index has a checked endpoint at or above it. -/
theorem target028_first_row_selection :
    ∀ n ∈ target028EulerPrefix252,
      1 ≤ n ∧ target028RowFor n ∈ target028WeightRows ∧ n ≤ (target028RowFor n).b := by
  decide +kernel

-- Kernel reduction evaluates the selected rational prime-power contributions.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The sum contains all certified prime-power rows through 252.
/-- The selected rational lower weights give a principal prefix above 79/20. -/
theorem target028_first_rows_rational :
    (79 / 20 : ℚ) <
      ∑ n ∈ target028EulerPrefix252,
        refinedPsiLower n (refinedEulerData n) * target028RowWeight n := by
  decide +kernel

-- The selected prefix is a filtered 193-row finite set.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum at cutoff 252 exceeds 79/20. Each checked
endpoint bounds all selected prime-power rows to its left, and the omitted
summands are nonnegative. -/
theorem target028_first_principal_lower :
    (79 / 20 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(252 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 252 n).re := by
  have hs : target028EulerPrefix252 ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028EulerPrefix252 ⊆ Finset.Ioc 0 ⌊(252 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_first_row_selection n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, target028_euler_prefix252_le hn⟩
  have hw0 : ∀ n ∈ target028EulerPrefix252, 0 ≤ target028RowWeight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028EulerPrefix252, (target028RowWeight n : ℝ) ≤ refinedScaledWeight 252 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb⟩ := target028_first_row_selection n hn
    have hcheck := target028_weight_rows_check (target028RowFor n) hm
    have hrow := (target028RowFor n).sound hcheck
    have hb : (target028RowFor n).b ≤ 252 := by
      have h := hcheck
      simp only [Target028WeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2.2.1
    have hmono :=
      target028_weight252_antitone (n := (n : ℝ)) (b := (target028RowFor n).b)
        (by exact_mod_cast hn1) (by exact_mod_cast hnb) (by exact_mod_cast hb)
    simpa only [target028RowWeight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hmono
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 252) target028EulerPrefix252
      target028RowWeight hs ht hw0 hw
  have hr :
    ((79 / 20 : ℚ) : ℝ) <
      ((∑ n ∈ target028EulerPrefix252,
            refinedPsiLower n (refinedEulerData n) * target028RowWeight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_first_rows_rational
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

end PseudoPrime.PrimeTestBounds.MillerRabin
