/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSignedSupportBudget
public import PseudoPrime.Analysis.GammaSignedRampCellBounds

/-! # Uniform signed dual budgets on closed scale cells -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: two ordered real scales. Claim: the smaller signed prime support is nested.
Proof: monotonicity of sqrt and natural floor. Role: use one support throughout a scale cell. -/
theorem gamma_signed_support_mono {x y : ℝ} (hxy : x ≤ y) :
    gammaSignedSupportPrimeSet x ⊆ gammaSignedSupportPrimeSet y := by
  intro p hp
  obtain ⟨hi, hp⟩ := Finset.mem_filter.mp hp
  obtain ⟨h3, hb⟩ := Finset.mem_Icc.mp hi
  have hc : 1 + 6 * Real.sqrt x ≤ 1 + 6 * Real.sqrt y :=
    add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxy) (by norm_num only : (0 : ℝ) ≤ 6))
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3, hb.trans (Nat.floor_mono hc)⟩, hp⟩

/-- Input: a logarithmic allowance L and scale endpoints lo,hi.
Definition: price at lo times L plus signed cell excess on the support at hi.
Output: a scalar upper budget. Role: enclose the dual sum on a whole closed scale cell. -/
noncomputable def gammaSignedCellDualBudget (L lo hi : ℝ) : ℝ :=
  Analysis.gammaRamifiedDualParameter lo * L +
    ∑ p ∈ gammaSignedSupportPrimeSet hi,
      Real.log p *
        max (Analysis.gammaRamifiedSignedCellAllowance p lo hi - (5 / 4 : ℝ) / Real.sqrt hi) 0

/-- Input: L>=0 and 1<=lo<=x<=hi. Claim: the signed dual budget at x is bounded
by the fixed cell expression. Proof: retain the subtracted price at hi, enlarge the prime
support, and bound the linear price at lo. Role: enable uniform scale-interval certification. -/
theorem gamma_scale_signed_dual_budget_le_cell {L x lo hi : ℝ} (hL : 0 ≤ L) (hlo : 1 ≤ lo)
    (hlox : lo ≤ x) (hxhi : x ≤ hi) :
    gammaScaleSignedDualBudget L x ≤ gammaSignedCellDualBudget L lo hi := by
  have hlo0 : 0 < lo := zero_lt_one.trans_le hlo
  have hx1 := hlo.trans hlox
  rw [gamma_scale_signed_dual_budget_eq_small_support L hx1]
  have hs :=
    Analysis.gamma_ramified_theta_excess_sum_le_signed_cell (gammaSignedSupportPrimeSet x)
      (fun p hp ↦ (Finset.mem_filter.mp hp).2) (show (0 : ℝ) ≤ 5 / 4 by norm_num only) hlo0 hlox
      hxhi
  have he (z : ℝ) :
    Analysis.gammaRamifiedThetaParameter (5 / 4) z = Analysis.gammaRamifiedDualParameter z := by
    dsimp only [Analysis.gammaRamifiedThetaParameter, Analysis.gammaRamifiedDualParameter]
    rw [div_div]
  simp only [he] at hs
  have ht :=
    Finset.sum_le_sum_of_subset_of_nonneg (gamma_signed_support_mono hxhi) (f := fun p : ℕ ↦
      Real.log p *
        max (Analysis.gammaRamifiedSignedCellAllowance p lo hi - (5 / 4 : ℝ) / Real.sqrt hi) 0)
      (fun p hp _ ↦
        mul_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
          (le_max_right _ _))
  have hp : Analysis.gammaRamifiedDualParameter x ≤ Analysis.gammaRamifiedDualParameter lo := by
    exact
      div_le_div₀ (by norm_num only : (0 : ℝ) ≤ 5) le_rfl
        (mul_pos (by norm_num only) (Real.sqrt_pos.mpr hlo0))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlox) (by norm_num only))
  exact add_le_add (mul_le_mul_of_nonneg_right hp hL) (hs.trans ht)

/-- Input: odd nonsquare n, log n<=L, L>=0, and 4096<=lo<=x<=hi.
Claim: the actual Jacobi joint budget is bounded by the fixed signed cell dual allowance.
Proof: combine the factor-free budget with the uniform dual cell bound.
Role: connect closed-cell arithmetic bounds to the existing witness separation. -/
theorem gamma_joint_prefix_le_signed_cell_budget {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    {L b x lo hi : ℝ} (hL : 0 ≤ L) (hlog : Real.log n ≤ L) (hlo : 4096 ≤ lo) (hlox : lo ≤ x)
    (hxhi : x ≤ hi) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + gammaSignedCellDualBudget L lo hi -
          2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
        7 / 60 := by
  have hj :=
    gamma_joint_prefix_le_factor_free_budget_small_scale (b := b) hn hns hlog (hlo.trans hlox)
  have hd :=
    gamma_scale_signed_dual_budget_le_cell hL (show 1 ≤ lo by linarith only [hlo]) hlox hxhi
  dsimp only [gammaFactorFreeJointBudget] at hj
  linarith only [hj, hd]

end PseudoPrime.LLS
