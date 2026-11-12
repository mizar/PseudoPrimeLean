/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevScale43

/-! # Explicit-formula scale conditions from logarithmic height 23.5 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At logarithmic height at least `47/2`, the exponential dominates five
thousand times the height. An elementary lower Taylor bound at `47/4` and
the exponential tangent inequality supply the estimate uniformly. -/
theorem exp_half_lower_235 {L : ℝ} (hL : (47 / 2 : ℝ) ≤ L) : 5000 * L ≤ Real.exp (L / 2) := by
  have he : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have he11 : (59000 : ℝ) ≤ Real.exp 11 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2718 / 1000 by norm_num only) he 11
    rw [← Real.exp_nat_mul] at h
    norm_num only at h ⊢
    linarith only [h]
  have he34 : (2 : ℝ) ≤ Real.exp (3 / 4) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 4) 4
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
      Nat.factorial_succ, Nat.cast_one, Nat.cast_ofNat, pow_zero, pow_succ, zero_add] at h
    linarith only [h]
  have hebase : (118000 : ℝ) ≤ Real.exp (47 / 4) := by
    have h := mul_le_mul he11 he34 (by norm_num only : (0 : ℝ) ≤ 2) (Real.exp_pos 11).le
    rw [← Real.exp_add] at h
    norm_num only at h
    exact h
  have hstep := Real.add_one_le_exp (L / 2 - 47 / 4)
  have hm := mul_le_mul hebase hstep (by linarith only [hL]) (Real.exp_pos _).le
  have heq : Real.exp (L / 2) = Real.exp (47 / 4) * Real.exp (L / 2 - 47 / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  nlinarith only [hm, hL]

/-- For `L ≥ 47/2`, the relative smoothing width is positive and at most
`1/1000`, the absolute width is positive, the lower endpoint exceeds one,
and the corresponding zero cutoff is at least `2000`. -/
theorem scale235_conditions {L : ℝ} (hL : (47 / 2 : ℝ) ≤ L) :
    0 < (5 * L) / (6 * Real.pi * Real.exp (L / 2)) ∧
      (5 * L) / (6 * Real.pi * Real.exp (L / 2)) ≤ 1 / 1000 ∧
      0 < (5 * L / (6 * Real.pi)) * Real.exp (L / 2) ∧
      1 < Real.exp L - (5 * L / (6 * Real.pi)) * Real.exp (L / 2) ∧
      2000 ≤ (12 * Real.pi * Real.exp (L / 2)) / (5 * L) := by
  have he := exp_half_lower_235 hL
  have hL0 : 0 < L := by linarith only [hL]
  have hp := Real.pi_pos
  have he0 := Real.exp_pos (L / 2)
  have hs : Real.exp L = Real.exp (L / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hδ : 0 < (5 * L) / (6 * Real.pi * Real.exp (L / 2)) :=
    div_pos (mul_pos (by norm_num only) hL0) (mul_pos (mul_pos (by norm_num only) hp) he0)
  have hδ' : (5 * L) / (6 * Real.pi * Real.exp (L / 2)) ≤ 1 / 1000 := by
    apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num only) hp) he0)).2
    have hm := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 6) hp.le)
    nlinarith only [hm, Real.pi_gt_three, hL]
  have hw : 0 < (5 * L / (6 * Real.pi)) * Real.exp (L / 2) :=
    mul_pos (div_pos (mul_pos (by norm_num only) hL0) (mul_pos (by norm_num only) hp)) he0
  have hhalf : (5 * L / (6 * Real.pi)) * Real.exp (L / 2) ≤ Real.exp L / 2 := by
    rw [hs]
    have hp' : 0 < 6 * Real.pi := mul_pos (by norm_num only) hp
    have hbound : 5 * L / (6 * Real.pi) ≤ Real.exp (L / 2) / 2 := by
      apply (div_le_div_iff₀ hp' (by norm_num only : (0 : ℝ) < 2)).2
      nlinarith only [he, hL, Real.pi_gt_three]
    have hm := mul_le_mul_of_nonneg_right hbound he0.le
    nlinarith only [hm]
  have hx : 1 < Real.exp L - (5 * L / (6 * Real.pi)) * Real.exp (L / 2) := by
    have he1 : 1000 ≤ Real.exp (L / 2) := by nlinarith only [he, hL]
    have hh2 := sq_nonneg (Real.exp (L / 2) - 1)
    rw [hs] at hhalf ⊢
    nlinarith only [hhalf, he1, hh2]
  have hT : 2000 ≤ (12 * Real.pi * Real.exp (L / 2)) / (5 * L) := by
    apply (le_div_iff₀ (mul_pos (by norm_num only) hL0)).2
    have hm := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 12) hp.le)
    nlinarith only [hm, hL, Real.pi_gt_three]
  exact ⟨hδ, hδ', hw, hx, hT⟩

/-- At `L ≥ 47/2`, the selected relative width is positive and at most
`1/1000`; the absolute width, cutoff, and cutoff logarithm have the displayed
forms. These identities normalize the explicit zero-split estimate. -/
theorem scale235_identities {L : ℝ} (hL : (47 / 2 : ℝ) ≤ L) :
    let δ := 5 * L / (6 * Real.pi * Real.exp (L / 2))
    let h := (5 * L / (6 * Real.pi)) * Real.exp (L / 2)
    0 < δ ∧
      δ ≤ 1 / 1000 ∧
      h = Real.exp L * δ ∧
      2 / δ = 12 * Real.pi * Real.exp (L / 2) / (5 * L) ∧
      Real.log ((2 / δ) / (2 * Real.pi)) = L / 2 - Real.log (5 * L / 6) := by
  dsimp only
  have hl : 0 < L := by linarith only [hL]
  have hp : 0 < Real.pi := Real.pi_pos
  have he : 0 < Real.exp (L / 2) := Real.exp_pos _
  have hc := scale235_conditions hL
  have hs : Real.exp L = Real.exp (L / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hT :
    2 / (5 * L / (6 * Real.pi * Real.exp (L / 2))) = 12 * Real.pi * Real.exp (L / 2) / (5 * L) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  refine ⟨hc.1, hc.2.1, ?_, hT, ?_⟩
  · rw [hs]
    have hcancel := mul_inv_cancel₀ he.ne'
    simp only [div_eq_mul_inv, mul_inv_rev] at hcancel ⊢
    linear_combination (-5 * L * Real.pi⁻¹ * (6 : ℝ)⁻¹ * Real.exp (L * 2⁻¹)) * hcancel
  · have hlog :
      (2 / (5 * L / (6 * Real.pi * Real.exp (L / 2)))) / (2 * Real.pi) =
        Real.exp (L / 2) / (5 * L / 6) := by
      rw [hT]
      have hcancel := mul_inv_cancel₀ hp.ne'
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv] at hcancel ⊢
      linear_combination (6 * Real.exp (L * 2⁻¹) * L⁻¹ * (5 : ℝ)⁻¹) * hcancel
    rw [hlog,
      Real.log_div he.ne' (ne_of_gt (div_pos (mul_pos (by norm_num only) hl) (by norm_num only))),
      Real.log_exp]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
