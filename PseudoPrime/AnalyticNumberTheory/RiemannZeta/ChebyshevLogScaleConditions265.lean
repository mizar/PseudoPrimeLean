/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevScale43

/-! # Explicit-formula scale bounds from logarithmic height twenty-six and one half -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At logarithmic height at least 53/2, the exponential dominates one thousand
times the height, supplying the explicit-formula width and cutoff bounds. -/
theorem exp_half_lower_265 {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L) : 1000 * L ≤ Real.exp (L / 2) := by
  have he : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num only at h ⊢
    linarith only [h]
  have he13 : (400000 : ℝ) ≤ Real.exp 13 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2718 / 1000 by norm_num only) he 13
    rw [← Real.exp_nat_mul] at h
    norm_num only at h ⊢
    linarith only [h]
  have hstep := Real.add_one_le_exp (L / 2 - 13)
  have hm := mul_le_mul he13 hstep (by linarith only [hL]) (Real.exp_pos 13).le
  have heq : Real.exp (L / 2) = Real.exp 13 * Real.exp (L / 2 - 13) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  nlinarith only [hm, hL]

/-- For logarithmic height at least 53/2, the explicit-formula averaging width
is positive, its lower endpoint exceeds one, and the zero cutoff is at least
1000. These are the domain conditions for the normalized estimate. -/
theorem scale265_conditions {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L) :
    0 < Real.exp (L / 2) * L / Real.pi ∧
      1 < Real.exp L - Real.exp (L / 2) * L / Real.pi ∧
      1000 ≤ 2 * Real.pi * Real.exp (L / 2) / L := by
  have he := exp_half_lower_265 hL
  have hL0 : 0 < L := by linarith only [hL]
  have hp := Real.pi_pos
  have he0 := Real.exp_pos (L / 2)
  have hs : Real.exp L = Real.exp (L / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hh : 0 < Real.exp (L / 2) * L / Real.pi := div_pos (mul_pos he0 hL0) hp
  have hhalf : Real.exp (L / 2) * L / Real.pi ≤ Real.exp L / 2 := by
    rw [hs, div_le_div_iff₀ hp (by norm_num only : (0 : ℝ) < 2)]
    have hm := mul_le_mul_of_nonneg_left he he0.le
    nlinarith only [hm, hL, hp, Real.pi_gt_three, he0]
  have hx : 1 < Real.exp L - Real.exp (L / 2) * L / Real.pi := by
    have he1 : 1000 ≤ Real.exp (L / 2) := by nlinarith only [he, hL]
    have hh2 := sq_nonneg (Real.exp (L / 2) - 1)
    rw [hs] at hhalf ⊢
    nlinarith only [hhalf, he1, hh2]
  have hT : 1000 ≤ 2 * Real.pi * Real.exp (L / 2) / L := by
    apply (le_div_iff₀ hL0).2
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * Real.pi by linarith only [hp])
    nlinarith only [hm, hL, hp, Real.pi_gt_three]
  exact ⟨hh, hx, hT⟩

/-- At logarithmic height at least 53/2, the selected relative width is in
`(0, 1/2]`, the absolute width is at least one, and the corresponding cutoff
and logarithms have the forms used in the normalized explicit formula. -/
theorem scale265_identities {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L) :
    let δ := L / (Real.pi * Real.exp (L / 2))
    let h := Real.exp (L / 2) * L / Real.pi
    0 < δ ∧
      δ ≤ 1 / 2 ∧
      1 ≤ h ∧
      h = Real.exp L * δ ∧
      2 / δ = 2 * Real.pi * Real.exp (L / 2) / L ∧
      Real.log ((2 / δ) / (2 * Real.pi)) = L / 2 - Real.log L ∧
      Real.log (2 / δ) = L / 2 - Real.log L + Real.log (2 * Real.pi) := by
  dsimp only
  have hl : 0 < L := by linarith only [hL]
  have hp : 0 < Real.pi := Real.pi_pos
  have he : 0 < Real.exp (L / 2) := Real.exp_pos _
  have hδ : 0 < L / (Real.pi * Real.exp (L / 2)) := div_pos hl (mul_pos hp he)
  have hu : L / (Real.pi * Real.exp (L / 2)) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos hp he)).2
    have hh := exp_half_lower_265 hL
    nlinarith only [hL, hh, hp, Real.pi_gt_three]
  have he1 : (1 : ℝ) ≤ Real.exp (L / 2) := by
    have hh := exp_half_lower_265 hL
    linarith only [hh, hL]
  have hw : 1 ≤ Real.exp (L / 2) * L / Real.pi := by
    apply (le_div_iff₀ hp).2
    have hm := mul_le_mul_of_nonneg_left hL he.le
    nlinarith only [hm, he1, Real.pi_lt_four]
  have hs : Real.exp L = Real.exp (L / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hwid : Real.exp (L / 2) * L / Real.pi = Real.exp L * (L / (Real.pi * Real.exp (L / 2))) := by
    rw [hs, pow_two, mul_assoc]
    have h : Real.exp (L / 2) * (L / (Real.pi * Real.exp (L / 2))) = L / Real.pi := by
      rw [mul_comm Real.pi (Real.exp (L / 2)), ← mul_div_assoc, mul_div_mul_left _ _ he.ne']
    rw [h, mul_div_assoc]
  have hT : 2 / (L / (Real.pi * Real.exp (L / 2))) = 2 * Real.pi * Real.exp (L / 2) / L := by
    simp only [div_div_eq_mul_div, mul_assoc]
  have hTpi : (2 / (L / (Real.pi * Real.exp (L / 2)))) / (2 * Real.pi) = Real.exp (L / 2) / L := by
    rw [hT, div_div, mul_comm L (2 * Real.pi)]
    exact mul_div_mul_left _ _ (mul_ne_zero (by norm_num only : (2 : ℝ) ≠ 0) hp.ne')
  have hlog1 :
    Real.log ((2 / (L / (Real.pi * Real.exp (L / 2)))) / (2 * Real.pi)) = L / 2 - Real.log L := by
    rw [hTpi, Real.log_div he.ne' hl.ne', Real.log_exp]
  have hlog2 :
    Real.log (2 / (L / (Real.pi * Real.exp (L / 2)))) =
      L / 2 - Real.log L + Real.log (2 * Real.pi) := by
    rw [hT]
    have heq : 2 * Real.pi * Real.exp (L / 2) / L = (2 * Real.pi) * (Real.exp (L / 2) / L) := by
      ring
    rw [heq, Real.log_mul (ne_of_gt (mul_pos (by norm_num only) hp)) (ne_of_gt (div_pos he hl)),
      Real.log_div he.ne' hl.ne', Real.log_exp]
    ring
  exact ⟨hδ, hu, hw, hwid, hT, hlog1, hlog2⟩

/-- From logarithmic height 29 onward, the half-height exponential dominates
four times the cubic. The tenth exponential-series term supplies the bound
uniformly throughout the interval. -/
private theorem exp_half_cubic29 {L : ℝ} (hL : 29 ≤ L) : 4 * L ^ 3 ≤ Real.exp (L / 2) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hp := Real.pow_div_factorial_le_exp (L / 2) (by linarith only [hL]) 10
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hp
  have h7 := pow_le_pow_left₀ (show (0 : ℝ) ≤ 29 by norm_num only) hL 7
  norm_num only at h7
  have hm := mul_le_mul_of_nonneg_right h7 (pow_nonneg hL0 3)
  have heq : (L / 2) ^ 10 = L ^ 7 * L ^ 3 / 1024 := by ring
  rw [heq] at hp
  nlinarith only [hp, hm, pow_nonneg hL0 3]

/-- For `L ≥ 53/2`, the half-height exponential dominates four times the cubic.
A finite interval uses an explicit exponential lower bound, and the existing
high-range estimate covers `L ≥ 29`. -/
theorem exp_half_cubic265 {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L) : 4 * L ^ 3 ≤ Real.exp (L / 2) := by
  by_cases h29 : 29 ≤ L
  · exact exp_half_cubic29 h29
  · have hU : L ≤ 29 := le_of_not_ge h29
    have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ L by linarith only [hL]) hU 3
    have he : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by
      have h := Real.exp_one_gt_d9
      norm_num only at h ⊢
      linarith only [h]
    have he13 : (400000 : ℝ) ≤ Real.exp 13 := by
      have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2718 / 1000 by norm_num only) he 13
      rw [← Real.exp_nat_mul] at h
      norm_num only at h ⊢
      linarith only [h]
    have hemono : Real.exp 13 ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr (by linarith only [hL])
    norm_num only at hp
    linarith only [hp, he13, hemono]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
