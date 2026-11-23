/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPsiLeeNosal
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevThetaHighMargin
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLinearBound
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Lower Lee–Nosal estimate on the high half-line -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A finite rational exponential sum supplies the three endpoint growth estimates. -/
private theorem exp_floor28 (q k : ℚ) (hq : 0 ≤ q)
    (hk : k ≤ (Finset.range 28).sum (fun i => q ^ i / i.factorial)) :
    (k : ℝ) ≤ Real.exp (q : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).2 hk
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] at h
  exact h.trans (Real.sum_le_exp_of_nonneg (by exact_mod_cast hq) 28)

/-- Exponential growth at rate one eighth dominates the logarithmic coordinate above 53/2. -/
private theorem log_le_exp_eighth {L : ℝ} (hl : 53 / 2 ≤ L) : L ≤ Real.exp (L / 8) := by
  have h := exp_floor28 (53 / 16) (53 / 2) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hs := Real.add_one_le_exp ((L - 53 / 2) / 8)
  have ht := mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 53 / 2)
  have he := mul_le_mul_of_nonneg_right h (Real.exp_pos ((L - 53 / 2) / 8)).le
  rw [← Real.exp_add, show (53 / 16 : ℝ) + (L - 53 / 2) / 8 = L / 8 by ring] at he
  linarith only [hl, ht, he]

/-- Under RH the square-root psi contribution exceeds its argument by at most one part in 96. -/
private theorem psi_half_le {L : ℝ} (hRH : RiemannHypothesis) (hl : 53 / 2 ≤ L) :
    Chebyshev.psi (Real.exp (L / 2)) ≤ (1 + 1 / 96) * Real.exp (L / 2) := by
  let z := Real.exp (L / 4)
  have hL := log_le_exp_eighth hl
  have hz : L ^ 2 ≤ z := by
    have h := pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ L) hL 2
    simpa only [pow_two, ← Real.exp_add, show L / 8 + L / 8 = L / 4 by ring] using h
  have hz0 : 0 ≤ z := (Real.exp_pos _).le
  have hy : z * z = Real.exp (L / 2) := by
    dsimp only [z]
    rw [← Real.exp_add, show L / 4 + L / 4 = L / 2 by ring]
  have hy101 : 101 ≤ Real.exp (L / 2) := by
    have hz101 : 101 ≤ z := by
      nlinarith only [hl, hz, mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ L by linarith only [hl])]
    exact hz101.trans (Real.exp_le_exp.mpr (by linarith only [hl]))
  have h := Arithmetic.psi_lee_nosal_of_RH hRH hy101
  have hb := (le_abs_self _).trans ((div_le_iff₀ (Real.sqrt_pos.2 (Real.exp_pos _))).1 h)
  rw [Real.log_exp, ← Real.exp_half, show L / 2 / 2 = L / 4 by ring] at hb
  have hn := Real.log_nonneg (by linarith only [hl] : 1 ≤ L / 2)
  have hc : RiemannZeta.leeNosalPsiLog (L / 2) ≤ z / 96 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).2
    nlinarith only [hz, mul_nonneg (show 0 ≤ L by linarith only [hl]) hn,
      mul_nonneg hz0 (sub_nonneg.mpr Real.pi_gt_three.le)]
  have hm := mul_le_mul_of_nonneg_right hc hz0
  change
    Chebyshev.psi (Real.exp (L / 2)) - Real.exp (L / 2) ≤
      RiemannZeta.leeNosalPsiLog (L / 2) * z at hb
  nlinarith only [hb, hm, hy]

/-- Linear estimates for the cube and fifth roots use fixed fractions of the square root. -/
private theorem small_roots_le {L : ℝ} (hl : 53 / 2 ≤ L) :
    80 * Real.exp (L / 3) ≤ Real.exp (L / 2) ∧ 2500 * Real.exp (L / 5) ≤ Real.exp (L / 2) := by
  have h3 := exp_floor28 (53 / 12) 80 (by decide +kernel) (by decide +kernel)
  have h5 := exp_floor28 (159 / 20) 2500 (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h3 h5
  have hc := h3.trans (Real.exp_le_exp.mpr (by linarith only [hl] : 53 / 12 ≤ L / 6))
  have hf := h5.trans (Real.exp_le_exp.mpr (by linarith only [hl] : 159 / 20 ≤ 3 * L / 10))
  constructor
  · simpa only [← Real.exp_add, show L / 6 + L / 3 = L / 2 by ring] using
      mul_le_mul_of_nonneg_right hc (Real.exp_pos (L / 3)).le
  · simpa only [← Real.exp_add, show 3 * L / 10 + L / 5 = L / 2 by ring] using
      mul_le_mul_of_nonneg_right hf (Real.exp_pos (L / 5)).le

/-- Above logarithmic height 53/2 the square, cube and fifth root contributions together
consume at most 103/100 of normalized error. -/
private theorem high_prime_power_le (hRH : RiemannHypothesis) {L : ℝ} (hl : 53 / 2 ≤ L) :
    (Chebyshev.psi (Real.exp L) - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      103 / 100 := by
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (Real.exp L)
  simp only [← Real.exp_mul, ← div_eq_mul_inv] at h
  have h3 := Arithmetic.psi_le_111 (Real.exp_pos (L / 3)).le
  have h5 := Arithmetic.psi_le_111 (Real.exp_pos (L / 5)).le
  obtain ⟨hc, hf⟩ := small_roots_le hl
  rw [← Real.exp_half]
  apply (div_le_iff₀ (Real.exp_pos _)).2
  linarith only [h, psi_half_le hRH hl, h3, h5, hc, hf, Real.exp_pos (L / 2)]

/-- Under RH, theta satisfies the lower Lee–Nosal estimate whenever log x is at least 53/2. -/
theorem theta_lower_log_half53 (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hl : 53 / 2 ≤ Real.log x) :
    (x - Chebyshev.theta x) / Real.sqrt x ≤ RiemannZeta.leeNosalPsiLog (Real.log x) := by
  have hp := (RiemannZeta.psi_integrated_of_RH hRH hx (by linarith only [hl])).1
  have hn := neg_le_abs (Chebyshev.psi x - x)
  rw [neg_sub] at hn
  have he :=
    (div_le_div_of_nonneg_right hn (Real.sqrt_nonneg x)).trans
      (hp.trans (RiemannZeta.integrated_envelope_margin_half53 hl))
  have hd := high_prime_power_le hRH hl
  rw [Real.exp_log hx] at hd
  have h := add_le_add he hd
  rw [← add_div, sub_add_sub_cancel] at h
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
