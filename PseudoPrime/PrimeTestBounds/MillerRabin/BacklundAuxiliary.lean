/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaHalfStripBounds

/-! # Rotated auxiliary function for the Backlund–Jensen method -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rotated Backlund auxiliary function at height `T` and exponent `N`.
It averages the two shifted zeta powers with conjugate unit phases, and is
real on the real axis. Its center value is positive for every exponent, so
the later Jensen argument does not need a selected subsequence. -/
noncomputable def backlundAux (T : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  let w := riemannZeta (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)
  let a := ((starRingEnd ℂ) w / (‖w‖ : ℂ)) ^ N
  (a * riemannZeta (z + (T : ℂ) * Complex.I) ^ N +
      (starRingEnd ℂ) a * riemannZeta (z - (T : ℂ) * Complex.I) ^ N) /
    2

/-- For any height and exponent, the Backlund auxiliary function is real on
the real axis. The two shifted zeta values and their coefficients are
complex conjugates. -/
theorem backlundAux_im_zero (T : ℝ) (N : ℕ) (x : ℝ) : (backlundAux T N (x : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have hc :
    (starRingEnd ℂ) (riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)) =
      riemannZeta ((x : ℂ) - (T : ℂ) * Complex.I) := by
    rw [← riemannZeta_conj]
    congr 1
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, sub_eq_add_neg]
  have hc' :
    (starRingEnd ℂ) (riemannZeta ((x : ℂ) - (T : ℂ) * Complex.I)) =
      riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) := by
    rw [← hc, starRingEnd_self_apply]
  dsimp only [backlundAux]
  simp only [map_div₀, map_add, map_mul, map_pow, starRingEnd_self_apply, map_ofNat, hc, hc']
  ring

/-- The auxiliary function at `3/2` equals the positive real number
`‖ζ(3/2 + iT)‖^N`. The rotation cancels the phase of the nonzero center value
for every natural exponent. -/
theorem backlundAux_center (T : ℝ) (N : ℕ) :
    backlundAux T N (((3 / 2 : ℝ) : ℂ)) =
      ((‖riemannZeta (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)‖ ^ N : ℝ) : ℂ) := by
  let w := riemannZeta (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)
  have hw : w ≠ 0 := by
    dsimp only [w]
    apply riemannZeta_ne_zero_of_one_lt_re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
    norm_num only
  have h0 : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
  have hu : (starRingEnd ℂ) w / (‖w‖ : ℂ) * w = (‖w‖ : ℂ) := by
    rw [div_mul_eq_mul_div, mul_comm ((starRingEnd ℂ) w), Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow, pow_two, mul_div_cancel_right₀ _ h0]
  have hplus : (((starRingEnd ℂ) w / (‖w‖ : ℂ)) ^ N) * w ^ N = ((‖w‖ ^ N : ℝ) : ℂ) := by
    rw [← mul_pow, hu, Complex.ofReal_pow]
  have hconj : riemannZeta (((3 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I) = (starRingEnd ℂ) w := by
    dsimp only [w]
    rw [← riemannZeta_conj]
    congr 1
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, sub_eq_add_neg]
  have hminus := congrArg (starRingEnd ℂ) hplus
  simp only [map_mul, map_pow, Complex.conj_ofReal] at hminus
  dsimp only [backlundAux]
  change
    (((starRingEnd ℂ) w / (‖w‖ : ℂ)) ^ N * w ^ N +
          (starRingEnd ℂ) (((starRingEnd ℂ) w / (‖w‖ : ℂ)) ^ N) *
            riemannZeta (((3 / 2 : ℝ) : ℂ) - (T : ℂ) * Complex.I) ^ N) /
        2 =
      ((‖w‖ ^ N : ℝ) : ℂ)
  rw [hconj, map_pow, hplus, hminus]
  ring

/-- The center of the Backlund auxiliary function is nonzero for every
height and exponent. This follows from the zero-free half-plane `Re s > 1`. -/
theorem backlundAux_center_ne_zero (T : ℝ) (N : ℕ) : backlundAux T N (((3 / 2 : ℝ) : ℂ)) ≠ 0 := by
  rw [backlundAux_center]
  apply Complex.ofReal_ne_zero.mpr
  apply pow_ne_zero
  apply norm_ne_zero_iff.mpr
  apply riemannZeta_ne_zero_of_one_lt_re
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  norm_num only

/-- The auxiliary function is complex differentiable at every point whose
imaginary part lies strictly between `-T` and `T`. The two shifted points
avoid the pole of zeta at one. -/
theorem backlundAux_differentiableAt {T : ℝ} (N : ℕ) {z : ℂ} (hz : -T < z.im ∧ z.im < T) :
    DifferentiableAt ℂ (backlundAux T N) z := by
  have hp : z + (T : ℂ) * Complex.I ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.one_im, mul_one, zero_mul, add_zero] at hi
    linarith only [hz.1, hi]
  have hm : z - (T : ℂ) * Complex.I ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.one_im, mul_one, zero_mul, add_zero] at hi
    linarith only [hz.2, hi]
  have hdp : DifferentiableAt ℂ (fun w : ℂ ↦ riemannZeta (w + (T : ℂ) * Complex.I)) z :=
    (differentiableAt_riemannZeta hp).comp z (differentiableAt_id.add_const _)
  have hdm : DifferentiableAt ℂ (fun w : ℂ ↦ riemannZeta (w - (T : ℂ) * Complex.I)) z :=
    (differentiableAt_riemannZeta hm).comp z (differentiableAt_id.sub_const _)
  let a : ℂ :=
    ((starRingEnd ℂ) (riemannZeta (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)) /
        (‖riemannZeta (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)‖ : ℂ)) ^
      N
  change
    DifferentiableAt ℂ
      (fun w : ℂ ↦
        (a * riemannZeta (w + (T : ℂ) * Complex.I) ^ N +
            (starRingEnd ℂ) a * riemannZeta (w - (T : ℂ) * Complex.I) ^ N) /
          2)
      z
  exact (((hdp.pow N).const_mul a).add ((hdm.pow N).const_mul ((starRingEnd ℂ) a))).div_const 2

/-- If `T > 2`, the auxiliary function is analytic on a neighborhood of the
closed disk of radius 2 centered at `3/2`. The disk lies inside the open
horizontal band where the two shifted zeta functions avoid their poles. -/
theorem backlundAux_analytic_disk {T : ℝ} (hT : 2 < T) (N : ℕ) :
    AnalyticOnNhd ℂ (backlundAux T N) (Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2) := by
  have hd : DifferentiableOn ℂ (backlundAux T N) (Complex.im ⁻¹' Set.Ioo (-T) T) := by
    intro z hz
    exact (backlundAux_differentiableAt N hz).differentiableWithinAt
  apply (hd.analyticOnNhd (isOpen_Ioo.preimage Complex.continuous_im)).mono
  intro z hz
  have hdist : ‖z - (((3 / 2 : ℝ) : ℂ))‖ ≤ 2 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hi := Complex.abs_im_le_norm (z - (((3 / 2 : ℝ) : ℂ)))
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hi
  have hab := abs_le.mp (hi.trans hdist)
  constructor <;> linarith only [hT, hab.1, hab.2]

/-- If both shifted zeta values have norm at most `M`, the rotated auxiliary
function has norm at most `M^N`. Both coefficients have norm one, so the
triangle inequality applies before taking any logarithms. -/
theorem norm_backlundAux_le (T : ℝ) (N : ℕ) (z : ℂ) {M : ℝ}
    (hp : ‖riemannZeta (z + (T : ℂ) * Complex.I)‖ ≤ M)
    (hm : ‖riemannZeta (z - (T : ℂ) * Complex.I)‖ ≤ M) : ‖backlundAux T N z‖ ≤ M ^ N := by
  let w := riemannZeta (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)
  let a := ((starRingEnd ℂ) w / (‖w‖ : ℂ)) ^ N
  have hw : w ≠ 0 := by
    dsimp only [w]
    apply riemannZeta_ne_zero_of_one_lt_re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
    norm_num only
  have h0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have ha : ‖a‖ = 1 := by
    dsimp only [a]
    rw [norm_pow, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg w), div_self h0, one_pow]
  have ha' : ‖(starRingEnd ℂ) a‖ = 1 := by rw [Complex.norm_conj, ha]
  have hpp : ‖a * riemannZeta (z + (T : ℂ) * Complex.I) ^ N‖ ≤ M ^ N := by
    rw [norm_mul, ha, one_mul, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hp N
  have hmm : ‖(starRingEnd ℂ) a * riemannZeta (z - (T : ℂ) * Complex.I) ^ N‖ ≤ M ^ N := by
    rw [norm_mul, ha', one_mul, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hm N
  change
    ‖(a * riemannZeta (z + (T : ℂ) * Complex.I) ^ N +
            (starRingEnd ℂ) a * riemannZeta (z - (T : ℂ) * Complex.I) ^ N) /
          2‖ ≤
      M ^ N
  rw [norm_div, Complex.norm_ofNat]
  have ht :=
    norm_add_le (a * riemannZeta (z + (T : ℂ) * Complex.I) ^ N)
      ((starRingEnd ℂ) a * riemannZeta (z - (T : ℂ) * Complex.I) ^ N)
  linarith only [ht, hpp, hmm]

/-- On `Re z ≥ 3/2`, the auxiliary function has norm at most `(14/5)^N`.
Both shifted zeta values stay in the same right half-plane and the rotation
does not change their norms. -/
theorem norm_backlundAux_right (T : ℝ) (N : ℕ) {z : ℂ} (hz : (3 / 2 : ℝ) ≤ z.re) :
    ‖backlundAux T N z‖ ≤ (14 / 5 : ℝ) ^ N := by
  apply norm_backlundAux_le T N z
  · apply (AnalyticNumberTheory.RiemannZeta.norm_zeta_lt_fourteen_fifths ?_).le
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hz
  · apply (AnalyticNumberTheory.RiemannZeta.norm_zeta_lt_fourteen_fifths ?_).le
    simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero] using hz

end PseudoPrime.PrimeTestBounds.MillerRabin
