/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundAuxiliary
public import Mathlib.Analysis.Complex.JensenFormula
import PseudoPrime.PrimeTestBounds.MillerRabin.ZetaHalfStripCircle
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaHalfStripReciprocal

/-! # Bounds for the left half of the Backlund circle -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A circle average is bounded by `K` if the values at every pair of
opposite points sum to at most `2K`. Rotation by π preserves the average;
circle integrability permits the sum to be averaged term by term. -/
private theorem circleAverage_le_of_pair {f : ℂ → ℝ} {c : ℂ} {R K : ℝ} (hf : CircleIntegrable f c R)
    (hpair : ∀ z ∈ Metric.sphere c |R|, f z + f (2 * c - z) ≤ 2 * K) :
    Real.circleAverage f c R ≤ K := by
  have hmap (θ : ℝ) : 2 * c - circleMap c R θ = circleMap c (-R) θ := by
    simp only [circleMap, Complex.ofReal_neg]
    ring
  have hfr : CircleIntegrable (fun z ↦ f (2 * c - z)) c R := by
    have h := (circleIntegrable_neg_radius (f := f)).2 hf
    unfold CircleIntegrable at h ⊢
    simpa only [hmap] using h
  have havg : Real.circleAverage (fun z ↦ f (2 * c - z)) c R = Real.circleAverage f c R := by
    rw [Real.circleAverage_def, Real.circleAverage_def]
    have heq :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), f (2 * c - circleMap c R θ)) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), f (circleMap c (-R) θ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      exact congrArg f (hmap θ)
    rw [heq]
    exact Real.circleAverage_neg_radius
  have hsum := Real.circleAverage_mono_on_of_le_circle (hf.add hfr) hpair
  rw [Real.circleAverage_add hf hfr, havg] at hsum
  linarith only [hsum]

/-- The logarithm of a nonnegative number bounded by `M^N` is at most
`N * log M` when `M ≥ 1`. The zero case uses Lean's total real logarithm. -/
private theorem log_le_nat_mul_of_le_pow {v M : ℝ} {N : ℕ} (hv0 : 0 ≤ v) (hM : 1 ≤ M)
    (hv : v ≤ M ^ N) : Real.log v ≤ (N : ℝ) * Real.log M := by
  by_cases hz : v = 0
  · rw [hz, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hM)
  · have hvpos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hz)
    have hb := Real.log_le_log hvpos hv
    rw [Real.log_pow] at hb
    exact hb

/-- The auxiliary function at the center has norm at least `(5/14)^N`.
The explicit reciprocal zeta estimate supplies a positive uniform lower
bound, which is needed for Jensen's center term. -/
theorem backlundAux_center_norm_lower (T : ℝ) (N : ℕ) :
    (5 / 14 : ℝ) ^ N ≤ ‖backlundAux T N (((3 / 2 : ℝ) : ℂ))‖ := by
  rw [backlundAux_center, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  apply pow_le_pow_left₀ (by norm_num only)
  apply AnalyticNumberTheory.RiemannZeta.five_fourteenths_le_norm_zeta
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  exact le_rfl

/-- For `T ≥ 17`, if `z` is in the left strip and `|Im z| ≤ 2`, the rotated
auxiliary function is bounded by `[T * exp (6 / (T - 2)^2)]^N`. Both shifted
zeta values satisfy the explicit strip bound at heights within 2 of `T`. -/
theorem norm_backlundAux_left {T : ℝ} (hT : 17 ≤ T) (N : ℕ) {z : ℂ} (hlo : (-(1 / 2) : ℝ) ≤ z.re)
    (hhi : z.re ≤ 3 / 2) (him : |z.im| ≤ 2) :
    ‖backlundAux T N z‖ ≤ (T * Real.exp (6 / (T - 2) ^ 2)) ^ N := by
  have hpRe : (z + (T : ℂ) * Complex.I).re = z.re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hmRe : (z - (T : ℂ) * Complex.I).re = z.re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero]
  have hpIm : (z + (T : ℂ) * Complex.I).im = z.im + T := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, zero_mul, add_zero]
  have hmIm : (z - (T : ℂ) * Complex.I).im = z.im - T := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, zero_mul, add_zero]
  have hb := abs_le.mp him
  apply norm_backlundAux_le T N z
  · apply
      norm_zeta_le_height hT
        (by
          rw [hpRe]; exact hlo)
        (by
          rw [hpRe]; exact hhi)
    · rw [hpIm]
      have ha := le_abs_self (z.im + T)
      linarith only [hb.1, ha]
    · rw [hpIm]
      apply abs_le.mpr
      constructor <;> linarith only [hT, hb.1, hb.2]
  · apply
      norm_zeta_le_height hT
        (by
          rw [hmRe]; exact hlo)
        (by
          rw [hmRe]; exact hhi)
    · rw [hmIm]
      have ha := neg_le_abs (z.im - T)
      linarith only [hb.2, ha]
    · rw [hmIm]
      apply abs_le.mpr
      constructor <;> linarith only [hT, hb.1, hb.2]

/-- On the left half of the closed disk of radius 2 centered at `3/2`, the
explicit Backlund auxiliary bound holds for every height `T ≥ 17`. The disk
geometry supplies the real-part and imaginary-part bounds. -/
theorem norm_backlundAux_left_disk {T : ℝ} (hT : 17 ≤ T) (N : ℕ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2) (hleft : z.re ≤ 3 / 2) :
    ‖backlundAux T N z‖ ≤ (T * Real.exp (6 / (T - 2) ^ 2)) ^ N := by
  have hdist : ‖z - (((3 / 2 : ℝ) : ℂ))‖ ≤ 2 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hre := Complex.abs_re_le_norm (z - (((3 / 2 : ℝ) : ℂ)))
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  have hlo := (abs_le.mp (hre.trans hdist)).1
  have him := Complex.abs_im_le_norm (z - (((3 / 2 : ℝ) : ℂ)))
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
  apply norm_backlundAux_left hT N (by linarith only [hlo]) hleft (him.trans hdist)

/-- For `T ≥ 17`, the average of `log ‖H_N‖` on the Backlund circle is at
most `N/2` times the sum of the explicit left- and right-semicircle log
bounds. Pairing opposite points avoids introducing a piecewise integrand. -/
theorem backlundAux_circleAverage_le {T : ℝ} (hT : 17 ≤ T) (N : ℕ) :
    Real.circleAverage (fun z ↦ Real.log ‖backlundAux T N z‖) (((3 / 2 : ℝ) : ℂ)) 2 ≤
      ((N : ℝ) / 2) * (Real.log (14 / 5) + Real.log T + 6 / (T - 2) ^ 2) := by
  have hT0 : 0 < T := by linarith only [hT]
  have hE : 1 ≤ Real.exp (6 / (T - 2) ^ 2) :=
    Real.one_le_exp (div_nonneg (by norm_num only) (sq_nonneg _))
  have hM : 1 ≤ T * Real.exp (6 / (T - 2) ^ 2) := by
    have hm :=
      mul_le_mul (show (1 : ℝ) ≤ T by linarith only [hT]) hE (by norm_num only : (0 : ℝ) ≤ 1) hT0.le
    norm_num only [one_mul] at hm
    exact hm
  have hLeft {z : ℂ} (hz : z ∈ Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2) (hleft : z.re ≤ 3 / 2) :
    Real.log ‖backlundAux T N z‖ ≤ (N : ℝ) * (Real.log T + 6 / (T - 2) ^ 2) := by
    have hb := norm_backlundAux_left_disk hT N hz hleft
    have hl := log_le_nat_mul_of_le_pow (norm_nonneg _) hM hb
    rw [Real.log_mul hT0.ne' (Real.exp_ne_zero _), Real.log_exp] at hl
    exact hl
  have hRight {z : ℂ} (hright : (3 / 2 : ℝ) ≤ z.re) :
    Real.log ‖backlundAux T N z‖ ≤ (N : ℝ) * Real.log (14 / 5) := by
    exact
      log_le_nat_mul_of_le_pow (norm_nonneg _) (by norm_num only)
        (norm_backlundAux_right T N hright)
  have hint : CircleIntegrable (fun z ↦ Real.log ‖backlundAux T N z‖) (((3 / 2 : ℝ) : ℂ)) 2 := by
    apply MeromorphicOn.circleIntegrable_log_norm
    have ha :=
      (backlundAux_analytic_disk (by linarith only [hT]) N).mono
        (Metric.sphere_subset_closedBall :
          Metric.sphere (((3 / 2 : ℝ) : ℂ)) 2 ⊆ Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2)
    simpa only [abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)] using ha.meromorphicOn
  apply circleAverage_le_of_pair hint
  intro z hz
  have hz' : z ∈ Metric.sphere (((3 / 2 : ℝ) : ℂ)) 2 := by
    simpa only [abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)] using hz
  have hw : 2 * (((3 / 2 : ℝ) : ℂ)) - z ∈ Metric.sphere (((3 / 2 : ℝ) : ℂ)) 2 := by
    rw [Metric.mem_sphere, dist_eq_norm] at hz' ⊢
    have heq : 2 * (((3 / 2 : ℝ) : ℂ)) - z - (((3 / 2 : ℝ) : ℂ)) = -(z - (((3 / 2 : ℝ) : ℂ))) := by
      ring
    rw [heq, norm_neg]
    exact hz'
  have hzball := Metric.sphere_subset_closedBall hz'
  have hwball := Metric.sphere_subset_closedBall hw
  have hwre : (2 * (((3 / 2 : ℝ) : ℂ)) - z).re = 3 - z.re := by
    have hre : (2 : ℂ).re = 2 := rfl
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hre, mul_zero,
      sub_zero]
    norm_num only
  by_cases hleft : z.re ≤ 3 / 2
  · have h₁ := hLeft hzball hleft
    have h₂ :=
      hRight (z := 2 * (((3 / 2 : ℝ) : ℂ)) - z)
        (by
          rw [hwre]; linarith only [hleft])
    nlinarith only [h₁, h₂]
  · have hright : (3 / 2 : ℝ) ≤ z.re := le_of_not_ge hleft
    have h₁ := hRight hright
    have h₂ :=
      hLeft hwball
        (by
          rw [hwre]; linarith only [hright])
    nlinarith only [h₁, h₂]

/-- For `T > 2`, Jensen's formula expresses the circle average of the
logarithmic auxiliary-function norm as the multiplicity-weighted zero sum
plus its center term. Analyticity on the disk and nonvanishing at the center
hold for every natural exponent. -/
theorem backlundAux_jensen {T : ℝ} (hT : 2 < T) (N : ℕ) :
    Real.circleAverage (fun z ↦ Real.log ‖backlundAux T N z‖) (((3 / 2 : ℝ) : ℂ)) 2 =
      (∑ᶠ u : ℂ,
          (MeromorphicOn.divisor (backlundAux T N) (Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2) u :
              ℝ) *
            Real.log (2 * ‖(((3 / 2 : ℝ) : ℂ)) - u‖⁻¹)) +
        Real.log ‖backlundAux T N (((3 / 2 : ℝ) : ℂ))‖ := by
  have h :=
    AnalyticOnNhd.circleAverage_log_norm (f := backlundAux T N) (c := (((3 / 2 : ℝ) : ℂ))) (R := 2)
      (by norm_num only)
      (by
        simpa only [abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)] using
          backlundAux_analytic_disk hT N)
      (backlundAux_center_ne_zero T N)
  rw [show |(2 : ℝ)| = 2 by norm_num only] at h
  exact h

/-- For `T ≥ 17`, Jensen's multiplicity-weighted zero sum for the rotated
auxiliary function is bounded by `N` times the explicit circle budget. The
paired semicircle estimate controls the average and the reciprocal zeta
estimate controls the center term. -/
theorem backlundAux_jensen_budget {T : ℝ} (hT : 17 ≤ T) (N : ℕ) :
    (∑ᶠ u : ℂ,
        (MeromorphicOn.divisor (backlundAux T N) (Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2) u : ℝ) *
          Real.log (2 * ‖(((3 / 2 : ℝ) : ℂ)) - u‖⁻¹)) ≤
      (N : ℝ) * ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) := by
  have hcenter := backlundAux_center_norm_lower T N
  have hlog := Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 5 / 14) N) hcenter
  rw [Real.log_pow] at hlog
  have hrecip : Real.log (5 / 14 : ℝ) = -Real.log (14 / 5 : ℝ) := by
    rw [show (5 / 14 : ℝ) = (14 / 5 : ℝ)⁻¹ by norm_num only, Real.log_inv]
  rw [hrecip] at hlog
  have hj := backlundAux_jensen (by linarith only [hT] : 2 < T) N
  have havg := backlundAux_circleAverage_le hT N
  have heq :
    ((N : ℝ) / 2) * (Real.log (14 / 5) + Real.log T + 6 / (T - 2) ^ 2) -
        (N : ℝ) * -Real.log (14 / 5) =
      (N : ℝ) * ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) := by
    ring
  linarith only [hj, havg, hlog, heq]

end PseudoPrime.PrimeTestBounds.MillerRabin
