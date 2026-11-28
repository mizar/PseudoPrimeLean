/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThreeFrequency644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThreeFrequency644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta

/-! # Symmetric Mellin kernel and cosine contours for section 122 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The even rational function whose restriction to the imaginary axis equals the
sixth-pole norm. Its only poles are the two real points ±107/100, each of order three. -/
noncomputable def quarterSymmetricKernel644 (z : ℂ) : ℂ :=
  (107 / 100 : ℂ) ^ 5 / (((107 / 100 : ℂ) - z) * ((107 / 100 : ℂ) + z)) ^ 3

/-- On the imaginary axis the symmetric rational function is the real sixth-pole
weight, including its normalization. -/
private theorem symmetric_axis (t : ℝ) :
    quarterSymmetricKernel644 (Complex.I * t) =
      (((107 / 100 : ℝ) ^ 5 / ((107 / 100 : ℝ) ^ 2 + t ^ 2) ^ 3 : ℝ) : ℂ) := by
  unfold quarterSymmetricKernel644
  push_cast
  rw [show
      ((107 / 100 : ℂ) - Complex.I * t) * (107 / 100 + Complex.I * t) =
        (107 / 100) ^ 2 + (t : ℂ) ^ 2
      by
      rw [mul_comm, ← sq_sub_sq, mul_pow, Complex.I_sq]
      ring]

private theorem exp_axis_644 (s t : ℝ) :
    (Complex.exp ((s : ℂ) * (Complex.I * t))).re = Real.cos (s * t) := by
  simp only [Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_add, add_zero, one_mul,
    Real.exp_zero]

private noncomputable def dilation : ℝ :=
  107 / 102

/-- The inverse profile of the symmetric sixth-pole kernel at pole 107/100.
It rescales the logarithmic coordinate of the pole-51/50 profile. -/
noncomputable def quarterSymmetricProfile644 (u : ℝ) : ℝ :=
  twoShiftSymmetricProfile (u ^ dilation)

private theorem kernel_dilation (s : ℂ) :
    quarterSymmetricKernel644 s =
      ((dilation⁻¹ : ℝ) : ℂ) * twoShiftSymmetricKernel (s / dilation) := by
  unfold quarterSymmetricKernel644 twoShiftSymmetricKernel dilation
  push_cast
  have hm : (51 / 50 : ℂ) - s / (107 / 102) = (107 / 100 - s) * (102 / 107) := by ring
  have hp : (51 / 50 : ℂ) + s / (107 / 102) = (107 / 100 + s) * (102 / 107) := by ring
  rw [hm, hp,
    show
      (107 / 100 - s) * (102 / 107) * ((107 / 100 + s) * (102 / 107)) =
        ((107 / 100 - s) * (107 / 100 + s)) * (102 / 107) ^ 2
      by ring]
  generalize (107 / 100 - s) * (107 / 100 + s) = D
  simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem profile_hasMellin {s : ℂ} (hl : -(107 / 100 : ℝ) < s.re) (hu : s.re < 107 / 100) :
    HasMellin (fun u ↦ (quarterSymmetricProfile644 u : ℂ)) s (quarterSymmetricKernel644 s) := by
  have hr : (s / dilation).re = s.re / dilation := Complex.div_ofReal_re _ _
  have hp : 0 < dilation := by norm_num only [dilation]
  have h :=
    twoShift_profile_hasMellin
      (show -(51 / 50 : ℝ) < (s / dilation).re
        by
        rw [hr, lt_div_iff₀ hp]
        norm_num only [dilation]
        linarith only [hl])
      (show (s / dilation).re < (51 / 50 : ℝ)
        by
        rw [hr, div_lt_iff₀ hp]
        norm_num only [dilation]
        linarith only [hu])
  refine ⟨(MellinConvergent.comp_rpow hp.ne').2 h.1, ?_⟩
  unfold quarterSymmetricProfile644
  rw [mellin_comp_rpow (fun v : ℝ ↦ (twoShiftSymmetricProfile v : ℂ)), h.2, abs_of_pos hp,
    Complex.real_smul, kernel_dilation]

private theorem den_re {z : ℂ} :
    (((107 / 100 : ℂ) - z) * (107 / 100 + z)).re = (107 / 100 : ℝ) ^ 2 - z.re ^ 2 + z.im ^ 2 := by
  rw [mul_comm, ← sq_sub_sq]
  simp only [Complex.sub_re, pow_two, Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- On the closed strip of real parts between -3/4 and 3/4 the even sixth-pole
kernel has uniform quadratic decay. The real part of its quadratic denominator
is bounded below by a positive constant plus the squared imaginary part. -/
private theorem symmetric_decay {z : ℂ} (hl : -(3 / 4 : ℝ) ≤ z.re) (hu : z.re ≤ 3 / 4) :
    ‖quarterSymmetricKernel644 z‖ ≤ 200 / (1 + ‖z‖ ^ 2) := by
  let D := ((107 / 100 : ℂ) - z) * (107 / 100 + z)
  have hr := sq_le_sq' hl hu
  have hd := Complex.re_le_norm D
  change (((107 / 100 : ℂ) - z) * (107 / 100 + z)).re ≤ ‖D‖ at hd
  rw [den_re] at hd
  have hpos : 1 / 3 ≤ ‖D‖ := by linarith only [hd, hr, sq_nonneg z.im]
  have hc : (1 / 3 : ℝ) ^ 2 ≤ ‖D‖ ^ 2 := pow_le_pow_left₀ (by norm_num only) hpos 2
  have hc3 := mul_le_mul_of_nonneg_right hc (norm_nonneg D)
  change ‖(107 / 100 : ℂ) ^ 5 / D ^ 3‖ ≤ _
  rw [norm_div, norm_pow, norm_pow, norm_div, Complex.norm_ofNat, Complex.norm_ofNat,
    div_le_div_iff₀ (pow_pos (by linarith only [hpos] : 0 < ‖D‖) _)
      (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)),
    Complex.sq_norm, Complex.normSq_apply]
  nlinarith only [hd, hr, hc3, sq_nonneg z.im]

/-- Both poles lie outside the closed three-quarter strip, so the rational kernel
is complex differentiable at every point of the strip. -/
private theorem symmetric_diff {z : ℂ} (hl : -(3 / 4 : ℝ) ≤ z.re) (hu : z.re ≤ 3 / 4) :
    DifferentiableAt ℂ quarterSymmetricKernel644 z := by
  have hn : ((107 / 100 : ℂ) - z) * (107 / 100 + z) ≠ 0 := by
    intro h
    have hh := den_re (z := z)
    rw [h, Complex.zero_re] at hh
    nlinarith only [hh, sq_le_sq' hl hu, sq_nonneg z.im]
  unfold quarterSymmetricKernel644
  fun_prop (disch := exact pow_ne_zero _ hn)

private theorem line_re (c t : ℝ) : ((c : ℂ) + Complex.I * t).re = c := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    zero_mul, mul_zero, sub_zero, add_zero]

/-- Uniform Cauchy decay makes the symmetric kernel integrable along each vertical
line with real part between -3/4 and 3/4. -/
private theorem symmetric_line {c : ℝ} (hl : -(3 / 4 : ℝ) ≤ c) (hu : c ≤ 3 / 4) :
    MeasureTheory.Integrable (fun t : ℝ ↦ quarterSymmetricKernel644 ((c : ℂ) + Complex.I * t)) := by
  have hc : Continuous (fun t : ℝ ↦ quarterSymmetricKernel644 ((c : ℂ) + Complex.I * t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (symmetric_diff (by rwa [line_re]) (by rwa [line_re])).continuousAt.comp
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul (200 : ℝ)).mono' hc.aestronglyMeasurable
  filter_upwards with t
  have hd := symmetric_decay (z := (c : ℂ) + Complex.I * t) (by rwa [line_re]) (by rwa [line_re])
  apply hd.trans
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left (by norm_num only) (by positivity)
  rw [Complex.sq_norm, Complex.normSq_apply, line_re]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add]
  nlinarith only [sq_nonneg c]

/-- The continuous exponential quadratic is the inverse on every line in the closed
three-quarter strip. Hence the inverse is independent of the line used for the contour. -/
private theorem symmetric_line_inversion {c u : ℝ} (hl : -(3 / 4 : ℝ) ≤ c) (hu : c ≤ 3 / 4)
    (hx : 0 < u) :
    Analysis.inverseMellin quarterSymmetricKernel644 c u = (quarterSymmetricProfile644 u : ℂ) := by
  let f := fun v : ℝ ↦ (quarterSymmetricProfile644 v : ℂ)
  have h (t : ℝ) :
    HasMellin f ((c : ℂ) + t * Complex.I)
      (quarterSymmetricKernel644 ((c : ℂ) + t * Complex.I)) := by
    apply profile_hasMellin <;> rw [mul_comm (t : ℂ) Complex.I, line_re] <;> linarith only [hl, hu]
  have hv : Complex.VerticalIntegrable quarterSymmetricKernel644 c := by
    simpa only [Complex.VerticalIntegrable, mul_comm Complex.I] using symmetric_line hl hu
  have hi := hv.congr (Filter.Eventually.of_forall fun t ↦ (h t).2.symm)
  have h0 : MellinConvergent f (c : ℂ) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using (h 0).1
  have hc : ContinuousAt f u := by
    have hc := Real.continuousAt_rpow_const u dilation (Or.inl hx.ne')
    have hlog := hc.log (Real.rpow_pos_of_pos hx dilation).ne'
    dsimp only [f, quarterSymmetricProfile644, twoShiftSymmetricProfile]
    apply Complex.continuous_ofReal.continuousAt.comp
    fun_prop
  change Analysis.inverseMellin quarterSymmetricKernel644 c u = f u
  rw [Analysis.inverseMellin_eq_mellinInv, ← mellinInv_mellin_eq c f hx h0 hi hc]
  unfold mellinInv
  congr 1
  exact
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun t ↦
        congrArg (fun z : ℂ ↦ (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) • z) (h t).2.symm)

/-- The symmetric sixth-pole test as an admissible Mellin kernel for the character
and principal contour formulas. Its inverse is the positive exponential quadratic,
and the strip of width 1/8 fits inside the region of uniform decay. -/
noncomputable def quarterSymmetricMellin644 : LLS.PaperStatements.MellinKernel where
  function := quarterSymmetricKernel644
  delta := 1 / 8
  delta_pos := by norm_num only
  region := {z | z.re ∈ Set.Ioo (-(3 / 4 : ℝ)) (3 / 4)}
  region_open := isOpen_Ioo.preimage Complex.continuous_re
  strip_subset := by
    intro z hz
    change -1 / 2 - 1 / 8 < z.re ∧ z.re ≤ 1 / 2 + 1 / 8 at hz
    exact ⟨by linarith only [hz.1], by linarith only [hz.2]⟩
  holomorphic := fun z hz ↦ (symmetric_diff hz.1.1.le hz.1.2.le).differentiableWithinAt
  regularized := fun z ↦ (z + 1 / 2) * quarterSymmetricKernel644 z
  regularized_holomorphic := fun z hz ↦
    (((differentiableAt_id (𝕜 := ℂ) (x := z)).add_const _).mul
        (symmetric_diff hz.1.le hz.2.le)).differentiableWithinAt
  regularized_eq := fun _ _ _ ↦ rfl
  decay := fun _ _ ↦ ⟨200, by norm_num only, fun _ hz _ ↦ symmetric_decay hz.1.le hz.2.le⟩
  mellin_integrable := fun _ _ hl hu hx ↦
    LLS.PaperStatements.integrable_inverseMellin_of_line hx
      (symmetric_line (by linarith only [hl]) (by linarith only [hu]))
  mellin_eq := by
    intro c u hl hu hx
    rw [symmetric_line_inversion (by linarith only [hl]) (by linarith only [hu]) hx,
      symmetric_line_inversion (by norm_num only) (by norm_num only) hx]
  mellin_nonneg := by
    intro u hx
    rw [symmetric_line_inversion (by norm_num only) (by norm_num only) hx, Complex.ofReal_re]
    unfold quarterSymmetricProfile644 twoShiftSymmetricProfile
    positivity
  mellin_nonzero := by
    refine ⟨1, zero_lt_one, ?_⟩
    rw [symmetric_line_inversion (by norm_num only) (by norm_num only) zero_lt_one,
      Complex.ofReal_re]
    norm_num only [quarterSymmetricProfile644, Real.one_rpow, twoShiftSymmetricProfile,
      Real.log_one, abs_zero, mul_zero, Real.exp_zero, zero_pow, OfNat.ofNat_ne_zero, add_zero,
      one_mul]
  mellin_real := by
    intro u hx
    rw [symmetric_line_inversion (by norm_num only) (by norm_num only) hx, Complex.ofReal_im]

/-- At a nonnegative frequency the real symmetric-kernel zero sum equals the two
vertical integrals less the forward arithmetic sum. The regularization residue
vanishes because the symmetric kernel is holomorphic at minus one half. -/
private theorem symmetric_contour {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {b : ℝ} (hb : 0 ≤ b) :
    let x := Real.exp b
    let W := fun s : ℂ ↦ quarterSymmetricKernel644 s * (x : ℂ) ^ s
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (∑' ρ, quarterSymmetricMellin644.oscillatingZeroTerm χ x ρ).re =
      (d * ∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * W (l t)).re +
          (d * ∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * W (r t)).re -
        (∑' n, quarterSymmetricMellin644.summand χ x n).re := by
  intro x W l r d
  have h :=
    LLS.PaperStatements.MellinKernel.tsum_summand_eq_completed_residue_formula
      quarterSymmetricMellin644 hq hG hp hn (inv_ne_one.mpr hn) (a := (-9 / 16 : ℝ)) (b := 9 / 16)
      (by norm_num only)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) (Real.one_le_exp hb) (by norm_num only)
      (by norm_num only)
  have hz (F : ℂ → ℂ) : quarterSymmetricMellin644.weightedResidue F x (-1 / 2) = 0 := by
    simp only [LLS.PaperStatements.MellinKernel.weightedResidue, ite_true]
    change -logDeriv F (-1 / 2) * (((-1 / 2 : ℂ) + 1 / 2) * _ * _) = 0
    rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]
  change
    (∑' n, quarterSymmetricMellin644.summand χ x n) =
      quarterSymmetricMellin644.weightedResidue _ x (-1 / 2) -
          (∑' ρ, quarterSymmetricMellin644.oscillatingZeroTerm χ x ρ) +
        d * (∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * W (l t)) +
        d * (∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * W (r t)) at h
  rw [hz, zero_sub] at h
  have he := congrArg Complex.re h
  simp only [Complex.add_re, Complex.neg_re] at he
  linarith only [he]

private theorem symmetric_zero_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) (ρ : ℂ) :
    (quarterSymmetricMellin644.oscillatingZeroTerm χ (Real.exp b) ρ).re =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ((107 / 100 : ℝ) ^ 5 / ((107 / 100 : ℝ) ^ 2 + ρ.im ^ 2) ^ 3) *
        Real.cos (b * ρ.im) := by
  unfold LLS.PaperStatements.MellinKernel.oscillatingZeroTerm
    LLS.PaperStatements.MellinKernel.kernelZeroTerm
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ←
    Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  change
    (((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℤ) : ℂ) *
          quarterSymmetricKernel644 (Complex.I * ρ.im) *
          _).re =
      _
  rw [symmetric_axis, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.re_ofReal_mul,
    exp_axis_644]

/-- The contour expression for a single frequency: the completed left integral
and the right gamma integral, less the forward symmetric-profile arithmetic sum. -/
noncomputable def quarterCosineContour644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) :
    ℝ :=
  let x := Real.exp b
  let W := fun s : ℂ ↦ quarterSymmetricKernel644 s * (x : ℂ) ^ s
  let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  (d * ∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * W (l t)).re +
      (d * ∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * W (r t)).re -
    (∑' n, quarterSymmetricMellin644.summand χ x n).re

/-- At a nonnegative fixed frequency the absolute sixth-pole zero mass
weighted by the cosine equals the corresponding real symmetric contour. -/
theorem quarter_cosine_contour_644 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {X b : ℝ} (hx : 0 < X) (hb : 0 ≤ b) :
    (∑' ρ : ℂ, ‖quarterKernel644.oscillatingZeroTerm χ X ρ‖ * Real.cos (b * ρ.im)) =
      quarterCosineContour644 χ b := by
  unfold quarterCosineContour644
  rw [← symmetric_contour hq hG hp hn hb,
    Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm quarterSymmetricMellin644 hq hG
        hp hn (inv_ne_one.mpr hn) (Real.exp_pos b))]
  apply tsum_congr
  intro ρ
  rw [LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm quarterKernel644 χ hx ρ,
    kernel_zero_norm hn, symmetric_zero_re, quarter_zero_norm_644]

/-- Under GRH the zero-frequency symmetric contour is the unweighted
absolute zero mass. This removes the common unshifted term from the phase gain. -/
theorem quarter_mass_cosine_644 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1) :
    quarterMass644 χ = quarterCosineContour644 χ 0 := by
  rw [← quarter_cosine_contour_644 hq hG hp hn zero_lt_one (le_refl (0 : ℝ))]
  simp only [zero_mul, Real.cos_zero, mul_one,
    LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm quarterKernel644 χ zero_lt_one]
  exact tsum_congr (fun ρ ↦ (kernel_zero_norm hn ρ).symm)

/-- Under GRH and agreement on primes through the cutoff, the section 122
three-frequency prime inequality can be written entirely with contour
remainders and forward sums. All three mixed frequencies are retained. -/
theorem quarter_three_contour_upper_644 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {X : ℝ} (hX : 1 ≤ X) (hcut : 1 ≤ X * Real.exp (-(3787 / 1000)))
    (hpass : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    let W := quarterCosineContour644 χ
    let C := fun y ↦ (contourRemainder644 χ y).re
    let S := fun y ↦ (∑' n, quarterKernel644.summand χ y n).re
    let T := fun t : ℝ ↦
      C (X * Real.exp (-t)) -
        (∑' n, quarterKernel644.summand (1 : DirichletCharacter ℂ 1) (X * Real.exp (-t)) n).re
    S X +
        (1.54 * (W (2687 / 1000) + T (2687 / 1000)) - 1.508 * (W (2707 / 1000) + T (2707 / 1000)) -
              0.0917 * (W (3787 / 1000) + T (3787 / 1000)) -
              ((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2) * quarterMass644 χ +
            1.54 * 1.508 * W (1 / 50) +
            1.54 * 0.0917 * W (11 / 10) -
          1.508 * 0.0917 * W (27 / 25)) ≤
      quarterMass644 χ + C X := by
  intro W C S T
  have hx := zero_lt_one.trans_le hX
  have h := quarter_three_prime_upper_644 hq hG hp hn hX hcut hpass
  dsimp only at h
  rw [quarter_cosine_contour_644 hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 2687 / 1000),
    quarter_cosine_contour_644 hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 2707 / 1000),
    quarter_cosine_contour_644 hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 3787 / 1000),
    quarter_cosine_contour_644 hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 1 / 50),
    quarter_cosine_contour_644 hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 11 / 10),
    quarter_cosine_contour_644 hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 27 / 25)] at h
  exact h

/-- At a positive input the inverse transform is an exponential quadratic
in the absolute logarithm. This form is used for the paired Euler weights. -/
theorem quarter_symmetric_transform_644 {u : ℝ} (hu : 0 < u) :
    let v := |Real.log u|
    quarterSymmetricMellin644.transform u =
      ((Real.exp (-(107 / 100) * v) *
            (3 / 16 + (3 * (107 / 100) / 16) * v + ((107 / 100) ^ 2 / 16) * v ^ 2) :
          ℝ) :
        ℂ) := by
  intro v
  have h : quarterSymmetricMellin644.transform u = (quarterSymmetricProfile644 u : ℂ) :=
    symmetric_line_inversion (c := 0) (by norm_num only) (by norm_num only) hu
  rw [h]
  apply congrArg Complex.ofReal
  dsimp only [quarterSymmetricProfile644, twoShiftSymmetricProfile, v]
  rw [Real.log_rpow hu, abs_mul, abs_of_nonneg (by norm_num only [dilation] : 0 ≤ dilation)]
  dsimp only [dilation]
  rw [show -(51 / 50 : ℝ) * (107 / 102 * |Real.log u|) = -(107 / 100) * |Real.log u| by ring]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
