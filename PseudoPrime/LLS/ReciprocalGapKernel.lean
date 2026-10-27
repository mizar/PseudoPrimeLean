/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalKernel
public import PseudoPrime.AnalyticNumberTheory.General.TwoPoleMellinInversion

/-! # Admissible compact reciprocal kernels with a positive adjustable gap -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- An open strip containing the allowed first pole and excluding the second.
The lower margin is min(h/2,1/4) and the upper edge is 3/4.
This permits every positive gap while retaining uniform real-part bounds. -/
noncomputable def reciprocalGapRegion (h : ℝ) : Set ℂ :=
  {s : ℂ | -1 / 2 - min (h / 2) (1 / 4) < s.re ∧ s.re < 3 / 4}

/-- In the gap region, the second shifted denominator has norm at least h/2.
Compare its real part with its norm and use the lower strip edge.
This is the quantitative denominator bound used in regularization and decay. -/
theorem reciprocalGap_second_norm_lower {h : ℝ} {s : ℂ} (hs : s ∈ reciprocalGapRegion h) :
    h / 2 ≤ ‖s + ((1 / 2 + h : ℝ) : ℂ)‖ := by
  have hr := Complex.re_le_norm (s + ((1 / 2 + h : ℝ) : ℂ))
  simp only [Complex.add_re, Complex.ofReal_re] at hr
  have hl : -1 / 2 - min (h / 2) (1 / 4) < s.re := hs.1
  linarith only [hr, hl, min_le_left (h / 2) (1 / 4)]

/-- For positive h in the gap region, the second denominator is nonzero.
Use its positive norm lower bound. This excludes the second pole from the region. -/
theorem reciprocalGap_second_shift_ne_zero {h : ℝ} (hh : 0 < h) {s : ℂ}
    (hs : s ∈ reciprocalGapRegion h) : s + ((1 / 2 + h : ℝ) : ℂ) ≠ 0 :=
  norm_pos_iff.mp (lt_of_lt_of_le (by linarith only [hh]) (reciprocalGap_second_norm_lower hs))

/-- For h,eta>0 in the gap region and first-pole distance at least eta,
the kernel norm is at most (3+6/(eta*h))/(1+norm(s)^2).
Separate small imaginary heights and large heights, retaining both denominators.
This certifies quadratic decay for each fixed positive gap. -/
theorem reciprocalGap_strip_bound {h η : ℝ} (hh : 0 < h) (hη : 0 < η) {s : ℂ}
    (hs : s ∈ reciprocalGapRegion h) (hd : η ≤ ‖s + 1 / 2‖) :
    ‖Analysis.reciprocalGapFunction h s‖ ≤ (3 + 6 / (η * h)) / (1 + ‖s‖ ^ 2) := by
  have hA : 0 < ‖s + 1 / 2‖ := hη.trans_le hd
  have hB := reciprocalGap_second_norm_lower hs
  have hB0 : 0 < ‖s + ((1 / 2 + h : ℝ) : ℂ)‖ := lt_of_lt_of_le (by linarith only [hh]) hB
  have hprod0 := mul_pos hA hB0
  have hlo : -(3 / 4 : ℝ) < s.re := by linarith only [hs.1, min_le_right (h / 2) (1 / 4)]
  have hsr : s.re ^ 2 ≤ 1 := by
    have hm :=
      mul_nonneg (show 0 ≤ s.re + 1 by linarith only [hlo])
        (show 0 ≤ 1 - s.re by linarith only [hs.2])
    nlinarith only [hm]
  have hsq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  unfold Analysis.reciprocalGapFunction Analysis.twoPoleFunction
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [norm_div, norm_one, norm_mul,
    div_le_div_iff₀ hprod0 (show 0 < 1 + ‖s‖ ^ 2 by linarith only [sq_nonneg ‖s‖])]
  by_cases ht : s.im ^ 2 ≤ 1
  · have hp := mul_le_mul hd hB (by linarith only [hh] : (0 : ℝ) ≤ h / 2) hA.le
    have hm :=
      mul_le_mul_of_nonneg_left hp (div_nonneg (by norm_num only : (0 : ℝ) ≤ 6) (mul_pos hη hh).le)
    have he : (6 / (η * h) : ℝ) * (η * (h / 2)) = 3 := by
      field_simp [hη.ne', hh.ne']
      ring
    nlinarith only [hm, he, hsq, hsr, ht, hprod0]
  · have ha := Complex.abs_im_le_norm (s + 1 / 2)
    have hb := Complex.abs_im_le_norm (s + ((1 / 2 + h : ℝ) : ℂ))
    norm_num only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, Complex.ofReal_im,
      zero_div, add_zero] at ha hb
    have hp := mul_le_mul ha hb (abs_nonneg s.im) hA.le
    rw [← sq, sq_abs] at hp
    have hm := mul_nonneg (div_nonneg (by norm_num only : (0 : ℝ) ≤ 6) (mul_pos hη hh).le) hprod0.le
    nlinarith only [hp, hm, hsq, hsr, lt_of_not_ge ht]

/-- For h>0, c>-1/2 and u>0, inverse Mellin integration gives the compact
profile with a=1/2. Translate the proved general Mellin inversion convention.
This supplies line independence, positivity and exact support for the kernel. -/
theorem inverseMellin_reciprocalGap {h c u : ℝ} (hh : 0 < h) (hc : (-1 / 2 : ℝ) < c) (hu : 0 < u) :
    inverseMellin (Analysis.reciprocalGapFunction h) c u =
      AnalyticNumberTheory.General.twoPoleMellinWeight (1 / 2) h u := by
  change inverseMellin (Analysis.twoPoleFunction (1 / 2) (1 / 2 + h)) c u = _
  rw [←
    AnalyticNumberTheory.General.mellinInv_twoPoleMellinWeight hh
      (show 0 < c + 1 / 2 by linarith only [hc]) hu]
  unfold inverseMellin mellinInv
  rw [Complex.real_smul]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul, mul_comm]

/-- Under the same positive-gap, line and argument assumptions, the inverse
Mellin integrand is integrable. Use vertical integrability and the constant
norm of the Mellin power. This discharges the admissible-kernel convergence field. -/
theorem integrable_inverseMellin_reciprocalGap {h c u : ℝ} (hh : 0 < h) (hc : (-1 / 2 : ℝ) < c)
    (hu : 0 < u) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) *
          (u : ℂ) ^ (-((c : ℂ) + Complex.I * t))) := by
  have hf :=
    AnalyticNumberTheory.General.verticalIntegrable_twoPoleFunction hh
      (show 0 < c + 1 / 2 by linarith only [hc])
  unfold Complex.VerticalIntegrable at hf
  apply integrable_inverseMellin_of_line hu
  exact
    hf.congr
      (Filter.Eventually.of_forall
        (fun t ↦ by
          unfold Analysis.reciprocalGapFunction
          change
            Analysis.twoPoleFunction (1 / 2) (1 / 2 + h) ((c : ℂ) + (t : ℂ) * Complex.I) =
              Analysis.twoPoleFunction (1 / 2) (1 / 2 + h) ((c : ℂ) + Complex.I * t)
          rw [mul_comm Complex.I (t : ℂ)]))

/-- At a point in the gap region other than -1/2, the kernel is complex
differentiable. Both shifted factors are nonzero. Differentiate their product
inverse. This proves holomorphy away from the allowed simple pole. -/
theorem differentiableAt_reciprocalGap {h : ℝ} (hh : 0 < h) {s : ℂ} (hs : s ∈ reciprocalGapRegion h)
    (hn : s ≠ -1 / 2) : DifferentiableAt ℂ (Analysis.reciprocalGapFunction h) s := by
  have hA : s + ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      reciprocal_shift_ne_zero hn
  have hd :
    DifferentiableAt ℂ (fun z : ℂ ↦ ((z + ((1 / 2 : ℝ) : ℂ)) * (z + ((1 / 2 + h : ℝ) : ℂ)))⁻¹) s :=
    (((differentiableAt_id (𝕜 := ℂ) (x := s)).add_const ((1 / 2 : ℝ) : ℂ)).mul
          ((differentiableAt_id (𝕜 := ℂ) (x := s)).add_const ((1 / 2 + h : ℝ) : ℂ))).inv
      (mul_ne_zero hA (reciprocalGap_second_shift_ne_zero hh hs))
  change
    DifferentiableAt ℂ (fun z : ℂ ↦ 1 / ((z + ((1 / 2 : ℝ) : ℂ)) * (z + ((1 / 2 + h : ℝ) : ℂ)))) s
  simpa only [one_div] using hd

/-- The admissible kernel for any positive gap h, with strip width
min(h/4,1/8). Its rational function, regularization, decay, integrability,
line independence and real positive compact inverse are all proved.
This makes adjustable gaps available to the existing contour and zero machinery. -/
noncomputable def reciprocalGapMellinKernel (h : ℝ) (hh : 0 < h) : MellinKernel where
  function := Analysis.reciprocalGapFunction h
  delta := min (h / 4) (1 / 8)
  delta_pos := lt_min (by linarith only [hh]) (by norm_num only)
  region := reciprocalGapRegion h
  region_open :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  strip_subset := by
    intro s hs
    have hm : min (h / 4) (1 / 8) ≤ min (h / 2) (1 / 4) :=
      min_le_min (by linarith only [hh]) (by norm_num only)
    exact ⟨by linarith only [hs.1, hm], by linarith only [hs.2, min_le_right (h / 4) (1 / 8)]⟩
  holomorphic := by
    intro s hs
    have hn : s ≠ -1 / 2 := by simpa only [Set.mem_singleton_iff] using hs.2
    exact (differentiableAt_reciprocalGap hh hs.1 hn).differentiableWithinAt
  regularized s := 1 / (s + ((1 / 2 + h : ℝ) : ℂ))
  regularized_holomorphic := by
    intro s hs
    have hd : DifferentiableAt ℂ (fun z : ℂ ↦ (z + ((1 / 2 + h : ℝ) : ℂ))⁻¹) s :=
      ((differentiableAt_id (𝕜 := ℂ) (x := s)).add_const ((1 / 2 + h : ℝ) : ℂ)).inv
        (reciprocalGap_second_shift_ne_zero hh hs)
    simpa only [one_div] using hd.differentiableWithinAt
  regularized_eq := by
    intro s _ hn
    have hA := reciprocal_shift_ne_zero hn
    simp only [one_div] at hA
    unfold Analysis.reciprocalGapFunction Analysis.twoPoleFunction
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    simp only [one_div, mul_inv]
    rw [← mul_assoc, mul_inv_cancel₀ hA, one_mul]
  decay := by
    intro η hη
    refine ⟨3 + 6 / (η * h), ?_, ?_⟩
    · exact
        add_pos_of_pos_of_nonneg (by norm_num only)
          (div_nonneg (by norm_num only) (mul_pos hη hh).le)
    · exact fun s hs hd ↦ reciprocalGap_strip_bound hh hη hs hd
  mellin_integrable := fun _ _ hc _ hu ↦ integrable_inverseMellin_reciprocalGap hh hc hu
  mellin_eq := by
    intro c u hc _ hu
    rw [inverseMellin_reciprocalGap hh hc hu, inverseMellin_reciprocalGap hh (by norm_num only) hu]
  mellin_nonneg := by
    intro u hu
    rw [inverseMellin_reciprocalGap hh (by norm_num only) hu]
    exact AnalyticNumberTheory.General.twoPoleMellinWeight_nonneg hh
  mellin_nonzero := by
    refine ⟨1 / 2, by norm_num only, ?_⟩
    rw [inverseMellin_reciprocalGap hh (by norm_num only) (by norm_num only)]
    exact
      (AnalyticNumberTheory.General.twoPoleMellinWeight_pos hh (by norm_num only : (0 : ℝ) < 1 / 2)
          (by norm_num only : (1 / 2 : ℝ) < 1)).ne'
  mellin_real := by
    intro u hu
    rw [inverseMellin_reciprocalGap hh (by norm_num only) hu]
    exact AnalyticNumberTheory.General.twoPoleMellinWeight_real (1 / 2) h u

end PseudoPrime.LLS.PaperStatements
