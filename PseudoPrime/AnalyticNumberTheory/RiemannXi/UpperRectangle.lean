/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.RectangleZeroSums
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation

/-! # Xi zeros in a positive-height counting rectangle -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- Under RH, xi has no real zeros. Every xi zero is a nontrivial zeta
zero, whose absolute height is strictly larger than `2π`. -/
theorem riemannXi_real_ne_zero (hRH : RiemannHypothesis) (x : ℝ) : riemannXi (x : ℂ) ≠ 0 := by
  intro hz
  have hζ := riemannZeta_zero_of_riemannXi_zero hz
  have hr := riemannXi_zero_re_nonneg hz
  have hl := RiemannZeta.zero_height_gt_two_pi hRH hζ hr
  simp only [Complex.ofReal_im, abs_zero] at hl
  have hp := Real.pi_pos
  linarith only [hl, hp]

/-- At a good zeta height, xi is nonzero on the whole horizontal line.
Every xi zero is a zeta zero with nonnegative real part. -/
theorem riemannXi_good_height_ne_zero {t : ℝ}
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) (x : ℝ) :
    riemannXi ((x : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  intro hz
  have hζ := riemannZeta_zero_of_riemannXi_zero hz
  have hr := riemannXi_zero_re_nonneg hz
  apply hgood _ hζ hr
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, mul_one, mul_zero, add_zero, zero_add]

/-- Under RH, an xi zero in the closed rectangle with real sides `-1/2`
and `3/2` and heights `0` and `t > 0` lies in its interior when `t` is a
good zeta height. The strip bounds exclude the vertical sides, the low-zero
bound excludes the bottom, and the good-height hypothesis excludes the top. -/
theorem zero_mem_upper_rectangle_interior (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) {ρ : ℂ} (hz : riemannXi ρ = 0)
    (hclosed :
      ρ ∈
        Rectangle.rectangleClosedBox ((-(1 / 2 : ℝ) : ℝ) : ℂ)
          (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :
    ρ ∈
      RectangleGeometry.rectangleOpenBox ((-(1 / 2 : ℝ) : ℝ) : ℂ)
        (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
  have hr0 := riemannXi_zero_re_nonneg hz
  have hr1 := riemannXi_zero_re_le_one hz
  have hζ := riemannZeta_zero_of_riemannXi_zero hz
  have him0 := RiemannZeta.zero_height_gt_two_pi hRH hζ hr0
  have hne : ρ.im ≠ t := hgood ρ hζ hr0
  simp only [Rectangle.rectangleClosedBox, Complex.mem_reProdIm, Set.mem_uIcc, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add] at hclosed
  have hb : 0 ≤ ρ.im ∧ ρ.im ≤ t := by
    rcases hclosed.2 with h | h
    · exact h
    · constructor <;> linarith only [h.1, h.2, ht]
  simp only [RectangleGeometry.rectangleOpenBox, Complex.mem_reProdIm, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add,
    min_eq_left (by norm_num only : -(1 / 2 : ℝ) ≤ 3 / 2),
    max_eq_right (by norm_num only : -(1 / 2 : ℝ) ≤ 3 / 2), min_eq_left ht.le, max_eq_right ht.le,
    Set.mem_Ioo]
  have hp : 0 < Real.pi := Real.pi_pos
  constructor
  · constructor <;> linarith only [hr0, hr1]
  · constructor
    · have habs : ρ.im ≠ 0 := by
        intro h
        rw [h, abs_zero] at him0
        linarith only [him0, hp]
      exact lt_of_le_of_ne hb.1 (Ne.symm habs)
    · exact lt_of_le_of_ne hb.2 hne

/-- Under RH at a good positive height, the xi-zero ledger of the counting
rectangle is exactly the positive-height zeta ledger with its closed height
bound. Xi-to-zeta correspondence and the interior result preserve the
existing positive-zero counting convention. -/
theorem upper_rectangle_zeros_eq (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) :
    General.entireZerosInRectangle differentiable_riemannXi
        (by
          rw [riemannXi_zero]; norm_num only)
        ((-(1 / 2 : ℝ) : ℝ) : ℂ) (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      (RiemannZeta.zerosUpTo t).filter (fun ρ ↦ 0 < ρ.im) := by
  classical
  ext ρ
  rw [General.mem_entireZerosInRectangle, Finset.mem_filter, RiemannZeta.mem_zerosUpTo ht.le]
  constructor
  · rintro ⟨hbox, hz⟩
    have hi := zero_mem_upper_rectangle_interior hRH ht hgood hz hbox
    simp only [RectangleGeometry.rectangleOpenBox, Complex.mem_reProdIm, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add,
      min_eq_left ht.le, max_eq_right ht.le, Set.mem_Ioo] at hi
    refine ⟨⟨riemannZeta_zero_of_riemannXi_zero hz, riemannXi_zero_re_nonneg hz, ?_⟩, hi.2.1⟩
    rw [abs_of_pos hi.2.1]
    exact hi.2.2.le
  · rintro ⟨⟨hz, hre, him⟩, hp⟩
    have hxi := xi_zero_of_zeta_zero_of_re_nonneg hz hre
    have hr1 := riemannXi_zero_re_le_one hxi
    rw [abs_of_pos hp] at him
    refine ⟨?_, hxi⟩
    simp only [Rectangle.rectangleClosedBox, Complex.mem_reProdIm, Set.mem_uIcc, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add]
    constructor <;> left
    · constructor <;> linarith only [hre, hr1]
    · exact ⟨hp.le, him⟩

/-- Under RH at a good positive height, the positively oriented boundary
integral of the xi logarithmic derivative is `2πi` times the multiplicity-
weighted positive zeta zero count. The finite residue theorem applies to
the interior ledger, and xi multiplicities equal zeta multiplicities. -/
theorem upper_rectangle_logDeriv_count (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) :
    RectangleGeometry.rectangleBoundaryIntegral (logDeriv riemannXi) ((-(1 / 2 : ℝ) : ℝ) : ℂ)
        (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      2 * Real.pi * Complex.I * (RiemannZeta.positiveZeroCount t : ℂ) := by
  have h0 : riemannXi 0 ≠ 0 := by
    rw [riemannXi_zero]; norm_num only
  have hre : (((-(1 / 2 : ℝ) : ℝ) : ℂ)).re < ((((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
    simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero]
    norm_num only
  have him : (((-(1 / 2 : ℝ) : ℝ) : ℂ)).im < ((((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im := by
    simpa only [Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add] using ht
  have hopen :
    ∀
      ρ ∈
        General.entireZerosInRectangle differentiable_riemannXi h0 ((-(1 / 2 : ℝ) : ℝ) : ℂ)
          (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I),
      ρ ∈
        RectangleGeometry.rectangleOpenBox ((-(1 / 2 : ℝ) : ℝ) : ℂ)
          (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    intro ρ hρ
    obtain ⟨hbox, hz⟩ := (General.mem_entireZerosInRectangle _ _ _ _ _).mp hρ
    exact zero_mem_upper_rectangle_interior hRH ht hgood hz hbox
  have h :=
    General.weighted_entire_finite_contour differentiable_riemannXi h0 (W := fun _ ↦ (-1 : ℂ))
      (differentiable_const _) hre him hopen
  simp only [mul_neg, neg_neg, mul_one] at h
  rw [upper_rectangle_zeros_eq hRH ht hgood] at h
  unfold RiemannZeta.positiveZeroCount
  rw [Complex.ofReal_sum, Finset.mul_sum]
  rw [h]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hz := (RiemannZeta.mem_zerosUpTo ht.le).mp (Finset.mem_filter.mp hρ).1
  have hxi := xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2.1
  have he := zeroMultiplicity_eq_zetaMultiplicity_of_zero hxi
  change analyticOrderNatAt riemannXi ρ = _ at he
  rw [he, Complex.ofReal_natCast]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
