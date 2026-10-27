/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.TwoPoleMellinWeights

/-! # Mellin inversion for compact profiles with adjustable reciprocal poles -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For h>0 and u>0, express the compact profile as u^a times the positive
part of 1-u^h, divided by h. Split at one and use monotonicity of powers.
This gives a continuous expression through the support endpoint. -/
theorem twoPoleMellinWeight_eq_clamped {a h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    twoPoleMellinWeight a h u = ((u ^ a * max (1 - u ^ h) 0 / h : ℝ) : ℂ) := by
  by_cases h1 : u ≤ 1
  · have hmem : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨hu, h1⟩
    rw [twoPoleMellinWeight_on_support hmem,
      max_eq_left (sub_nonneg.mpr (Real.rpow_le_one hu.le h1 hh.le)), Real.rpow_add hu]
    congr 1
    ring
  · have hoff : u ∉ Set.Ioc (0 : ℝ) 1 := fun h ↦ h1 h.2
    have hpow : 1 ≤ u ^ h := Real.one_le_rpow (le_of_lt (lt_of_not_ge h1)) hh.le
    rw [twoPoleMellinWeight_off_support hoff, max_eq_right (by linarith only [hpow]), mul_zero,
      zero_div, Complex.ofReal_zero]

/-- For positive h and argument x, the compact profile is continuous at x,
including x=1. Use the clamped expression on the positive half-line and
continuity of real powers. This supplies pointwise Mellin inversion. -/
theorem continuousAt_twoPoleMellinWeight {a h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    ContinuousAt (twoPoleMellinWeight a h) x := by
  have heq :
    Set.EqOn (twoPoleMellinWeight a h) (fun t : ℝ ↦ ((t ^ a * max (1 - t ^ h) 0 / h : ℝ) : ℂ))
      (Set.Ioi 0) :=
    fun t ht ↦ twoPoleMellinWeight_eq_clamped hh ht
  refine (ContinuousOn.congr ?_ heq).continuousAt (isOpen_Ioi.mem_nhds hx)
  intro t ht
  have ha : ContinuousAt (fun u : ℝ ↦ u ^ a) t := continuousAt_id.rpow_const (Or.inl (ne_of_gt ht))
  have hb : ContinuousAt (fun u : ℝ ↦ u ^ h) t := continuousAt_id.rpow_const (Or.inl (ne_of_gt ht))
  have hf : ContinuousAt (fun u : ℝ ↦ u ^ a * max (1 - u ^ h) 0 / h) t :=
    (ha.mul ((continuousAt_const.sub hb).max continuousAt_const)).div_const h
  exact (Complex.continuous_ofReal.continuousAt.comp hf).continuousWithinAt

/-- For h>0 and a vertical line with sigma+a>0, the two-pole reciprocal
function is vertically integrable. Bound it by a positive resolvent and then
an integrable multiple of 1/(1+t^2), retaining both nonzero denominators.
This justifies inversion without assuming vertical convergence. -/
theorem verticalIntegrable_twoPoleFunction {a h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ + a) :
    Complex.VerticalIntegrable (Analysis.twoPoleFunction a (a + h)) σ := by
  have hA : 0 < (σ + a) * (σ + a + h) := mul_pos hσ (by linarith only [hσ, hh])
  have hm : 0 < min ((σ + a) * (σ + a + h)) 1 := lt_min hA zero_lt_one
  have hline : Continuous (fun t : ℝ ↦ (σ : ℂ) + (t : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hza (t : ℝ) : (σ : ℂ) + (t : ℂ) * Complex.I + a ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.zero_re] at hr
    linarith only [hσ, hr]
  have hzb (t : ℝ) : (σ : ℂ) + (t : ℂ) * Complex.I + ((a + h : ℝ) : ℂ) ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.zero_re] at hr
    linarith only [hσ, hh, hr]
  have hf :
    Continuous
      (fun t : ℝ ↦
        (1 : ℂ) /
          (((σ : ℂ) + (t : ℂ) * Complex.I + a) *
            ((σ : ℂ) + (t : ℂ) * Complex.I + ((a + h : ℝ) : ℂ)))) :=
    continuous_const.div ((hline.add_const (a : ℂ)).mul (hline.add_const ((a + h : ℝ) : ℂ)))
      (fun t ↦ mul_ne_zero (hza t) (hzb t))
  unfold Complex.VerticalIntegrable
  apply
    MeasureTheory.Integrable.mono'
      (integrable_inv_one_add_sq.const_mul (min ((σ + a) * (σ + a + h)) 1)⁻¹)
  · exact hf.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t
    have he :
      Analysis.twoPoleFunction a (a + h) ((σ : ℂ) + (t : ℂ) * Complex.I) =
        Analysis.twoPoleFunction (σ + a) (σ + a + h) (Complex.I * t) := by
      unfold Analysis.twoPoleFunction
      simp only [Complex.ofReal_add]
      congr 1
      ring
    have hk :=
      Analysis.twoPoleFunction_norm_le_resolvent (Real.sqrt_pos.mpr hA)
        (show (Real.sqrt ((σ + a) * (σ + a + h))) ^ 2 ≤ (σ + a) * (σ + a + h) by
          rw [Real.sq_sqrt hA.le])
        (t := t)
    rw [Real.sq_sqrt hA.le] at hk
    rw [he]
    have hmul := mul_le_mul_of_nonneg_right (min_le_right ((σ + a) * (σ + a + h)) 1) (sq_nonneg t)
    have hd : min ((σ + a) * (σ + a + h)) 1 * (1 + t ^ 2) ≤ (σ + a) * (σ + a + h) + t ^ 2 := by
      nlinarith only [hmul, min_le_left ((σ + a) * (σ + a + h)) 1]
    have hden : 0 < min ((σ + a) * (σ + a + h)) 1 * (1 + t ^ 2) :=
      mul_pos hm (by linarith only [sq_nonneg t])
    have hb := one_div_le_one_div_of_le hden hd
    have heq :
      1 / (min ((σ + a) * (σ + a + h)) 1 * (1 + t ^ 2)) =
        (min ((σ + a) * (σ + a + h)) 1)⁻¹ * (1 + t ^ 2)⁻¹ := by
      rw [one_div, mul_inv]
    exact hk.trans (hb.trans_eq heq)

/-- For h>0, sigma+a>0 and x>0, the inverse Mellin transform of the two-pole
function equals its compact profile. Use the forward transform, proved vertical
integrability and continuity. This is the scalar inversion used by admissible kernels. -/
theorem mellinInv_twoPoleMellinWeight {a h σ x : ℝ} (hh : 0 < h) (hσ : 0 < σ + a) (hx : 0 < x) :
    mellinInv σ (Analysis.twoPoleFunction a (a + h)) x = twoPoleMellinWeight a h x := by
  have hconv :=
    (hasMellin_twoPoleMellinWeight hh (s := (σ : ℂ)) (by simpa only [Complex.ofReal_re] using hσ)).1
  have hpoint (t : ℝ) :
    mellin (twoPoleMellinWeight a h) ((σ : ℂ) + (t : ℂ) * Complex.I) =
      Analysis.twoPoleFunction a (a + h) ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    (hasMellin_twoPoleMellinWeight hh
        (show 0 < ((σ : ℂ) + (t : ℂ) * Complex.I).re + a by
          simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hσ)).2
  have hVI : Complex.VerticalIntegrable (mellin (twoPoleMellinWeight a h)) σ := by
    have h := verticalIntegrable_twoPoleFunction hh hσ
    unfold Complex.VerticalIntegrable at h ⊢
    exact h.congr (Filter.Eventually.of_forall (fun t ↦ (hpoint t).symm))
  have hm :=
    mellinInv_mellin_eq σ (twoPoleMellinWeight a h) hx hconv hVI
      (continuousAt_twoPoleMellinWeight hh hx)
  have hfun :
    (fun t : ℝ ↦
        (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) •
          Analysis.twoPoleFunction a (a + h) ((σ : ℂ) + (t : ℂ) * Complex.I)) =
      (fun t : ℝ ↦
        (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) •
          mellin (twoPoleMellinWeight a h) ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    funext t
    rw [hpoint]
  rw [← hm]
  unfold mellinInv
  rw [hfun]

/-- For h>0 and 0<u<1, the real compact profile is strictly positive.
Factor it as u^a*(1-u^h)/h. This certifies a nonzero transform for every
positive gap when constructing an admissible Mellin kernel. -/
theorem twoPoleMellinWeight_pos {a h u : ℝ} (hh : 0 < h) (hu : 0 < u) (hu1 : u < 1) :
    0 < (twoPoleMellinWeight a h u).re := by
  have hp : 0 < 1 - u ^ h := sub_pos.mpr (Real.rpow_lt_one hu.le hu1 hh)
  rw [twoPoleMellinWeight_eq_clamped hh hu, Complex.ofReal_re, max_eq_left hp.le]
  exact div_pos (mul_pos (Real.rpow_pos_of_pos hu a) hp) hh

end PseudoPrime.AnalyticNumberTheory.General
