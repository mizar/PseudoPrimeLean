/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinWeights
public import PseudoPrime.Analysis.TwoPoleResolventBounds

/-! # Nonnegative compact Mellin profiles with an adjustable pole gap -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The normalized difference of powers u^a and u^(a+h), supported on (0,1].
Inputs are real parameters a,h and a real argument. Its Mellin transform has
poles at -a and -(a+h). Positive h gives a nonnegative real compact profile. -/
noncomputable def twoPoleMellinWeight (a h : ℝ) (u : ℝ) : ℂ :=
  (h : ℂ)⁻¹ *
    (Set.indicator (Set.Ioc (0 : ℝ) 1) (fun t ↦ (t : ℂ) ^ (a : ℂ)) u -
      Set.indicator (Set.Ioc (0 : ℝ) 1) (fun t ↦ (t : ℂ) ^ ((a + h : ℝ) : ℂ)) u)

/-- If h>0 and Re(s)+a>0, the compact profile is Mellin convergent and its
transform is the two-pole reciprocal function. Subtract the two power-indicator
transforms and normalize. This supplies the forward-transform input for inversion. -/
theorem hasMellin_twoPoleMellinWeight {a h : ℝ} (hh : 0 < h) {s : ℂ} (hs : 0 < s.re + a) :
    HasMellin (twoPoleMellinWeight a h) s (Analysis.twoPoleFunction a (a + h) s) := by
  have h1 :=
    hasMellin_cpow_Ioc (a : ℂ)
      (show 0 < s.re + (a : ℂ).re by simpa only [Complex.ofReal_re] using hs)
  have h2 :=
    hasMellin_cpow_Ioc ((a + h : ℝ) : ℂ)
      (show 0 < s.re + ((a + h : ℝ) : ℂ).re
        by
        simp only [Complex.ofReal_re]
        linarith only [hs, hh])
  have hd := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2] at hd
  have hm := hasMellin_const_smul hd.1 ((h : ℂ)⁻¹)
  rw [hd.2] at hm
  have ha0 : s + (a : ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hr
    linarith only [hs, hr]
  have hb0 : s + ((a + h : ℝ) : ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hr
    linarith only [hs, hh, hr]
  have he :
    (h : ℂ)⁻¹ * (1 / (s + (a : ℂ)) - 1 / (s + ((a + h : ℝ) : ℂ))) =
      Analysis.twoPoleFunction a (a + h) s := by
    unfold Analysis.twoPoleFunction
    field_simp [ha0, hb0, Complex.ofReal_ne_zero.mpr hh.ne']
    simp only [Complex.ofReal_add]
    ring
  unfold twoPoleMellinWeight
  simpa only [smul_eq_mul, he] using hm

/-- On (0,1], the compact complex profile is the real power difference
(u^a-u^(a+h))/h. Rewrite positive-real complex powers.
This is the explicit arithmetic weight used to check positivity. -/
theorem twoPoleMellinWeight_on_support {a h u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    twoPoleMellinWeight a h u = (((u ^ a - u ^ (a + h)) / h : ℝ) : ℂ) := by
  unfold twoPoleMellinWeight
  rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, ← Complex.ofReal_cpow hu.1.le a, ←
    Complex.ofReal_cpow hu.1.le (a + h)]
  rw [Complex.ofReal_div, Complex.ofReal_sub]
  rw [div_eq_mul_inv]
  ring

/-- Outside (0,1], the compact profile is zero for all parameters.
Both indicators vanish. This provides exact support without a tail estimate. -/
theorem twoPoleMellinWeight_off_support {a h u : ℝ} (hu : u ∉ Set.Ioc (0 : ℝ) 1) :
    twoPoleMellinWeight a h u = 0 := by
  rw [twoPoleMellinWeight, Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, sub_self,
    mul_zero]

/-- For positive gap h and arbitrary a,u, the profile has nonnegative real part.
On its support factor out u^a and use u^h<=1; outside it is zero.
This is the positivity requirement for finite-scale test weights. -/
theorem twoPoleMellinWeight_nonneg {a h u : ℝ} (hh : 0 < h) :
    0 ≤ (twoPoleMellinWeight a h u).re := by
  by_cases hu : u ∈ Set.Ioc (0 : ℝ) 1
  · rw [twoPoleMellinWeight_on_support hu, Complex.ofReal_re, Real.rpow_add hu.1]
    have he : u ^ a - u ^ a * u ^ h = u ^ a * (1 - u ^ h) := by ring
    rw [he]
    exact
      div_nonneg
        (mul_nonneg (Real.rpow_nonneg hu.1.le a)
          (sub_nonneg.mpr (Real.rpow_le_one hu.1.le hu.2 hh.le)))
        hh.le
  · rw [twoPoleMellinWeight_off_support hu, Complex.zero_re]

/-- For arbitrary real parameters and argument, the profile is real-valued.
Use its real formula on the support and zero elsewhere.
This separates positivity from the Mellin integration hypotheses. -/
theorem twoPoleMellinWeight_real (a h u : ℝ) : (twoPoleMellinWeight a h u).im = 0 := by
  by_cases hu : u ∈ Set.Ioc (0 : ℝ) 1
  · rw [twoPoleMellinWeight_on_support hu, Complex.ofReal_im]
  · rw [twoPoleMellinWeight_off_support hu, Complex.zero_im]

end PseudoPrime.AnalyticNumberTheory.General
