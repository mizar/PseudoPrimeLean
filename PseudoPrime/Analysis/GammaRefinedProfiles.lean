/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRefinedCompactIntegrals
public import PseudoPrime.Analysis.GammaLeftMoments

/-! # Two-region profiles for refined Gamma moments

Keep the curved compact envelope and use an inverse-square integrable tail.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The positive-height profile with compact function f and tail coefficient C.
Definition: f on [0,1] plus C times the inverse-square real power on (1,infinity).
Output: zero below zero, with both nonnegative regions retained separately.
Role: shared integration interface for the zeroth and first Gamma moments. -/
noncomputable def gammaRefinedProfile (f : ℝ → ℝ) (C t : ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) 1).indicator f t + (Set.Ioi (1 : ℝ)).indicator (fun u ↦ C * u ^ (-2 : ℝ)) t

/-- Input: a continuous compact function and any real tail coefficient.
Claim: the two-region profile is integrable on the whole real line.
Proof: bounded-interval continuity and inverse-square decay on the positive tail.
Role: justify linearity when computing both Gamma moments. -/
theorem gammaRefinedProfile_integrable (f : ℝ → ℝ) (C : ℝ) (hf : Continuous f) :
    MeasureTheory.Integrable (gammaRefinedProfile f C) := by
  have hc := hf.continuousOn.integrableOn_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
  have ht : MeasureTheory.IntegrableOn (fun t : ℝ ↦ C * t ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num only : (-2 : ℝ) < -1)
          (by norm_num only : (0 : ℝ) < 1)).const_mul
      C
  exact (hc.integrable_indicator measurableSet_Icc).add (ht.integrable_indicator measurableSet_Ioi)

/-- Input: a continuous compact function and any real coefficient C.
Claim: the whole profile integral is the compact interval integral plus C.
Proof: split the two indicators and integrate the inverse-square tail exactly.
Role: preserve exact compact masses in both refined moments. -/
theorem gammaRefinedProfile_integral (f : ℝ → ℝ) (C : ℝ) (hf : Continuous f) :
    (∫ t : ℝ, gammaRefinedProfile f C t) = (∫ t in (0 : ℝ)..1, f t) + C := by
  have hc := hf.continuousOn.integrableOn_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
  have ht : MeasureTheory.IntegrableOn (fun t : ℝ ↦ C * t ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num only : (-2 : ℝ) < -1)
          (by norm_num only : (0 : ℝ) < 1)).const_mul
      C
  dsimp only [gammaRefinedProfile]
  erw [MeasureTheory.integral_add (hc.integrable_indicator measurableSet_Icc)
      (ht.integrable_indicator measurableSet_Ioi),
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_indicator measurableSet_Ioi, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num only : (0 : ℝ) ≤ 1),
    MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num only) (by norm_num only)]
  norm_num only [Real.one_rpow, mul_one]

/-- The symmetric whole-line envelope formed from the positive profile and its reflection.
Input: compact function f, tail coefficient C, and arbitrary real height.
Output: the sum of the two supported profiles.
Role: integrate both signs of the Gamma height using one compact calculation. -/
noncomputable def gammaRefinedEnvelope (f : ℝ → ℝ) (C t : ℝ) : ℝ :=
  gammaRefinedProfile f C t + gammaRefinedProfile f C (-t)

/-- Input: a continuous compact function.
Claim: the reflected whole-line envelope is integrable.
Proof: add the integrable profile and its reflection.
Role: justify the actual Gamma left-integral majorant. -/
theorem gammaRefinedEnvelope_integrable (f : ℝ → ℝ) (C : ℝ) (hf : Continuous f) :
    MeasureTheory.Integrable (gammaRefinedEnvelope f C) :=
  (gammaRefinedProfile_integrable f C hf).add (gammaRefinedProfile_integrable f C hf).comp_neg

/-- Input: a continuous compact function.
Claim: the symmetric envelope integral is twice the compact mass plus the tail mass.
Proof: reflection preserves Lebesgue integration; use the exact profile integral.
Role: retain exact constants before normalizing both Gamma moments. -/
theorem gammaRefinedEnvelope_integral (f : ℝ → ℝ) (C : ℝ) (hf : Continuous f) :
    (∫ t : ℝ, gammaRefinedEnvelope f C t) = 2 * ((∫ t in (0 : ℝ)..1, f t) + C) := by
  dsimp only [gammaRefinedEnvelope]
  rw [MeasureTheory.integral_add (gammaRefinedProfile_integrable f C hf)
      (gammaRefinedProfile_integrable f C hf).comp_neg,
    MeasureTheory.integral_neg_eq_self, gammaRefinedProfile_integral f C hf]
  ring

/-- Input: nonnegative compact values on the unit interval and nonnegative tail coefficient.
Claim: the supported profile is nonnegative at every real input.
Proof: each indicator is nonnegative on its support.
Role: permit reflection to bound absolute Gamma heights. -/
theorem gammaRefinedProfile_nonneg (f : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t) (t : ℝ) : 0 ≤ gammaRefinedProfile f C t := by
  exact
    add_nonneg (Set.indicator_nonneg hf t)
      (Set.indicator_nonneg (s := Set.Ioi (1 : ℝ))
        (fun u hu ↦ mul_nonneg hC (Real.rpow_nonneg (zero_lt_one.trans (Set.mem_Ioi.mp hu)).le _))
        t)

/-- Input: nonnegative height, compact and tail bounds, and nonnegative profile components.
Claim: the supported profile bounds the given value at that height.
Proof: select the compact or tail indicator at the unit cut.
Role: connect the two actual Gamma estimates to an integrable majorant. -/
theorem le_gammaRefinedProfile (f : ℝ → ℝ) {C a g : ℝ} (hC : 0 ≤ C)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t) (ha : 0 ≤ a) (hc : a ≤ 1 → g ≤ f a)
    (ht : 1 < a → g ≤ C * a ^ (-2 : ℝ)) : g ≤ gammaRefinedProfile f C a := by
  have hc0 := Set.indicator_nonneg hf a
  have ht0 :=
    Set.indicator_nonneg (s := Set.Ioi (1 : ℝ))
      (fun u hu ↦
        mul_nonneg hC (Real.rpow_nonneg (zero_lt_one.trans (Set.mem_Ioi.mp hu)).le (-2 : ℝ)))
      a
  dsimp only [gammaRefinedProfile]
  by_cases hsmall : a ≤ 1
  · rw [Set.indicator_of_mem (show a ∈ Set.Icc (0 : ℝ) 1 from ⟨ha, hsmall⟩)]
    linarith only [hc hsmall, ht0]
  · have hlarge : 1 < a := lt_of_not_ge hsmall
    rw [Set.indicator_of_mem (show a ∈ Set.Ioi (1 : ℝ) from hlarge)]
    linarith only [ht hlarge, hc0]

/-- Claim: the zeroth symmetric envelope has its exact curved compact mass and unit tail.
Proof: specialize the two-region integral and the compact primitive.
Role: normalize the whole-line zeroth Gamma moment. -/
theorem gammaRefinedZeroEnvelope_integral :
    (∫ t : ℝ, gammaRefinedEnvelope gammaRefinedCompactZero 1 t) =
      2 * ((16 / 15 : ℝ) * Real.arsinh 16 + 1) := by
  rw [gammaRefinedEnvelope_integral gammaRefinedCompactZero 1 continuous_gammaRefinedCompactZero,
    integral_gammaRefinedCompactZero]

/-- Claim: the first symmetric envelope has exact compact mass and tail thirty-one sixteenths.
Proof: specialize the two-region integral and square-root primitive.
Role: normalize the whole-line first Gamma moment. -/
theorem gammaRefinedFirstEnvelope_integral :
    (∫ t : ℝ, gammaRefinedEnvelope (fun u ↦ u * gammaRefinedCompactZero u) (31 / 16) t) =
      2 * ((Real.sqrt 257 - 1) / 15 + 31 / 16) := by
  rw [gammaRefinedEnvelope_integral (fun u ↦ u * gammaRefinedCompactZero u) (31 / 16)
      (continuous_id.mul continuous_gammaRefinedCompactZero),
    integral_gammaRefinedCompactFirst]

/-- Claim: the compact Gamma envelope is nonnegative at every height.
Proof: divide a positive rational coefficient by a nonnegative square root.
Role: provide the supported nonnegativity hypothesis in the profile comparison. -/
theorem gammaRefinedCompactZero_nonneg (t : ℝ) : 0 ≤ gammaRefinedCompactZero t := by
  exact div_nonneg (by norm_num only : (0 : ℝ) ≤ 256 / 15) (Real.sqrt_nonneg _)

/-- Claim: the compact envelope depends only on the absolute height.
Proof: its denominator depends on the square of the height.
Role: select a positive profile without changing the actual Gamma compact bound. -/
theorem gammaRefinedCompactZero_abs (t : ℝ) :
    gammaRefinedCompactZero |t| = gammaRefinedCompactZero t := by
  simp only [gammaRefinedCompactZero, mul_pow, sq_abs]

/-- Input: real part minus one sixteenth.
Claim: the combined compact and inverse-square profile bounds the actual Gamma norm.
Proof: split at unit absolute height and apply the certified compact and tail estimates.
Role: whole-line Gamma majorant whose exact integral is available. -/
theorem norm_Gamma_le_gammaRefinedZeroProfile {s : ℂ} (hs : s.re = -1 / 16) :
    ‖Complex.Gamma s‖ ≤ gammaRefinedProfile gammaRefinedCompactZero 1 |s.im| := by
  apply
    le_gammaRefinedProfile gammaRefinedCompactZero zero_le_one
      (fun t _ ↦ gammaRefinedCompactZero_nonneg t) (abs_nonneg s.im)
  · intro _
    exact
      (norm_Gamma_le_gammaRefinedCompactZero hs).trans_eq (gammaRefinedCompactZero_abs s.im).symm
  · intro ha
    have hb := norm_Gamma_neg_one_sixteenth_le_inv_sq hs (abs_pos.mp (zero_lt_one.trans ha))
    simpa only [Real.rpow_neg (abs_nonneg s.im), Real.rpow_two, sq_abs, one_mul, one_div] using hb

/-- Input: real part minus one sixteenth.
Claim: the combined first profile bounds the actual height-weighted Gamma norm.
Proof: use the curved compact estimate and the refined inverse-square weighted tail.
Role: connect the first moment integral to the actual left-line integrand. -/
theorem norm_Gamma_mul_height_le_gammaRefinedFirstProfile {s : ℂ} (hs : s.re = -1 / 16) :
    ‖Complex.Gamma s‖ * |s.im| ≤
      gammaRefinedProfile (fun u ↦ u * gammaRefinedCompactZero u) (31 / 16) |s.im| := by
  apply
    le_gammaRefinedProfile (fun u ↦ u * gammaRefinedCompactZero u)
      (by norm_num only : (0 : ℝ) ≤ 31 / 16)
      (fun u hu ↦ mul_nonneg hu.1 (gammaRefinedCompactZero_nonneg u)) (abs_nonneg s.im)
  · intro _
    have h :=
      mul_le_mul_of_nonneg_right (norm_Gamma_le_gammaRefinedCompactZero hs) (abs_nonneg s.im)
    simpa only [gammaRefinedCompactZero_abs, mul_comm] using h
  · intro ha
    have hb :=
      norm_Gamma_neg_one_sixteenth_mul_height_le_refined_tail hs (abs_pos.mp (zero_lt_one.trans ha))
    simpa only [Real.rpow_neg (abs_nonneg s.im), Real.rpow_two, sq_abs, div_eq_mul_inv] using hb

/-- Input: real part minus one sixteenth.
Claim: the actual Gamma norm is bounded by the integrable symmetric envelope.
Proof: combine the positive-height profile bound and nonnegative reflection.
Role: majorant for the zeroth whole-line Gamma moment. -/
theorem norm_Gamma_le_gammaRefinedZeroEnvelope {s : ℂ} (hs : s.re = -1 / 16) :
    ‖Complex.Gamma s‖ ≤ gammaRefinedEnvelope gammaRefinedCompactZero 1 s.im := by
  exact
    (norm_Gamma_le_gammaRefinedZeroProfile hs).trans
      (profile_abs_le_symmetric
        (gammaRefinedProfile_nonneg gammaRefinedCompactZero zero_le_one
          (fun u _ ↦ gammaRefinedCompactZero_nonneg u))
        s.im)

/-- Input: real part minus one sixteenth.
Claim: the height-weighted Gamma norm is bounded by the symmetric first envelope.
Proof: combine the actual first-profile bound with nonnegative reflection.
Role: majorant for the first whole-line Gamma moment. -/
theorem norm_Gamma_mul_height_le_gammaRefinedFirstEnvelope {s : ℂ} (hs : s.re = -1 / 16) :
    ‖Complex.Gamma s‖ * |s.im| ≤
      gammaRefinedEnvelope (fun u ↦ u * gammaRefinedCompactZero u) (31 / 16) s.im := by
  exact
    (norm_Gamma_mul_height_le_gammaRefinedFirstProfile hs).trans
      (profile_abs_le_symmetric
        (gammaRefinedProfile_nonneg (fun u ↦ u * gammaRefinedCompactZero u)
          (by norm_num only : (0 : ℝ) ≤ 31 / 16)
          (fun u hu ↦ mul_nonneg hu.1 (gammaRefinedCompactZero_nonneg u)))
        s.im)

/-- The refined symmetric zeroth envelope with unit inverse-square tail.
Input: any real height. Output: the common majorant for the Gamma norm.
Role: keep left-integral formulas short while retaining the exact two-region profile. -/
noncomputable def gammaRefinedZeroEnvelope (t : ℝ) : ℝ :=
  gammaRefinedEnvelope gammaRefinedCompactZero 1 t

/-- The refined symmetric first envelope with tail coefficient thirty-one sixteenths.
Input: any real height. Output: the majorant for the height-weighted Gamma norm.
Role: supply the first moment in the refined left-integral estimate. -/
noncomputable def gammaRefinedFirstEnvelope (t : ℝ) : ℝ :=
  gammaRefinedEnvelope (fun u ↦ u * gammaRefinedCompactZero u) (31 / 16) t

/-- Claim: the refined zeroth envelope is integrable.
Proof: specialize the symmetric two-region integrability theorem.
Role: justify integrating the zeroth term of the left-line majorant. -/
theorem gammaRefinedZeroEnvelope_integrable : MeasureTheory.Integrable gammaRefinedZeroEnvelope :=
  gammaRefinedEnvelope_integrable gammaRefinedCompactZero 1 continuous_gammaRefinedCompactZero

/-- Claim: the refined first envelope is integrable.
Proof: specialize symmetric profile integrability to the continuous height-weighted function.
Role: justify the first term of the left-line majorant. -/
theorem gammaRefinedFirstEnvelope_integrable : MeasureTheory.Integrable gammaRefinedFirstEnvelope :=
  gammaRefinedEnvelope_integrable (fun u ↦ u * gammaRefinedCompactZero u) (31 / 16)
    (continuous_id.mul continuous_gammaRefinedCompactZero)

end PseudoPrime.Analysis
