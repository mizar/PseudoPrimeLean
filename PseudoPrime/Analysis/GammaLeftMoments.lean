/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaVerticalNumericalBounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! # Three-region Gamma moment majorants

Integrable symmetric envelopes retain the compact, inverse and power-tail bounds.
Their normalized masses are at most 16/5 and 5/3 for the left completed integral.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The positive half-line Gamma envelope uses 32, 2/t and 6/t⁴ on three regions.
The cut points are 1/16 and 1; outside the positive half-line it is zero.
Its exact integral controls the zeroth left-line moment. -/
noncomputable def gammaLeftZeroProfile (t : ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) (1 / 16)).indicator (fun _ ↦ (32 : ℝ)) t +
    (Set.Ioc (1 / 16 : ℝ) 1).indicator (fun u ↦ 2 * u⁻¹) t +
    (Set.Ioi (1 : ℝ)).indicator (fun u ↦ 6 * u ^ (-4 : ℝ)) t

/-- The zeroth profile is integrable. Use continuity on the two bounded regions
and fourth-power decay on the tail to justify its exact integral. -/
theorem gammaLeftZeroProfile_integrable : MeasureTheory.Integrable gammaLeftZeroProfile := by
  have hc :=
    (continuous_const : Continuous (fun _ : ℝ ↦ (32 : ℝ))).continuousOn |>.integrableOn_Icc (μ :=
      MeasureTheory.volume) (a := 0) (b := 1 / 16)
  have hm : MeasureTheory.IntegrableOn (fun u : ℝ ↦ 2 * u⁻¹) (Set.Ioc (1 / 16 : ℝ) 1) := by
    apply
      ContinuousOn.integrableOn_Icc ((continuous_id.continuousOn.inv₀ ?_).const_mul 2) |>.mono_set
        Set.Ioc_subset_Icc_self
    intro u hu
    exact (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 16) hu.1).ne'
  have ht : MeasureTheory.IntegrableOn (fun u : ℝ ↦ 6 * u ^ (-4 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num only : (-4 : ℝ) < -1)
          (by norm_num only : (0 : ℝ) < 1)).const_mul
      6
  exact
    ((hc.integrable_indicator measurableSet_Icc).add
          (hm.integrable_indicator measurableSet_Ioc)).add
      (ht.integrable_indicator measurableSet_Ioi)

/-- The zeroth profile has integral 4+2log(16). Integrate its three indicator
terms separately with the constant, inverse and tail-power formulas. -/
theorem gammaLeftZeroProfile_integral :
    (∫ t : ℝ, gammaLeftZeroProfile t) = 4 + 2 * Real.log 16 := by
  have hc :=
    (continuous_const : Continuous (fun _ : ℝ ↦ (32 : ℝ))).continuousOn |>.integrableOn_Icc (μ :=
      MeasureTheory.volume) (a := 0) (b := 1 / 16)
  have hm : MeasureTheory.IntegrableOn (fun u : ℝ ↦ 2 * u⁻¹) (Set.Ioc (1 / 16 : ℝ) 1) := by
    apply
      ContinuousOn.integrableOn_Icc ((continuous_id.continuousOn.inv₀ ?_).const_mul 2) |>.mono_set
        Set.Ioc_subset_Icc_self
    intro u hu
    exact (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 16) hu.1).ne'
  have ht : MeasureTheory.IntegrableOn (fun u : ℝ ↦ 6 * u ^ (-4 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num only : (-4 : ℝ) < -1)
          (by norm_num only : (0 : ℝ) < 1)).const_mul
      6
  dsimp only [gammaLeftZeroProfile]
  change
    (∫ t : ℝ,
        (((Set.Icc (0 : ℝ) (1 / 16)).indicator (fun _ ↦ (32 : ℝ)) +
              (Set.Ioc (1 / 16 : ℝ) 1).indicator (fun u ↦ 2 * u⁻¹)) +
            (Set.Ioi (1 : ℝ)).indicator (fun u ↦ 6 * u ^ (-4 : ℝ)))
          t) =
      _
  erw [MeasureTheory.integral_add
      ((hc.integrable_indicator measurableSet_Icc).add (hm.integrable_indicator measurableSet_Ioc))
      (ht.integrable_indicator measurableSet_Ioi),
    MeasureTheory.integral_add (hc.integrable_indicator measurableSet_Icc)
      (hm.integrable_indicator measurableSet_Ioc),
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.integral_indicator measurableSet_Ioi, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num only : (0 : ℝ) ≤ 1 / 16), ←
    intervalIntegral.integral_of_le (by norm_num only : (1 / 16 : ℝ) ≤ 1),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_inv_of_pos (by norm_num only) (by norm_num only), MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num only) (by norm_num only)]
  norm_num only [Real.one_rpow, smul_eq_mul]
  ring

/-- The positive half-line height envelope uses 32t, 2 and 6/t³ on three regions.
The cut points are 1/16 and 1; its exact integral controls the first moment. -/
noncomputable def gammaLeftFirstProfile (t : ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) (1 / 16)).indicator (fun u ↦ (32 : ℝ) * u) t +
    (Set.Ioc (1 / 16 : ℝ) 1).indicator (fun _ ↦ (2 : ℝ)) t +
    (Set.Ioi (1 : ℝ)).indicator (fun u ↦ 6 * u ^ (-3 : ℝ)) t

/-- The first profile is integrable. Use continuity on bounded regions and
third-power decay on the tail to justify the first-moment estimate. -/
theorem gammaLeftFirstProfile_integrable : MeasureTheory.Integrable gammaLeftFirstProfile := by
  have hc :=
    (continuous_const.mul continuous_id :
          Continuous (fun u : ℝ ↦ (32 : ℝ) * u)).continuousOn |>.integrableOn_Icc
      (μ := MeasureTheory.volume) (a := 0) (b := 1 / 16)
  have hm : MeasureTheory.IntegrableOn (fun _ : ℝ ↦ (2 : ℝ)) (Set.Ioc (1 / 16 : ℝ) 1) :=
    ((continuous_const : Continuous (fun _ : ℝ ↦ (2 : ℝ))).continuousOn.integrableOn_Icc (μ :=
          MeasureTheory.volume)).mono_set
      Set.Ioc_subset_Icc_self
  have ht : MeasureTheory.IntegrableOn (fun u : ℝ ↦ 6 * u ^ (-3 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num only : (-3 : ℝ) < -1)
          (by norm_num only : (0 : ℝ) < 1)).const_mul
      6
  exact
    ((hc.integrable_indicator measurableSet_Icc).add
          (hm.integrable_indicator measurableSet_Ioc)).add
      (ht.integrable_indicator measurableSet_Ioi)

/-- The first profile has integral 79/16. Integrate its compact linear term,
constant middle term and third-power tail to supply the first moment. -/
theorem gammaLeftFirstProfile_integral : (∫ t : ℝ, gammaLeftFirstProfile t) = 79 / 16 := by
  have hc :=
    (continuous_const.mul continuous_id :
          Continuous (fun u : ℝ ↦ (32 : ℝ) * u)).continuousOn |>.integrableOn_Icc
      (μ := MeasureTheory.volume) (a := 0) (b := 1 / 16)
  have hm : MeasureTheory.IntegrableOn (fun _ : ℝ ↦ (2 : ℝ)) (Set.Ioc (1 / 16 : ℝ) 1) :=
    ((continuous_const : Continuous (fun _ : ℝ ↦ (2 : ℝ))).continuousOn.integrableOn_Icc (μ :=
          MeasureTheory.volume)).mono_set
      Set.Ioc_subset_Icc_self
  have ht : MeasureTheory.IntegrableOn (fun u : ℝ ↦ 6 * u ^ (-3 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num only : (-3 : ℝ) < -1)
          (by norm_num only : (0 : ℝ) < 1)).const_mul
      6
  dsimp only [gammaLeftFirstProfile]
  erw [MeasureTheory.integral_add
      ((hc.integrable_indicator measurableSet_Icc).add (hm.integrable_indicator measurableSet_Ioc))
      (ht.integrable_indicator measurableSet_Ioi),
    MeasureTheory.integral_add (hc.integrable_indicator measurableSet_Icc)
      (hm.integrable_indicator measurableSet_Ioc),
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.integral_indicator measurableSet_Ioi, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num only : (0 : ℝ) ≤ 1 / 16), ←
    intervalIntegral.integral_of_le (by norm_num only : (1 / 16 : ℝ) ≤ 1),
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
    MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num only) (by norm_num only)]
  norm_num only [Real.one_rpow, smul_eq_mul]

/-- The zeroth profile is nonnegative at every height. Each indicator is
nonnegative on its support; this permits symmetrization of the majorant. -/
theorem gammaLeftZeroProfile_nonneg (t : ℝ) : 0 ≤ gammaLeftZeroProfile t := by
  have hc :=
    Set.indicator_nonneg (fun _ _ ↦ (by norm_num only : (0 : ℝ) ≤ 32)) t (s := Set.Icc 0 (1 / 16))
  have hm :=
    Set.indicator_nonneg (s := Set.Ioc (1 / 16 : ℝ) 1)
      (fun u hu ↦
        mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
          (inv_nonneg.mpr (by linarith only [hu.1] : 0 ≤ u)))
      t
  have ht :=
    Set.indicator_nonneg (s := Set.Ioi (1 : ℝ))
      (fun u hu ↦
        mul_nonneg (by norm_num only : (0 : ℝ) ≤ 6)
          (Real.rpow_nonneg (by linarith only [Set.mem_Ioi.mp hu] : 0 ≤ u) (-4 : ℝ)))
      t
  exact add_nonneg (add_nonneg hc hm) ht

/-- The first profile is nonnegative at every height. Each supported term is
nonnegative, so adding its reflected copy preserves upper bounds. -/
theorem gammaLeftFirstProfile_nonneg (t : ℝ) : 0 ≤ gammaLeftFirstProfile t := by
  have hc :=
    Set.indicator_nonneg (s := Set.Icc (0 : ℝ) (1 / 16))
      (fun u hu ↦ mul_nonneg (by norm_num only : (0 : ℝ) ≤ 32) hu.1) t
  have hm :=
    Set.indicator_nonneg (fun _ _ ↦ (by norm_num only : (0 : ℝ) ≤ 2)) t (s := Set.Ioc (1 / 16) 1)
  have ht :=
    Set.indicator_nonneg (s := Set.Ioi (1 : ℝ))
      (fun u hu ↦
        mul_nonneg (by norm_num only : (0 : ℝ) ≤ 6)
          (Real.rpow_nonneg (by linarith only [Set.mem_Ioi.mp hu] : 0 ≤ u) (-3 : ℝ)))
      t
  exact add_nonneg (add_nonneg hc hm) ht

/-- At nonnegative height, the compact, inverse and fourth-power bounds imply
the zeroth profile bound. Split at 1/16 and 1 to select the applicable term. -/
theorem le_gammaLeftZeroProfile {a g : ℝ} (ha : 0 ≤ a) (hc : g ≤ 32) (hm : 0 < a → g ≤ 2 * a⁻¹)
    (ht : 1 < a → g ≤ 6 * a ^ (-4 : ℝ)) : g ≤ gammaLeftZeroProfile a := by
  have hc0 :=
    Set.indicator_nonneg (fun _ _ ↦ (by norm_num only : (0 : ℝ) ≤ 32)) a (s := Set.Icc 0 (1 / 16))
  have hm0 :=
    Set.indicator_nonneg (s := Set.Ioc (1 / 16 : ℝ) 1)
      (fun u hu ↦
        mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
          (inv_nonneg.mpr (by linarith only [hu.1] : 0 ≤ u)))
      a
  have ht0 :=
    Set.indicator_nonneg (s := Set.Ioi (1 : ℝ))
      (fun u hu ↦
        mul_nonneg (by norm_num only : (0 : ℝ) ≤ 6)
          (Real.rpow_nonneg (by linarith only [Set.mem_Ioi.mp hu] : 0 ≤ u) (-4 : ℝ)))
      a
  dsimp only [gammaLeftZeroProfile]
  by_cases hsmall : a ≤ 1 / 16
  · rw [Set.indicator_of_mem (show a ∈ Set.Icc 0 (1 / 16) from ⟨ha, hsmall⟩)]
    linarith only [hc, hm0, ht0]
  · have hap : 0 < a := by linarith only [lt_of_not_ge hsmall]
    by_cases hmiddle : a ≤ 1
    · rw [Set.indicator_of_mem (show a ∈ Set.Ioc (1 / 16) 1 from ⟨lt_of_not_ge hsmall, hmiddle⟩)]
      linarith only [hm hap, hc0, ht0]
    · have hlarge : 1 < a := lt_of_not_ge hmiddle
      rw [Set.indicator_of_mem (show a ∈ Set.Ioi 1 from hlarge)]
      linarith only [ht hlarge, hc0, hm0]

/-- For a nonnegative profile, its value at |t| is bounded by f(t)+f(-t).
Split by the sign of t; this converts half-line bounds into integrable majorants. -/
theorem profile_abs_le_symmetric {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) (t : ℝ) :
    f |t| ≤ f t + f (-t) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    exact le_add_of_nonneg_right (hf (-t))
  · rw [abs_of_nonpos (lt_of_not_ge ht).le]
    exact le_add_of_nonneg_left (hf t)

/-- At nonnegative height, the linear, constant and third-power bounds imply
the first profile bound. The same region split controls the weighted Gamma norm. -/
theorem le_gammaLeftFirstProfile {a g : ℝ} (ha : 0 ≤ a) (hc : g ≤ 32 * a) (hm : 0 < a → g ≤ 2)
    (ht : 1 < a → g ≤ 6 * a ^ (-3 : ℝ)) : g ≤ gammaLeftFirstProfile a := by
  have hc0 :=
    Set.indicator_nonneg (s := Set.Icc (0 : ℝ) (1 / 16))
      (fun u hu ↦ mul_nonneg (by norm_num only : (0 : ℝ) ≤ 32) hu.1) a
  have hm0 :=
    Set.indicator_nonneg (s := Set.Ioc (1 / 16 : ℝ) 1) (fun _ _ ↦ (by norm_num only : (0 : ℝ) ≤ 2))
      a
  have ht0 :=
    Set.indicator_nonneg (s := Set.Ioi (1 : ℝ))
      (fun u hu ↦
        mul_nonneg (by norm_num only : (0 : ℝ) ≤ 6)
          (Real.rpow_nonneg (by linarith only [Set.mem_Ioi.mp hu] : 0 ≤ u) (-3 : ℝ)))
      a
  dsimp only [gammaLeftFirstProfile]
  by_cases hsmall : a ≤ 1 / 16
  · rw [Set.indicator_of_mem (show a ∈ Set.Icc 0 (1 / 16) from ⟨ha, hsmall⟩)]
    linarith only [hc, hm0, ht0]
  · have hap : 0 < a := by linarith only [lt_of_not_ge hsmall]
    by_cases hmiddle : a ≤ 1
    · rw [Set.indicator_of_mem (show a ∈ Set.Ioc (1 / 16) 1 from ⟨lt_of_not_ge hsmall, hmiddle⟩)]
      linarith only [hm hap, hc0, ht0]
    · have hlarge : 1 < a := lt_of_not_ge hmiddle
      rw [Set.indicator_of_mem (show a ∈ Set.Ioi 1 from hlarge)]
      linarith only [ht hlarge, hc0, hm0]

/-- On Re s=-1/16 and nonzero height, the Gamma norm is bounded by 6|Im s|⁻⁴.
Rewrite the existing fourth-power bound as a real power for tail integration. -/
theorem norm_Gamma_neg_one_sixteenth_le_rpow_tail {s : ℂ} (hs : s.re = -1 / 16) (hi : s.im ≠ 0) :
    ‖Complex.Gamma s‖ ≤ 6 * |s.im| ^ (-4 : ℝ) := by
  have h := norm_Gamma_neg_one_sixteenth_le_fourth hs hi
  have he : (-4 : ℝ) = -((4 : ℕ) : ℝ) := by norm_num only
  have h4 : 0 ≤ s.im ^ 4 := by nlinarith only [sq_nonneg (s.im ^ 2)]
  rw [he, Real.rpow_neg (abs_nonneg s.im), Real.rpow_natCast, pow_abs, abs_of_nonneg h4]
  exact h.trans_eq (div_eq_mul_inv 6 (s.im ^ 4))

/-- On Re s=-1/16, the Gamma norm is bounded by the zeroth profile at |Im s|.
Combine the compact, inverse and tail estimates to obtain a moment majorant. -/
theorem norm_Gamma_neg_one_sixteenth_le_zeroProfile {s : ℂ} (hs : s.re = -1 / 16) :
    ‖Complex.Gamma s‖ ≤ gammaLeftZeroProfile |s.im| := by
  apply le_gammaLeftZeroProfile (abs_nonneg s.im) (norm_Gamma_neg_one_sixteenth_le_thirty_two hs)
  · intro ha
    exact
      (norm_Gamma_neg_one_sixteenth_le_inverse hs (abs_pos.mp ha)).trans_eq
        (div_eq_mul_inv 2 |s.im|)
  · intro ha
    exact norm_Gamma_neg_one_sixteenth_le_rpow_tail hs (abs_pos.mp (zero_lt_one.trans ha))

/-- Multiplying positive a by a⁻⁴ gives a⁻³. Real-power addition proves the
identity used to convert Gamma tail decay into a first-moment envelope. -/
theorem abs_mul_rpow_neg_four {a : ℝ} (ha : 0 < a) : a * a ^ (-4 : ℝ) = a ^ (-3 : ℝ) := by
  nth_rw 1 [← Real.rpow_one a]
  rw [← Real.rpow_add ha]
  norm_num only

/-- On Re s=-1/16, |Im s| times the Gamma norm is bounded by the first profile.
Multiply each of the three Gamma bounds by the nonnegative height. -/
theorem norm_Gamma_neg_one_sixteenth_mul_height_le_firstProfile {s : ℂ} (hs : s.re = -1 / 16) :
    |s.im| * ‖Complex.Gamma s‖ ≤ gammaLeftFirstProfile |s.im| := by
  apply le_gammaLeftFirstProfile (abs_nonneg s.im)
  · have h :=
      mul_le_mul_of_nonneg_left (norm_Gamma_neg_one_sixteenth_le_thirty_two hs) (abs_nonneg s.im)
    linarith only [h]
  · intro ha
    have h :=
      mul_le_mul_of_nonneg_left (norm_Gamma_neg_one_sixteenth_le_inverse hs (abs_pos.mp ha)) ha.le
    rw [mul_div_cancel₀ 2 ha.ne'] at h
    exact h
  · intro ha
    have hap := zero_lt_one.trans ha
    have h :=
      mul_le_mul_of_nonneg_left (norm_Gamma_neg_one_sixteenth_le_rpow_tail hs (abs_pos.mp hap))
        hap.le
    calc
      _ ≤ |s.im| * (6 * |s.im| ^ (-4 : ℝ)) := h
      _ = 6 * (|s.im| * |s.im| ^ (-4 : ℝ)) := by ring
      _ = _ := by rw [abs_mul_rpow_neg_four hap]

/-- The whole-line zeroth envelope is the sum of the profile and its reflection.
Both summands are integrable; it bounds the Gamma norm at every height. -/
noncomputable def gammaLeftZeroEnvelope (t : ℝ) : ℝ :=
  gammaLeftZeroProfile t + gammaLeftZeroProfile (-t)

/-- The whole-line first envelope is the profile plus its reflection.
Its integral bounds the absolute-height Gamma moment on the left line. -/
noncomputable def gammaLeftFirstEnvelope (t : ℝ) : ℝ :=
  gammaLeftFirstProfile t + gammaLeftFirstProfile (-t)

/-- The whole-line zeroth envelope is integrable. Reflection preserves
integrability, and addition combines the two half-line profiles. -/
theorem gammaLeftZeroEnvelope_integrable : MeasureTheory.Integrable gammaLeftZeroEnvelope :=
  gammaLeftZeroProfile_integrable.add gammaLeftZeroProfile_integrable.comp_neg

/-- The whole-line first envelope is integrable. Reflect and add the
integrable first profile to control weighted left-line integrands. -/
theorem gammaLeftFirstEnvelope_integrable : MeasureTheory.Integrable gammaLeftFirstEnvelope :=
  gammaLeftFirstProfile_integrable.add gammaLeftFirstProfile_integrable.comp_neg

/-- The whole-line zeroth envelope has integral 8+4log(16). Reflection keeps
the profile integral unchanged, so the whole-line mass is twice that integral. -/
theorem gammaLeftZeroEnvelope_integral :
    (∫ t : ℝ, gammaLeftZeroEnvelope t) = 8 + 4 * Real.log 16 := by
  dsimp only [gammaLeftZeroEnvelope]
  rw [MeasureTheory.integral_add gammaLeftZeroProfile_integrable
      gammaLeftZeroProfile_integrable.comp_neg,
    MeasureTheory.integral_neg_eq_self, gammaLeftZeroProfile_integral]
  ring

/-- The whole-line first envelope has integral 79/8. Add the equal reflected
profile integrals to obtain the exact first-moment mass. -/
theorem gammaLeftFirstEnvelope_integral : (∫ t : ℝ, gammaLeftFirstEnvelope t) = 79 / 8 := by
  dsimp only [gammaLeftFirstEnvelope]
  rw [MeasureTheory.integral_add gammaLeftFirstProfile_integrable
      gammaLeftFirstProfile_integrable.comp_neg,
    MeasureTheory.integral_neg_eq_self, gammaLeftFirstProfile_integral]
  norm_num only

/-- The zeroth envelope integral divided by 2π is at most 16/5.
Use log(16)=4log(2), log(2)<0.7 and π>3 for the explicit comparison. -/
theorem gammaLeftZeroEnvelope_normalized_le :
    (1 / (2 * Real.pi)) * (∫ t : ℝ, gammaLeftZeroEnvelope t) ≤ 16 / 5 := by
  have hlog : Real.log 16 < 14 / 5 := by
    have h := Real.log_pow 2 4
    norm_num only at h
    rw [h]
    linarith only [Real.log_two_lt_d9]
  rw [gammaLeftZeroEnvelope_integral, one_div, mul_comm, ← div_eq_mul_inv,
    div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos)]
  nlinarith only [hlog, Real.pi_gt_three]

/-- The first envelope integral divided by 2π is at most 5/3.
Its exact mass 79/8 and π>3 prove the numerical first-moment bound. -/
theorem gammaLeftFirstEnvelope_normalized_le :
    (1 / (2 * Real.pi)) * (∫ t : ℝ, gammaLeftFirstEnvelope t) ≤ 5 / 3 := by
  rw [gammaLeftFirstEnvelope_integral, one_div, mul_comm, ← div_eq_mul_inv,
    div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos)]
  nlinarith only [Real.pi_gt_three]

/-- On Re s=-1/16, the Gamma norm is bounded by the whole-line zeroth envelope.
Combine the half-line bound and nonnegative symmetrization for integral estimates. -/
theorem norm_Gamma_neg_one_sixteenth_le_zeroEnvelope {s : ℂ} (hs : s.re = -1 / 16) :
    ‖Complex.Gamma s‖ ≤ gammaLeftZeroEnvelope s.im :=
  (norm_Gamma_neg_one_sixteenth_le_zeroProfile hs).trans
    (profile_abs_le_symmetric gammaLeftZeroProfile_nonneg s.im)

/-- On Re s=-1/16, the height-weighted Gamma norm is bounded by the first envelope.
Symmetrize the first profile to obtain the whole-line weighted majorant. -/
theorem norm_Gamma_neg_one_sixteenth_mul_height_le_firstEnvelope {s : ℂ} (hs : s.re = -1 / 16) :
    |s.im| * ‖Complex.Gamma s‖ ≤ gammaLeftFirstEnvelope s.im :=
  (norm_Gamma_neg_one_sixteenth_mul_height_le_firstProfile hs).trans
    (profile_abs_le_symmetric gammaLeftFirstProfile_nonneg s.im)

end PseudoPrime.Analysis
