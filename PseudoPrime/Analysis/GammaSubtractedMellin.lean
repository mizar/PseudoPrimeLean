/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaMellin
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The subtracted exponential density on the negative Gamma strip

Subtracting the origin residue gives exp(-u)-1. Its Mellin integral converges on
-1 < Re s < 0 and identifies the negative-strip Gamma transform.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The subtracted exponential density exp(-u)-1, embedded in the complex numbers.
It vanishes at zero and remains bounded on the positive half-line, so its Mellin strip
lies between minus one and zero. It supplies the negative-line conductor correction. -/
noncomputable def gammaSubtractedDensity (u : ℝ) : ℂ :=
  (Real.exp (-u) - 1 : ℝ)

/-- On nonnegative arguments the density norm is one minus exp(-u).
Keep the negative sign of the real density before taking its norm. -/
theorem norm_gammaSubtractedDensity {u : ℝ} (hu : 0 ≤ u) :
    ‖gammaSubtractedDensity u‖ = 1 - Real.exp (-u) := by
  dsimp only [gammaSubtractedDensity]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
  · ring
  · exact sub_nonpos.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu))

/-- The subtracted density norm is at most u for u ≥ 0. The tangent inequality for
the exponential provides the linear vanishing needed at the Mellin origin. -/
theorem norm_gammaSubtractedDensity_le_self {u : ℝ} (hu : 0 ≤ u) :
    ‖gammaSubtractedDensity u‖ ≤ u := by
  rw [norm_gammaSubtractedDensity hu]
  have h := Real.add_one_le_exp (-u)
  linarith only [h]

/-- The subtracted density norm is at most one on the positive half-line.
This supplies its constant majorant at infinity. -/
theorem norm_gammaSubtractedDensity_le_one {u : ℝ} (hu : 0 ≤ u) :
    ‖gammaSubtractedDensity u‖ ≤ 1 := by
  rw [norm_gammaSubtractedDensity hu]
  linarith only [Real.exp_pos (-u)]

/-- The subtracted density is continuous on the real line.
The real exponential and real inclusion give its local integrability. -/
theorem continuous_gammaSubtractedDensity : Continuous gammaSubtractedDensity := by
  exact
    Complex.continuous_ofReal.comp ((Real.continuous_exp.comp continuous_neg).sub continuous_const)

/-- The subtracted density has an absolutely convergent Mellin integral on
the needed open strip -1 < Re s < 0. Use its linear and constant majorants.
This is the spatial convergence input for negative-line inversion. -/
theorem mellinConvergent_gammaSubtractedDensity {s : ℂ} (hlo : -1 < s.re) (hhi : s.re < 0) :
    MellinConvergent gammaSubtractedDensity s := by
  have ht : gammaSubtractedDensity =O[Filter.atTop] (fun u : ℝ ↦ u ^ (-(0 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
    simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using
      norm_gammaSubtractedDensity_le_one hu
  have hb : gammaSubtractedDensity =O[nhdsWithin 0 (Set.Ioi 0)] (fun u : ℝ ↦ u ^ (-(-1 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [self_mem_nhdsWithin] with u hu
    simpa only [neg_neg, Real.rpow_one, one_mul, Real.norm_eq_abs, abs_of_pos hu] using
      norm_gammaSubtractedDensity_le_self hu.le
  exact
    mellinConvergent_of_isBigO_rpow
      (continuous_gammaSubtractedDensity.continuousOn.locallyIntegrableOn measurableSet_Ioi) ht hhi
      hb hlo

/-- The complex-valued subtracted density has derivative minus exp(-u).
Differentiate the real exponential and then apply real inclusion. -/
theorem hasDerivAt_gammaSubtractedDensity (u : ℝ) :
    HasDerivAt gammaSubtractedDensity (-(Real.exp (-u) : ℂ)) u := by
  have h := (((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_id u).neg).sub_const 1).ofReal_comp
  convert h using 1
  · rfl
  · simp only [mul_neg_one, Complex.ofReal_neg]

/-- Near zero, the Mellin boundary product has norm at most u to the power Re s+1.
Multiply the linear density bound by the exact complex-power norm. -/
theorem norm_cpow_mul_gammaSubtractedDensity_le_zero (s : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ s * gammaSubtractedDensity u‖ ≤ u ^ (s.re + 1) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Real.rpow_add hu, Real.rpow_one]
  exact
    mul_le_mul_of_nonneg_left (norm_gammaSubtractedDensity_le_self hu.le) (Real.rpow_nonneg hu.le _)

/-- At infinity, the same Mellin boundary product has norm at most u to the power Re s.
Use the constant density bound before taking the improper boundary limit. -/
theorem norm_cpow_mul_gammaSubtractedDensity_le_top (s : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ s * gammaSubtractedDensity u‖ ≤ u ^ s.re := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu]
  have h :=
    mul_le_mul_of_nonneg_left (norm_gammaSubtractedDensity_le_one hu.le)
      (Real.rpow_nonneg hu.le s.re)
  simpa only [mul_one] using h

/-- For Re s > -1, the actual Mellin boundary product tends to zero from the right at zero.
Its vanishing is supplied by the subtracted density, not by the separate power factor. -/
theorem tendsto_cpow_mul_gammaSubtractedDensity_zero {s : ℂ} (hs : -1 < s.re) :
    Filter.Tendsto (fun u : ℝ ↦ (u : ℂ) ^ s * gammaSubtractedDensity u) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have he : 0 < s.re + 1 := by linarith only [hs]
  apply
    squeeze_zero_norm'
      (Filter.eventually_of_mem self_mem_nhdsWithin
        (fun u hu ↦ norm_cpow_mul_gammaSubtractedDensity_le_zero s hu))
  simpa only [Real.zero_rpow he.ne'] using
    ((Real.continuous_rpow_const he.le).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds

/-- For Re s < 0, the actual Mellin boundary product tends to zero at infinity.
Use its bounded density and the negative real-power decay. -/
theorem tendsto_cpow_mul_gammaSubtractedDensity_top {s : ℂ} (hs : s.re < 0) :
    Filter.Tendsto (fun u : ℝ ↦ (u : ℂ) ^ s * gammaSubtractedDensity u) Filter.atTop (nhds 0) := by
  apply
    squeeze_zero_norm'
      (Filter.eventually_of_mem (Filter.Ioi_mem_atTop (0 : ℝ))
        (fun u hu ↦ norm_cpow_mul_gammaSubtractedDensity_le_top s hu))
  simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hs)

/-- The differentiated exponential term has an absolutely convergent power integral
when Re s > -1. Euler's Gamma integral at s+1 supplies the integrability. -/
theorem integrableOn_cpow_mul_neg_exp {s : ℂ} (hs : -1 < s.re) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ s * (-(Real.exp (-u) : ℂ))) (Set.Ioi 0) := by
  have hp : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith only [hs]
  have h := (Complex.GammaIntegral_convergent hp).neg
  apply h.congr_fun _ measurableSet_Ioi
  intro u hu
  simp only [Pi.neg_apply, add_sub_cancel_right]
  ring

/-- Integration by parts evaluates the subtracted density's Mellin transform on
-1 < Re s < 0 as Gamma s. Both improper boundary terms vanish by the proved
product limits; the origin subtraction is retained exactly. -/
theorem mellin_gammaSubtractedDensity {s : ℂ} (hlo : -1 < s.re) (hhi : s.re < 0) :
    mellin gammaSubtractedDensity s = Complex.Gamma s := by
  have hp : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith only [hlo]
  have hs : s ≠ 0 := by
    intro he
    rw [he, Complex.zero_re] at hhi
    exact (lt_irrefl 0) hhi
  have hc := mellinConvergent_gammaSubtractedDensity hlo hhi
  change
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * gammaSubtractedDensity u)
      (Set.Ioi 0) at hc
  have h1 :
    MeasureTheory.IntegrableOn ((fun u : ℝ ↦ (u : ℂ) ^ s) * (fun u ↦ -(Real.exp (-u) : ℂ)))
      (Set.Ioi 0) :=
    integrableOn_cpow_mul_neg_exp hlo
  have h2 :
    MeasureTheory.IntegrableOn ((fun u : ℝ ↦ s * (u : ℂ) ^ (s - 1)) * gammaSubtractedDensity)
      (Set.Ioi 0) := by
    simpa only [MeasureTheory.IntegrableOn, Pi.mul_def, mul_assoc] using hc.const_mul s
  have hi :=
    MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      (fun u hu ↦ hasDerivAt_ofReal_cpow_const (ne_of_gt hu) hs)
      (fun u hu ↦ hasDerivAt_gammaSubtractedDensity u) h1 h2
      (by simpa only [Pi.mul_def] using tendsto_cpow_mul_gammaSubtractedDensity_zero hlo)
      (by simpa only [Pi.mul_def] using tendsto_cpow_mul_gammaSubtractedDensity_top hhi)
  have hleft :
    (∫ u : ℝ in Set.Ioi 0, (u : ℂ) ^ s * (-(Real.exp (-u) : ℂ))) = -Complex.Gamma (s + 1) := by
    rw [Complex.Gamma_eq_integral hp, Complex.GammaIntegral, ← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    simp only [add_sub_cancel_right]
    ring
  have hright :
    (∫ u : ℝ in Set.Ioi 0, (s * (u : ℂ) ^ (s - 1)) * gammaSubtractedDensity u) =
      s * mellin gammaSubtractedDensity s := by
    simp only [mellin, smul_eq_mul, mul_assoc, MeasureTheory.integral_const_mul]
  rw [hleft, hright, sub_zero, zero_sub] at hi
  have he : s * mellin gammaSubtractedDensity s = Complex.Gamma (s + 1) := neg_injective hi.symm
  rw [Complex.Gamma_add_one s hs] at he
  exact mul_left_cancel₀ hs he

end PseudoPrime.Analysis
