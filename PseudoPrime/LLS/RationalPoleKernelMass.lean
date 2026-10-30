/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.CauchyPowerIntegrals
public import PseudoPrime.LLS.RationalPoleKernel
public import PseudoPrime.LLS.MellinKernelForwardTransform

/-! # Actual masses and principal endpoint values for rational-pole kernels -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The fixed fourth-order admissible kernel with a=13/25 and c=14/25.
All admissibility fields come from the proved rational-pole construction. This is the
quadratic candidate whose finite cutoff coefficient remains to be certified. -/
noncomputable def rationalPoleFourKernel : MellinKernel :=
  rationalPoleMellinKernel 2 (13 / 25) (14 / 25) (by norm_num only) (by norm_num only)
    (by norm_num only)

/-- The fixed sixth-order admissible kernel with a=1/2 and c=3/2.
The same function and profile serve indices four, five and six. Constructing the kernel
does not assert the numerical conductor coefficient or any finite entrance point. -/
noncomputable def rationalPoleSixKernel : MellinKernel :=
  rationalPoleMellinKernel 3 (1 / 2) (3 / 2) (by norm_num only) (by norm_num only)
    (by norm_num only)

/-- For m>=1,0<a<1, the actual rational-pole Mellin mass equals the m-th Cauchy
integral divided by 2pi. Substitute the exact critical-line norm and change variables
by the positive scale 2a. The mass is independent of a and the modulation c. -/
theorem rationalPole_mass_eq_cauchy_integral (m : ℕ) {a c : ℝ} (hm : 1 ≤ m) (ha : 0 < a)
    (ha1 : a < 1) :
    (rationalPoleMellinKernel m a c hm ha ha1).mass =
      (∫ t : ℝ, 1 / (1 + t ^ 2) ^ m) / (2 * Real.pi) := by
  have hA : 0 < 2 * a := mul_pos (by norm_num only) ha
  have hn (t : ℝ) :
    ‖Analysis.rationalPoleFunction m a c (Complex.I * t)‖ =
      (2 * a) * (1 / (1 + (2 * a * t) ^ 2) ^ m) :=
    (Analysis.norm_rationalPoleFunction m ha t).trans (mul_one_div _ _).symm
  change (∫ t : ℝ, ‖Analysis.rationalPoleFunction m a c (Complex.I * t)‖) / (2 * Real.pi) = _
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hn),
    MeasureTheory.integral_const_mul,
    MeasureTheory.Measure.integral_comp_mul_left (fun t : ℝ ↦ 1 / (1 + t ^ 2) ^ m) (2 * a),
    smul_eq_mul, abs_of_pos (inv_pos.mpr hA), ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul]

/-- Every admissible fourth-order rational-pole kernel has actual mass 1/4.
Insert the exact second Cauchy integral into the scale-independent mass identity.
This is the mass used by the quadratic coefficient certificate. -/
theorem rationalPole_four_mass {a c : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (rationalPoleMellinKernel 2 a c (by norm_num only) ha ha1).mass = 1 / 4 := by
  rw [rationalPole_mass_eq_cauchy_integral, Analysis.integral_cauchy_power_two]
  apply (div_eq_iff (mul_ne_zero (by norm_num only) Real.pi_ne_zero)).mpr
  apply (div_eq_iff (by norm_num only : (2 : ℝ) ≠ 0)).mpr
  ring

/-- Every admissible sixth-order rational-pole kernel has actual mass 3/16.
Insert the exact third Cauchy integral into the scale-independent mass identity.
One shared kernel can therefore serve the index-four, five and six certificates. -/
theorem rationalPole_six_mass {a c : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (rationalPoleMellinKernel 3 a c (by norm_num only) ha ha1).mass = 3 / 16 := by
  rw [rationalPole_mass_eq_cauchy_integral, Analysis.integral_cauchy_power_three]
  apply (div_eq_iff (mul_ne_zero (by norm_num only) Real.pi_ne_zero)).mpr
  apply (div_eq_iff (by norm_num only : (8 : ℝ) ≠ 0)).mpr
  ring

/-- The actual rational-pole function at 1/2 has real value
2a exp(c)/(1+a)^(2m). Evaluate the complex exponent and real denominator.
This identifies the principal endpoint in the conductor comparison. -/
theorem rationalPole_half_value (m : ℕ) {a c : ℝ} (hm : 1 ≤ m) (ha : 0 < a) (ha1 : a < 1) :
    ((rationalPoleMellinKernel m a c hm ha ha1).function (1 / 2)).re =
      2 * a * Real.exp c / (1 + a) ^ (2 * m) := by
  change (Analysis.rationalPoleFunction m a c (1 / 2)).re = _
  unfold Analysis.rationalPoleFunction
  rw [show 2 * (c : ℂ) * (1 / 2) = (c : ℂ) by ring,
    show 1 + 2 * (a : ℂ) * (1 / 2) = 1 + (a : ℂ) by ring]
  have he :
    ((2 * a : ℝ) : ℂ) * Complex.exp (c : ℂ) / (1 + (a : ℂ)) ^ (2 * m) =
      (2 * a * Real.exp c / (1 + a) ^ (2 * m) : ℝ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_exp]
  rw [he, Complex.ofReal_re]

/-- For positive u, the actual admissible rational-pole kernel has the stated
real profile as its transform. Apply the proved inverse formula on the line zero,
which lies right of the pole. This connects profile calculations to the actual kernel. -/
theorem rationalPole_transform (m : ℕ) {a c u : ℝ} (hm : 1 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hu : 0 < u) :
    (rationalPoleMellinKernel m a c hm ha ha1).transform u =
      (Analysis.rationalPoleProfile m a c u : ℂ) := by
  exact
    Analysis.inverseMellin_rationalPole hm ha
      (by simpa only [zero_add] using inv_pos.mpr (mul_pos (by norm_num only) ha)) hu c

/-- The actual full positive-axis weighted profile integral equals
2a exp(c)/(1+a)^(2m). Apply the existing forward Mellin identity and the half-value
formula. A separate truncated integral is still needed for the principal cutoff at one. -/
theorem rationalPole_total_weight (m : ℕ) {a c : ℝ} (hm : 1 ≤ m) (ha : 0 < a) (ha1 : a < 1) :
    (∫ u : ℝ in Set.Ioi 0,
        ((rationalPoleMellinKernel m a c hm ha ha1).transform u).re / Real.sqrt u) =
      2 * a * Real.exp c / (1 + a) ^ (2 * m) := by
  exact (MellinKernel.integral_weight_Ioi_eq _).trans (rationalPole_half_value m hm ha ha1)

end PseudoPrime.LLS.PaperStatements
