/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaResolventScalarBounds

/-! # Integrated rational minorant for the Gamma central resolvent -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Elementary exponential minorant of the scalar density. The two decay
rates are positive when c exceeds 3/4; its exact integral gives the high-index
resolvent lower bound used in the archimedean parity series. -/
noncomputable def gammaResolventMinorant (c x r : ℝ) : ℝ :=
  (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) *
    ((1 + x⁻¹) * Real.exp (-(c - 1 / 4) * r) - x⁻¹ * Real.exp (-(c - 3 / 4) * r))

/-- For positive scale, the elementary exponential minorant is bounded by the
actual scalar density at every real coordinate. The proof expands the tangent
minorant and combines its exponential factors without changing the sign. -/
theorem gammaResolventMinorant_le_density {x : ℝ} (hx : 0 < x) (c r : ℝ) :
    gammaResolventMinorant c x r ≤ gammaResolventScalarDensity c x r := by
  have hE : Real.exp (-(c - 1 / 4) * r) * Real.exp (r / 2) = Real.exp (-(c - 3 / 4) * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hEq :
    gammaResolventMinorant c x r =
      Real.sqrt x⁻¹ * Real.exp (-(c - 1 / 4) * r) * Real.exp (-x⁻¹) *
        (1 - x⁻¹ * (Real.exp (r / 2) - 1)) := by
    unfold gammaResolventMinorant
    rw [← hE]
    ring
  rw [hEq]
  exact gammaResolventScalarDensity_ge_tangent hx c r

/-- When c exceeds 3/4, both exponential terms in the minorant are integrable
on the positive half-line. Constants depending on the scale do not affect
integrability, so this claim holds for every real scale. -/
theorem integrableOn_gammaResolventMinorant {c : ℝ} (hc : 3 / 4 < c) (x : ℝ) :
    MeasureTheory.IntegrableOn (gammaResolventMinorant c x) (Set.Ioi 0) := by
  have h1 : -(c - 1 / 4) < 0 := by linarith only [hc]
  have h2 : -(c - 3 / 4) < 0 := neg_neg_of_pos (sub_pos.mpr hc)
  exact
    (((integrableOn_exp_mul_Ioi h1 (0 : ℝ)).const_mul (1 + x⁻¹)).sub
          ((integrableOn_exp_mul_Ioi h2 (0 : ℝ)).const_mul x⁻¹)).const_mul
      (Real.sqrt x⁻¹ * Real.exp (-x⁻¹))

/-- The minorant has an exact rational integral when both decay rates are
positive. Integrate the two elementary exponentials separately after proving
their integrability; the resulting difference retains the cancellation. -/
theorem integral_gammaResolventMinorant {c : ℝ} (hc : 3 / 4 < c) (x : ℝ) :
    (∫ r : ℝ in Set.Ioi 0, gammaResolventMinorant c x r) =
      (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) * ((1 + x⁻¹) / (c - 1 / 4) - x⁻¹ / (c - 3 / 4)) := by
  have h1 : -(c - 1 / 4) < 0 := by linarith only [hc]
  have h2 : -(c - 3 / 4) < 0 := neg_neg_of_pos (sub_pos.mpr hc)
  unfold gammaResolventMinorant
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub ((integrableOn_exp_mul_Ioi h1 (0 : ℝ)).const_mul (1 + x⁻¹))
      ((integrableOn_exp_mul_Ioi h2 (0 : ℝ)).const_mul x⁻¹),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, integral_exp_mul_Ioi h1,
    integral_exp_mul_Ioi h2]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, mul_one_div]

/-- Positive scale and decay c greater than 3/4 give a rational lower bound
for the actual scalar integral. Both sides of the integral comparison are
integrable, and the pointwise comparison is the proved tangent minorant. -/
theorem integral_gammaResolventScalarDensity_ge_rational {c x : ℝ} (hc : 3 / 4 < c) (hx : 0 < x) :
    (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) * ((1 + x⁻¹) / (c - 1 / 4) - x⁻¹ / (c - 3 / 4)) ≤
      ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity c x r := by
  have hc0 : 0 < c := by linarith only [hc]
  rw [← integral_gammaResolventMinorant hc x]
  exact
    MeasureTheory.integral_mono (integrableOn_gammaResolventMinorant hc x)
      (integrableOn_gammaResolventScalarDensity hc0 hx)
      (fun r ↦ gammaResolventMinorant_le_density hx c r)

/-- The actual normalized central Gamma resolvent has the certified rational
lower bound on its real part for positive scale and c greater than 3/4.
The exact real integral representation transfers the scalar estimate directly
to the inverse Mellin term in the digamma series. -/
theorem gamma_central_resolvent_integral_re_ge_rational {c x : ℝ} (hc : 3 / 4 < c) (hx : 0 < x) :
    (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) * ((1 + x⁻¹) / (c - 1 / 4) - x⁻¹ / (c - 3 / 4)) ≤
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            (1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * gammaCentralMellinWeight x t)).re := by
  have hc0 : 0 < c := by linarith only [hc]
  rw [gamma_central_resolvent_integral_eq_real hc0 hx, Complex.ofReal_re]
  exact integral_gammaResolventScalarDensity_ge_rational hc hx

/-- Express the actual resolvent lower bound as a leading reciprocal minus
a second-order rational error. Both denominators are positive under c > 3/4.
This cancellation-preserving form is suited to summing the parity tails. -/
theorem gamma_central_resolvent_integral_re_ge_main_sub_error {c x : ℝ} (hc : 3 / 4 < c)
    (hx : 0 < x) :
    (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) * (1 / (c - 1 / 4) - x⁻¹ / (2 * (c - 1 / 4) * (c - 3 / 4))) ≤
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            (1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * gammaCentralMellinWeight x t)).re := by
  have h1 : c - 1 / 4 ≠ 0 := ne_of_gt (by linarith only [hc])
  have h2 : c - 3 / 4 ≠ 0 := ne_of_gt (sub_pos.mpr hc)
  have hE :
    1 / (c - 1 / 4) - x⁻¹ / (2 * (c - 1 / 4) * (c - 3 / 4)) =
      (1 + x⁻¹) / (c - 1 / 4) - x⁻¹ / (c - 3 / 4) := by
    have h3 : c * 4 - 1 ≠ 0 := ne_of_gt (by linarith only [hc])
    have h4 : c * 4 - 3 ≠ 0 := ne_of_gt (by linarith only [hc])
    field_simp [h1, h2, h3, h4, hx.ne']
    ring
  rw [hE]
  exact gamma_central_resolvent_integral_re_ge_rational hc hx

end PseudoPrime.LLS.PaperStatements
