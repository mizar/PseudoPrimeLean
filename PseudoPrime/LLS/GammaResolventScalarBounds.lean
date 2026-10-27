/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaResolventFubini

/-! # Real scalar density for the Gamma central resolvent -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Real density for the normalized central resolvent, with decay c, scale x,
and Laplace coordinate r. Its integral is the exact inverse Mellin resolvent;
the definition retains the shifted scale to reuse the certified Gamma density. -/
noncomputable def gammaResolventScalarDensity (c x r : ℝ) : ℝ :=
  Real.exp (-c * r) * Real.sqrt ((x * Real.exp (-r / 2))⁻¹) * Real.exp (-(x * Real.exp (-r / 2))⁻¹)

/-- Every scalar density is nonnegative, since both exponential factors are
positive and the real square root is nonnegative. This supplies the sign of
individual inverse Mellin resolvents in the archimedean series. -/
theorem gammaResolventScalarDensity_nonneg (c x r : ℝ) : 0 ≤ gammaResolventScalarDensity c x r := by
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (Real.exp_pos _).le

/-- For positive decay and scale, the scalar density is integrable on the
positive half-line. Fubini integrability and the exact inner evaluation prove
this without adding a separate scalar-integrability premise. -/
theorem integrableOn_gammaResolventScalarDensity {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    MeasureTheory.IntegrableOn (gammaResolventScalarDensity c x) (Set.Ioi 0) := by
  have h :=
    ((integrable_central_resolvent_laplace_mul_weight hc hx).integral_prod_left.const_mul
        (((1 / (2 * Real.pi) : ℝ) : ℂ))).re
  exact
    h.congr
      (MeasureTheory.ae_of_all _
        (fun r ↦ by
          change
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ,
                    Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
                      gammaCentralMellinWeight x t)).re =
              gammaResolventScalarDensity c x r
          rw [gamma_central_laplace_inner_integral_eq_density hx c r]
          exact Complex.ofReal_re _))

/-- For positive decay and scale, the normalized resolvent integral is exactly
the real scalar integral embedded in the complex numbers. This formulation
allows real integral inequalities to be applied directly to the resolvent. -/
theorem gamma_central_resolvent_integral_eq_real {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, (1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * gammaCentralMellinWeight x t) =
      (((∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity c x r) : ℝ) : ℂ) := by
  rw [gamma_central_resolvent_integral_eq_scalar hc hx, ← integral_complex_ofReal]
  rfl

/-- Every positive-parameter normalized resolvent has nonnegative real part.
The exact real integral representation and the nonnegative density prove the
claim, giving the sign of the low-index terms in the parity series. -/
theorem gamma_central_resolvent_integral_re_nonneg {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    0 ≤
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            (1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * gammaCentralMellinWeight x t)).re := by
  rw [gamma_central_resolvent_integral_eq_real hc hx, Complex.ofReal_re]
  exact MeasureTheory.integral_nonneg (fun r ↦ gammaResolventScalarDensity_nonneg c x r)

/-- For a positive Mellin scale, rewrite the scalar density using the reciprocal
scale and an unshifted exponential. The formula isolates the decay exponent
c-1/4 and is used to compare high-index terms with elementary exponentials. -/
theorem gammaResolventScalarDensity_eq_exp {x : ℝ} (hx : 0 < x) (c r : ℝ) :
    gammaResolventScalarDensity c x r =
      Real.sqrt x⁻¹ * Real.exp (-(c - 1 / 4) * r) * Real.exp (-x⁻¹ * Real.exp (r / 2)) := by
  have hE : (Real.exp (-r / 2))⁻¹ = Real.exp (r / 2) := by
    rw [← Real.exp_neg]; congr 1; ring
  have hS : Real.sqrt (Real.exp (r / 2)) = Real.exp (r / 4) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    ring
  unfold gammaResolventScalarDensity
  rw [mul_inv, hE, Real.sqrt_mul (inv_pos.mpr hx).le, hS]
  simp only [neg_mul]
  have hD : -(c * r) + r / 4 = -((c - 1 / 4) * r) := by ring
  calc
    _ =
        Real.sqrt x⁻¹ * (Real.exp (-(c * r)) * Real.exp (r / 4)) *
          Real.exp (-(x⁻¹ * Real.exp (r / 2))) :=
      by ring
    _ = _ := by rw [← Real.exp_add, hD]

/-- A first-order exponential minorant bounds the scalar density from below
at every real Laplace coordinate. Positive scale ensures the nonnegative
prefactor. Integrating this bound yields the rational high-index estimate. -/
theorem gammaResolventScalarDensity_ge_tangent {x : ℝ} (hx : 0 < x) (c r : ℝ) :
    Real.sqrt x⁻¹ * Real.exp (-(c - 1 / 4) * r) * Real.exp (-x⁻¹) *
        (1 - x⁻¹ * (Real.exp (r / 2) - 1)) ≤
      gammaResolventScalarDensity c x r := by
  rw [gammaResolventScalarDensity_eq_exp hx]
  have hT : 1 - x⁻¹ * (Real.exp (r / 2) - 1) ≤ Real.exp (-x⁻¹ * (Real.exp (r / 2) - 1)) := by
    have h := Real.add_one_le_exp (-x⁻¹ * (Real.exp (r / 2) - 1))
    convert h using 1
    ring
  have hM :=
    mul_le_mul_of_nonneg_left hT
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg x⁻¹) (Real.exp_pos (-(c - 1 / 4) * r)).le)
        (Real.exp_pos (-x⁻¹)).le)
  have hE :
    Real.exp (-x⁻¹) * Real.exp (-x⁻¹ * (Real.exp (r / 2) - 1)) =
      Real.exp (-x⁻¹ * Real.exp (r / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [mul_assoc, hE] using hM

end PseudoPrime.LLS.PaperStatements
