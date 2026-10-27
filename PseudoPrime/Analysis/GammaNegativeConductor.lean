/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaNegativeInversion

/-!
# The signed conductor term on a negative Gamma Mellin line

Exact negative-strip inversion gives a nonpositive conductor contribution, with the
origin residue subtracted. This evaluates the constant component, not the remaining
Dirichlet or digamma parts of a left contour integral.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The real conductor contribution for coefficient A and positive scale x.
It is A/sqrt(x) times exp(-1/x)-1; the subtracted one retains the origin residue. -/
noncomputable def gammaNegativeConductorTerm (A x : ℝ) : ℝ :=
  A / Real.sqrt x * (Real.exp (-x⁻¹) - 1)

/-- On -1 < c < 0, the actual inverse Gamma integral with constant coefficient A/sqrt(x)
is the real signed conductor term. Negative-strip Mellin inversion supplies the equality. -/
theorem negative_conductor_mellinInv_eq {c x : ℝ} (hlo : -1 < c) (hhi : c < 0) (hx : 0 < x)
    (A : ℝ) :
    (A : ℂ) / (Real.sqrt x : ℂ) * mellinInv c Complex.Gamma x⁻¹ =
      (gammaNegativeConductorTerm A x : ℂ) := by
  rw [mellinInv_Gamma_negative hlo hhi (inv_pos.mpr hx)]
  simp only [gammaNegativeConductorTerm, Complex.ofReal_mul, Complex.ofReal_div]

/-- For a nonnegative conductor coefficient, the exact contribution is nonpositive.
Use exp(-1/x) ≤ 1, retaining its sign instead of paying its absolute value. -/
theorem gammaNegativeConductorTerm_nonpos {A x : ℝ} (hA : 0 ≤ A) (hx : 0 < x) :
    gammaNegativeConductorTerm A x ≤ 0 := by
  exact
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg hA (Real.sqrt_nonneg x))
      (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr hx.le))))

/-- The signed conductor term is bounded below by -A/(x sqrt(x)) for A ≥ 0 and x > 0.
The tangent inequality for exp bounds the exact correction's magnitude. -/
theorem gammaNegativeConductorTerm_lower {A x : ℝ} (hA : 0 ≤ A) (hx : 0 < x) :
    -(A / (x * Real.sqrt x)) ≤ gammaNegativeConductorTerm A x := by
  have he := Real.add_one_le_exp (-x⁻¹)
  have h :=
    mul_le_mul_of_nonneg_left (by linarith only [he] : -x⁻¹ ≤ Real.exp (-x⁻¹) - 1)
      (div_nonneg hA (Real.sqrt_pos.mpr hx).le)
  dsimp only [gammaNegativeConductorTerm]
  convert h using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A conductor f ≥ pi makes log(f/pi) nonnegative, hence gives a nonpositive exact
negative-line contribution. This is the sign required by the proposed left-line budget. -/
theorem gammaNegativeConductorTerm_log_nonpos {f x : ℝ} (hf : Real.pi ≤ f) (hx : 0 < x) :
    gammaNegativeConductorTerm (Real.log (f / Real.pi)) x ≤ 0 := by
  apply gammaNegativeConductorTerm_nonpos _ hx
  exact Real.log_nonneg ((le_div_iff₀ Real.pi_pos).mpr (by simpa only [one_mul] using hf))

/-- On a positive real base, inverse-base negative powers equal the original powers.
The principal logarithm has zero argument, so inversion introduces no branch correction. -/
theorem positive_inv_cpow_neg {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ (-z) = (x : ℂ) ^ z := by
  have ha : Complex.arg (x : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact ne_of_lt Real.pi_pos
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ ha, Complex.cpow_neg, inv_inv]

/-- The actual vertical Gamma integral with x to the contour power equals exp(-1/x)-1
on -1 < c < 0. Rewrite the positive inverse base in the proved Mellin inversion formula. -/
theorem negative_Gamma_vertical_integral_eq {c x : ℝ} (hlo : -1 < c) (hhi : c < 0) (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ t : ℝ, Complex.Gamma ((c : ℂ) + t * Complex.I) * (x : ℂ) ^ ((c : ℂ) + t * Complex.I)) =
      (Real.exp (-x⁻¹) - 1 : ℝ) := by
  rw [← mellinInv_Gamma_negative hlo hhi (inv_pos.mpr hx), mellinInv]
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by simp only [positive_inv_cpow_neg hx, smul_eq_mul, mul_comm])

/-- The actual constant-coefficient vertical integral, normalized by sqrt(x), equals
the signed real conductor term. This supplies the constant component of a left-line split;
the nonconstant logarithmic-derivative remainder is not estimated by this theorem. -/
theorem negative_conductor_vertical_integral_eq {c x : ℝ} (hlo : -1 < c) (hhi : c < 0) (hx : 0 < x)
    (A : ℝ) :
    (A : ℂ) / (Real.sqrt x : ℂ) *
        ((1 / (2 * Real.pi) : ℝ) •
          (∫ t : ℝ,
            Complex.Gamma ((c : ℂ) + t * Complex.I) * (x : ℂ) ^ ((c : ℂ) + t * Complex.I))) =
      (gammaNegativeConductorTerm A x : ℂ) := by
  rw [negative_Gamma_vertical_integral_eq hlo hhi hx]
  simp only [gammaNegativeConductorTerm, Complex.ofReal_mul, Complex.ofReal_div]

end PseudoPrime.Analysis
