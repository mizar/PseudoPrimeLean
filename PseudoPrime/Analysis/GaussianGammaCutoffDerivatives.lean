/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianGammaCutoff
public import PseudoPrime.Analysis.MidpointQuadrature

/-! # Explicit derivatives of the Gaussian cutoff density -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The tilted Gaussian exp(-v²+v/2) has logarithmic derivative -2v+1/2.
Differentiate its quadratic exponent explicitly. This supplies the first product factor. -/
theorem hasDerivAt_gaussianTilt (v : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.exp (-(x ^ 2) + x / 2))
      (Real.exp (-(v ^ 2) + v / 2) * (-2 * v + 1 / 2)) v := by
  have hd := (((hasDerivAt_id v).pow 2).neg.add ((hasDerivAt_id v).div_const 2)).exp
  simp only [Pi.neg_apply, Pi.add_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one] at hd
  convert hd using 1
  ring

/-- At cutoff l and shift v, the factor 1-exp(-l exp(-v)) has derivative
-l exp(-v) exp(-l exp(-v)). Two chain rules give the cutoff contribution. -/
theorem hasDerivAt_gaussianCutoffFactor (l v : ℝ) :
    HasDerivAt (fun x : ℝ ↦ 1 - Real.exp (-l * Real.exp (-x)))
      (-l * Real.exp (-v) * Real.exp (-l * Real.exp (-v))) v := by
  have hd := (hasDerivAt_const v (1 : ℝ)).sub (((hasDerivAt_id v).neg.exp.const_mul (-l)).exp)
  simp only [Pi.neg_apply, id_eq] at hd
  convert hd using 1
  ring

/-- The first tilted Gaussian derivative has derivative A((−2v+1/2)²−2).
The product rule isolates the curvature polynomial used in the midpoint error bound. -/
theorem hasDerivAt_gaussianTilt_first (v : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.exp (-(x ^ 2) + x / 2) * (-2 * x + 1 / 2))
      (Real.exp (-(v ^ 2) + v / 2) * ((-2 * v + 1 / 2) ^ 2 - 2)) v := by
  have hd := (hasDerivAt_gaussianTilt v).mul (((hasDerivAt_id v).const_mul (-2)).add_const (1 / 2))
  simp only [id_eq, mul_one] at hd
  convert hd using 1
  ring

/-- Writing z=l exp(-v), the cutoff factor's second derivative is (z-z²)exp(-z).
Differentiate the first derivative by the product rule. This is the second cutoff contribution. -/
theorem hasDerivAt_gaussianCutoffFactor_first (l v : ℝ) :
    HasDerivAt (fun x : ℝ ↦ -l * Real.exp (-x) * Real.exp (-l * Real.exp (-x)))
      ((l * Real.exp (-v) - (l * Real.exp (-v)) ^ 2) * Real.exp (-l * Real.exp (-v))) v := by
  have hz := (hasDerivAt_id v).neg.exp.const_mul (-l)
  have hd := hz.mul hz.exp
  simp only [Pi.neg_apply, id_eq] at hd
  convert hd using 1
  ring

/-- The explicit first derivative of the normalized Gaussian cutoff density.
Inputs are cutoff l and shift v; the two product contributions retain the sqrt(pi)
normalization. The derivative theorem connects this formula to midpoint quadrature. -/
noncomputable def gaussianGammaCutoffIntegrandDeriv (l v : ℝ) : ℝ :=
  (Real.exp (-(v ^ 2) + v / 2) * (-2 * v + 1 / 2) * (1 - Real.exp (-l * Real.exp (-v))) +
      Real.exp (-(v ^ 2) + v / 2) * (-l * Real.exp (-v) * Real.exp (-l * Real.exp (-v)))) /
    Real.sqrt Real.pi

/-- The explicit second derivative of the normalized Gaussian cutoff density.
The three terms are A''C, 2A'C', and AC'', divided by sqrt(pi).
This formula separates factors for the uniform curvature estimate. -/
noncomputable def gaussianGammaCutoffIntegrandSecondDeriv (l v : ℝ) : ℝ :=
  (Real.exp (-(v ^ 2) + v / 2) * ((-2 * v + 1 / 2) ^ 2 - 2) * (1 - Real.exp (-l * Real.exp (-v))) +
      2 * (Real.exp (-(v ^ 2) + v / 2) * (-2 * v + 1 / 2)) *
        (-l * Real.exp (-v) * Real.exp (-l * Real.exp (-v))) +
      Real.exp (-(v ^ 2) + v / 2) *
        ((l * Real.exp (-v) - (l * Real.exp (-v)) ^ 2) * Real.exp (-l * Real.exp (-v)))) /
    Real.sqrt Real.pi

/-- The cutoff density equals the tilted Gaussian times its cutoff factor,
divided by sqrt(pi). Combine exponentials to expose the product used for differentiation. -/
theorem gaussianGammaCutoffIntegrand_eq_product (l v : ℝ) :
    gaussianGammaCutoffIntegrand l v =
      (Real.exp (-(v ^ 2) + v / 2) * (1 - Real.exp (-l * Real.exp (-v)))) / Real.sqrt Real.pi := by
  rw [gaussianGammaCutoffIntegrand, normalizedGaussianWeight, Real.exp_add]
  ring

/-- For every real cutoff and shift, the explicit first derivative differentiates
the actual cutoff density. Rewrite to the tilted product and use both factor derivatives.
This supplies the first derivative input to the composite midpoint rule. -/
theorem hasDerivAt_gaussianGammaCutoffIntegrand (l v : ℝ) :
    HasDerivAt (gaussianGammaCutoffIntegrand l) (gaussianGammaCutoffIntegrandDeriv l v) v := by
  have he :
    gaussianGammaCutoffIntegrand l = fun x : ℝ ↦
      (Real.exp (-(x ^ 2) + x / 2) * (1 - Real.exp (-l * Real.exp (-x)))) / Real.sqrt Real.pi :=
    funext (gaussianGammaCutoffIntegrand_eq_product l)
  rw [he]
  exact
    ((hasDerivAt_gaussianTilt v).mul (hasDerivAt_gaussianCutoffFactor l v)).div_const
      (Real.sqrt Real.pi)

/-- For every real cutoff and shift, the explicit second derivative differentiates
the first derivative formula. Two product rules collect the mixed terms.
This supplies the second derivative input to the composite midpoint rule. -/
theorem hasDerivAt_gaussianGammaCutoffIntegrandDeriv (l v : ℝ) :
    HasDerivAt (gaussianGammaCutoffIntegrandDeriv l) (gaussianGammaCutoffIntegrandSecondDeriv l v)
      v := by
  have hd :=
    (((hasDerivAt_gaussianTilt_first v).mul (hasDerivAt_gaussianCutoffFactor l v)).add
          ((hasDerivAt_gaussianTilt v).mul (hasDerivAt_gaussianCutoffFactor_first l v))).div_const
      (Real.sqrt Real.pi)
  convert hd using 1
  · rfl
  · unfold gaussianGammaCutoffIntegrandSecondDeriv
    ring

end PseudoPrime.Analysis
