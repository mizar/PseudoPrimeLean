/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186Assembly
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186AbelSquare
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186H30
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186XiBudget

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ForwardAbel
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteLoss

/-! # Scalar finite envelope of the K186 direct comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The polynomial multiplying the rate-`11/4` part of the right Euler tail. -/
noncomputable def k186EulerLatePoly : Polynomial ℝ :=
  let P := k186MassPoly
  let Q := Polynomial.X ^ 2 * (Polynomial.C (13 / 4) * P - P.derivative)
  Polynomial.X ^ 2 * P + eulerMomentPoly Q (11 / 4)

/-- The finite loss with the reflected Euler, Xi, and right Euler contributions
replaced by fixed coefficients and polynomial evaluations. -/
noncomputable def k186FiniteEnvelope (C L x : ℝ) : ℝ :=
  let z := 5 + x
  Real.exp (-(11 / 4 : ℝ) * z) *
          ((2 * L - 4) * HighGaussianKernel.k186.realProfile.eval z +
            6 * k186ReflectedMoment.eval z) +
        Real.exp (-z / 2) * C -
      94173 / 1250 +
    3 / 100 +
    3 / 16 +
    4 * Real.exp (-(9 / 4 : ℝ) * x) * (eulerMomentPoly k186MassPoly (9 / 4)).eval x +
    Real.exp (-(11 / 4 : ℝ) * x) * k186EulerLatePoly.eval x / 6

/-- Under RH, the finite loss uses the same exponential-polynomial envelope
for the whole range. The only remaining negative-profile coefficient is H30. -/
theorem k186_finite_loss_le_envelope (hRH : RiemannHypothesis) {C : ℝ}
    (hC : highH30Charge .k186 ≤ C) (L x : ℝ) : k186FiniteLoss L x ≤ k186FiniteEnvelope C L x := by
  have hr := k186_reflected_le_moment (5 + x) hC
  have hxi := k186_xi_mass_le hRH
  have ht := k186_tail_cost_exp x
  dsimp only [k186FiniteLoss, k186FiniteEnvelope, k186EulerLatePoly] at ht ⊢
  rw [ht]
  linarith only [hr, hxi]

/-- After the H30 cap, positivity of the exponential-polynomial
comparison on the finite log range closes the remaining budget. -/
theorem k186_budget_of_envelope {C : ℝ} (hC : highH30Charge .k186 ≤ C)
    (h :
      ∀ x ∈ Set.Icc (30 : ℝ) 61,
        let L := Real.exp (x / 2) / gaussianK186FarScale
        3 / 8 * L + k186FiniteEnvelope C L x <
          0.7216056623106 * Real.exp (x / 2) - 301 / 20000 * x ^ 2 - (x + 5) ^ 2 / 6000 -
            k186ForwardEndpoint (x + 5) -
            6 / 5) :
    K186FiniteBudget := by
  apply k186_finite_budget_of_abel
  intro hRH x hx
  dsimp only
  have hh := h x hx
  have hr := k186_abel_residual_of_square hRH hx.1 k186_abel_square_le
  have hl := k186_finite_loss_le_envelope hRH hC (Real.exp (x / 2) / gaussianK186FarScale) x
  dsimp only [k186FiniteForward]
  linarith only [hh, hr, hl]

/-- The certified negative-profile coefficient leaves only the finite
range comparison to close the K186 budget. -/
theorem k186_budget_of_finite_check
    (h :
      ∀ x ∈ Set.Icc (30 : ℝ) 61,
        let L := Real.exp (x / 2) / gaussianK186FarScale
        3 / 8 * L + k186FiniteEnvelope 78548 L x <
          0.7216056623106 * Real.exp (x / 2) - 301 / 20000 * x ^ 2 - (x + 5) ^ 2 / 6000 -
            k186ForwardEndpoint (x + 5) -
            6 / 5) :
    K186FiniteBudget := by exact k186_budget_of_envelope k186_h30_charge_le h

end PseudoPrime.PrimeTestBounds.MillerRabin
