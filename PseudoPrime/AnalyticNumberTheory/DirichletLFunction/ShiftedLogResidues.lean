/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ShiftedLogarithmicResidues
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedLogMellinInversion
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HadamardMultiplicityFactorization

/-!
# Local shifted logarithmic residues for Dirichlet characters

Specialize the general origin and zero residue formulas to the character kernel.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The character kernel is the general shifted logarithmic kernel. Unfold logDeriv and
move the negation through division to reuse the general local residue formulas. -/
theorem shiftedLogContourKernel_eq_general {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x σ : ℝ)
    (s : ℂ) :
    shiftedLogContourKernel χ x σ s = General.shiftedLogarithmicKernel χ.LFunction x (σ : ℂ) s := by
  unfold shiftedLogContourKernel General.shiftedLogarithmicKernel
  rw [logDeriv_apply, neg_div]

/-- For a nonprincipal character, x>0 and sigma>=1, all sufficiently small squares at zero
have the explicit double-pole residue. L is analytic and nonzero at sigma; specialize the
general regularization formula. This is the Mellin-pole term of the shifted contour ledger. -/
theorem exists_radius_shiftedLogContourKernel_origin {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {x σ : ℝ} (hx : 0 < x) (hσ : 1 ≤ σ) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral (shiftedLogContourKernel χ x σ)
                (RectangleGeometry.centeredSquareLower 0 r)
                (RectangleGeometry.centeredSquareUpper 0 r) =
              2 * Real.pi * Complex.I *
                (-deriv (logDeriv χ.LFunction) (σ : ℂ) -
                  logDeriv χ.LFunction (σ : ℂ) * (Real.log x : ℂ)) := by
  have hL : χ.LFunction (σ : ℂ) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simpa only [Complex.ofReal_re] using hσ)
  have heq :
    shiftedLogContourKernel χ x σ = General.shiftedLogarithmicKernel χ.LFunction x (σ : ℂ) :=
    funext (shiftedLogContourKernel_eq_general χ x σ)
  rw [heq]
  exact
    General.exists_radius_shiftedLogarithmicKernel_origin
      ((χ.differentiable_LFunction hχ).analyticAt _) hL hx

/-- For a nonprincipal character, x>0 and an L-zero rho distinct from sigma, the residue at
rho-sigma is minus its multiplicity times x^(rho-sigma)/(rho-sigma)^2.
The local finite-order factorization supplies the regular logarithmic derivative.
This records the shifted zero contribution before global contour assembly. -/
theorem exists_radius_shiftedLogContourKernel_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {x σ : ℝ} {ρ : ℂ} (hx : 0 < x) (hzero : χ.LFunction ρ = 0) (hρ : ρ - (σ : ℂ) ≠ 0) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral (shiftedLogContourKernel χ x σ)
                (RectangleGeometry.centeredSquareLower (ρ - (σ : ℂ)) r)
                (RectangleGeometry.centeredSquareUpper (ρ - (σ : ℂ)) r) =
              2 * Real.pi * Complex.I *
                (-(dirichletLFunctionZeroMultiplicity χ ρ : ℂ) * (x : ℂ) ^ (ρ - (σ : ℂ)) /
                  (ρ - (σ : ℂ)) ^ 2) := by
  obtain ⟨g, _, hg, hg0, hlog⟩ := exists_eventuallyEq_logDeriv_dirichletLFunction_at_zero hχ hzero
  have heq :
    shiftedLogContourKernel χ x σ = General.shiftedLogarithmicKernel χ.LFunction x (σ : ℂ) :=
    funext (shiftedLogContourKernel_eq_general χ x σ)
  rw [heq]
  exact General.exists_radius_shiftedLogarithmicKernel_zero hg hg0 hx hρ hlog

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
