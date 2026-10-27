/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularExplicitNumerics
public import PseudoPrime.LLS.MellinKernelCompactZeroMass
public import PseudoPrime.LLS.MellinKernelExplicitFormula

/-! # Positive triangular kernel zero sums and the scale-one explicit formula

Imaginary-axis positivity identifies the oscillating sum at one with absolute mass.
The exact residue formula then isolates this mass without a cancellation coefficient.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a positive triangular parameter and a nonprincipal character, every
kernel zero term is the complex cast of its nonnegative norm. Identify divisor
multiplicity with natural analytic order and use the imaginary-axis sinc square.
This removes possible complex cancellation in the triangular zero ledger. -/
theorem triangular_kernelZeroTerm_eq_ofReal_norm {a : ℝ} (ha : 0 < a) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (ρ : ℂ) :
    (triangularMellinKernel ha).kernelZeroTerm χ ρ =
      ((‖(triangularMellinKernel ha).kernelZeroTerm χ ρ‖ : ℝ) : ℂ) := by
  rw [MellinKernel.norm_kernelZeroTerm_eq_order_mul _ hne]
  rw [MellinKernel.kernelZeroTerm,
    AnalyticNumberTheory.DirichletLFunction.completed_divisor_eq_analyticOrderNatAt hne,
    Int.cast_natCast]
  change
    (analyticOrderNatAt χ.completedLFunction ρ : ℂ) *
        Analysis.triangularMellinFunction a (Complex.I * ρ.im) =
      ((analyticOrderNatAt χ.completedLFunction ρ : ℝ) *
          ‖Analysis.triangularMellinFunction a (Complex.I * ρ.im)‖ :
        ℝ)
  rw [Analysis.norm_triangularMellinFunction_imaginary ha.ne',
    Analysis.triangularMellinFunction_imaginary ha.ne', Complex.ofReal_mul, Complex.ofReal_natCast]

/-- The triangular zero sum equals the complex cast of its absolute mass
for a nonprincipal character. Apply the pointwise positivity identity and
commute real casts with the infinite sum. This requires no GRH for the identity. -/
theorem triangular_kernelZeroSum_eq_ofReal_absoluteMass {a : ℝ} (ha : 0 < a) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) :
    (∑' ρ : ℂ, (triangularMellinKernel ha).kernelZeroTerm χ ρ) =
      ((∑' ρ : ℂ, ‖(triangularMellinKernel ha).kernelZeroTerm χ ρ‖ : ℝ) : ℂ) := by
  calc
    _ = ∑' ρ : ℂ, ((‖(triangularMellinKernel ha).kernelZeroTerm χ ρ‖ : ℝ) : ℂ) :=
      tsum_congr (fun ρ ↦ triangular_kernelZeroTerm_eq_ofReal_norm ha hne ρ)
    _ = _ := (Complex.ofReal_tsum _).symm

/-- At scale one, the triangular oscillating zero sum equals the complex
cast of the absolute zero mass. The phase is one and all zero terms are
nonnegative real casts. This connects the zero ledger to the explicit formula. -/
theorem triangular_oscillatingZeroSum_one_eq_ofReal_absoluteMass {a : ℝ} (ha : 0 < a) {q : ℕ}
    [NeZero q] {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) :
    (∑' ρ : ℂ, (triangularMellinKernel ha).oscillatingZeroTerm χ 1 ρ) =
      ((∑' ρ : ℂ, ‖(triangularMellinKernel ha).kernelZeroTerm χ ρ‖ : ℝ) : ℂ) := by
  simp only [MellinKernel.oscillatingZeroTerm, Complex.ofReal_one, Complex.one_cpow, mul_one]
  exact triangular_kernelZeroSum_eq_ofReal_absoluteMass ha hne

/-- For primitive nonprincipal GRH data of modulus at least two, the actual
alpha-18 absolute zero mass plus the scale-one arithmetic sum equals the pole
and the completed left-line and gamma-factor right-line integrals. Specialize
the exact contour formula to lines -9/16 and 9/16 and use zero-term positivity.
This is the identity from which an explicit finite-conductor mass bound is derived. -/
theorem triangular18_absoluteMass_explicit_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (∑' n : ℕ, K.summand χ 1 n) + ((∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ : ℝ) : ℂ) =
      MellinKernel.weightedResidue K (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) 1 (-1 / 2) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv (DirichletCharacter.gammaFactor χ)
                (((9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have he :=
    MellinKernel.tsum_summand_eq_completed_residue_formula K hq hGRH hp hne hinv (a := -9 / 16)
      (b := 9 / 16) (x := 1) (by norm_num only)
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) le_rfl (by norm_num only) (by norm_num only)
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at he
  rw [triangular_oscillatingZeroSum_one_eq_ofReal_absoluteMass (by norm_num only : (0 : ℝ) < 18)
      hne] at he
  linear_combination he

end PseudoPrime.LLS.PaperStatements
