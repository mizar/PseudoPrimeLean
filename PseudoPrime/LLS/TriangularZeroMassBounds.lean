/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularIntegralNumerics

/-! # Alpha-18 absolute zero mass with one remaining arithmetic term

The conductor coefficient is exactly thirty-six and both contour integrals have
numerical constants. The entire triangular kernel contributes no designated pole.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal GRH data of modulus at least two, the actual
alpha-18 absolute zero mass is at most 36*log(q), the absolute real scale-one
arithmetic sum, and 1150000000000000. Remove the zero pole term, take real parts
of the conductor formula, and apply the two numerical integral bounds.
This isolates the arithmetic term still needed for the final additive constant. -/
theorem triangular18_absoluteMass_le_conductor_add_arithmetic {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤
      36 * Real.log q + |(∑' n : ℕ, K.summand χ 1 n).re| + 1150000000000000 := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let R :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
          K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))
  let G :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv χ.gammaFactor (((9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
  have hR : ‖R‖ ≤ (1100000000000000 : ℝ) := triangular18_normalized_reflectedIntegral_norm_le hinv
  have hG : ‖G‖ ≤ (50000000000000 : ℝ) := triangular18_normalized_gammaIntegral_norm_le χ
  have he := triangular18_absoluteMass_conductor_formula hq hGRH hp hne hinv
  dsimp only at he
  rw [triangular_weightedResidue_pole_eq_zero, add_zero] at he
  rw [← Complex.natCast_log, ← Complex.ofReal_ofNat 36, ← Complex.ofReal_mul] at he
  have her := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re] at her
  change
    (∑' n : ℕ, K.summand χ 1 n).re + (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) =
      36 * Real.log q + R.re + G.re at her
  have hr := (Complex.re_le_norm R).trans hR
  have hg := (Complex.re_le_norm G).trans hG
  have hs := le_abs_self (-(∑' n : ℕ, K.summand χ 1 n).re)
  rw [abs_neg] at hs
  change (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤ _
  linarith only [her, hr, hg, hs]

end PseudoPrime.LLS.PaperStatements
