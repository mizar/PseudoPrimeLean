/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogResidueLedger
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorLogDeriv

/-! # Exact logarithmic origin values for primitive characters -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For an even primitive nonprincipal character and `x > 0`, evaluate the
logarithmic residue at zero as the negative derivative of the completed logarithmic
derivative, its logarithmic endpoint term, and the explicit even gamma correction.
The canonical local factor supplies the trigamma constant, and the cubic Mellin pole
supplies the quadratic logarithm. This exact endpoint identity does not require GRH. -/
theorem log_residue_zero_even_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (he : χ.Even) {x : ℝ} (hx : 0 < x) :
    dirichletLogResidueAt hne x 0 =
      -deriv (logDeriv χ.completedLFunction) 0 -
          logDeriv χ.completedLFunction 0 * (Real.log x : ℂ) +
        ((Real.pi ^ 2 / 24 - (Real.log Real.pi + Real.eulerMascheroniConstant) / 2 * Real.log x -
              (Real.log x) ^ 2 / 2 :
            ℝ) :
          ℂ) := by
  rw [dirichletLogResidueAt_zero_of_even hne x he, iteratedDeriv_2_logEvenReg_zero hp hne hx,
    deriv_logDeriv_evenZeroFactor_zero hp hne, logDeriv_evenZeroLocalFactor_zero hp hne, ←
    Complex.ofReal_log hx.le, ← Complex.ofReal_log Real.pi_nonneg]
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

/-- For an odd character, the gamma logarithmic derivative at zero is the
explicit complex digamma special value. This retains the whole complex
constant needed by the exact logarithmic and reciprocal residue formulas. -/
theorem logDeriv_gammaFactor_zero_odd_eq {q : ℕ} {χ : DirichletCharacter ℂ q} (ho : χ.Odd) :
    logDeriv (DirichletCharacter.gammaFactor χ) 0 =
      -Complex.log (Real.pi : ℂ) / 2 - Complex.log 2 - (Real.eulerMascheroniConstant : ℂ) / 2 := by
  rw [gammaLogDeriv_odd_eq_digamma ho (by simpa only [zero_add] using Gamma.half_ne_neg_nat),
    zero_add, Complex.digamma_one_half]
  ring

/-- For an odd primitive nonprincipal character and `x > 0`, evaluate the
logarithmic residue at zero as the completed logarithmic derivative endpoint and its
derivative, plus the explicit odd gamma correction. Differentiate the Mellin
regularization and insert the digamma and trigamma special values. This retains the
complete complex endpoint needed by the logarithmic explicit formula without GRH. -/
theorem log_residue_zero_odd_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (ho : χ.Odd) {x : ℝ} (hx : 0 < x) :
    dirichletLogResidueAt hne x 0 =
      -deriv (logDeriv χ.completedLFunction) 0 -
          logDeriv χ.completedLFunction 0 * (Real.log x : ℂ) +
        ((Real.pi ^ 2 / 8 -
              (Real.log Real.pi / 2 + Real.log 2 + Real.eulerMascheroniConstant / 2) * Real.log x :
            ℝ) :
          ℂ) := by
  have hbridge :
    logDeriv χ.LFunction 0 =
      logDeriv χ.completedLFunction 0 - logDeriv (DirichletCharacter.gammaFactor χ) 0 :=
    (eventuallyEq_logDeriv_L_zero_of_odd hp hne ho).self_of_nhds
  have hl2 : Complex.log 2 = (Real.log 2 : ℂ) := by
    simpa only [Complex.ofReal_ofNat] using (Complex.ofReal_log (zero_le_two : (0 : ℝ) ≤ 2)).symm
  rw [dirichletLogResidueAt_zero_of_odd hne x ho, deriv_logMellinReg_zero_odd_eq hp hne ho hx,
    deriv_logDeriv_LFunction_zero_of_odd hp hne ho, hbridge, logDeriv_gammaFactor_zero_odd_eq ho, ←
    Complex.ofReal_log hx.le, ← Complex.ofReal_log Real.pi_nonneg, hl2]
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
