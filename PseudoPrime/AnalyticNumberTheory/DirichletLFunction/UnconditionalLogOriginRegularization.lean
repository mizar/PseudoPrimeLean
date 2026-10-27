/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogErrorBound

/-! # Origin-regularized unconditional logarithmic explicit formulas -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a character, real scale, and complex zero parameter, subtract the genus
correction at two from the half-scale zero term. Its linear numerator at zero
cancels, while the correction series remains summable. This retains the exact
arithmetic formula and removes the origin derivative from the later remainder. -/
noncomputable def regularizedLogHalfZeroTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ)
    (ρ : ℂ) : ℂ :=
  completedLogHalfZeroTerm χ x ρ -
    (Real.log 2 : ℂ) *
      ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (1 / ((2 : ℂ) - ρ) + 1 / ρ))

/-- For primitive nonprincipal characters with nonprincipal inverse, modulus at
least two, and scale at least two, the regularized half-scale terms are summable.
Subtract the summable genus expansion at two from the original zero series. -/
theorem summable_regularizedLogHalfZeroTerm_unconditionally {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 2 ≤ x) : Summable (regularizedLogHalfZeroTerm χ x) := by
  exact
    (summable_completedLogHalfZeroTerm_unconditionally hq hp hne hinv hx).sub
      ((summable_completed_genus_terms_right hq hp hne hinv (s := 2)
            (by norm_num only [Complex.re_ofNat])).mul_left
        (Real.log 2 : ℂ))

/-- Under the primitive nonprincipal hypotheses and scale at least two, the
regularized zero sum equals the original half-scale sum minus the genus correction.
The unconditional centered Hadamard identity identifies its sum with the difference
of completed logarithmic derivatives at two and zero. -/
theorem tsum_regularizedLogHalfZeroTerm_eq_unconditionally {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 2 ≤ x) :
    (∑' ρ : ℂ, regularizedLogHalfZeroTerm χ x ρ) =
      (∑' ρ : ℂ, completedLogHalfZeroTerm χ x ρ) -
        (Real.log 2 : ℂ) * (logDeriv χ.completedLFunction 2 - logDeriv χ.completedLFunction 0) := by
  unfold regularizedLogHalfZeroTerm
  rw [(summable_completedLogHalfZeroTerm_unconditionally hq hp hne hinv hx).tsum_sub
      ((summable_completed_genus_terms_right hq hp hne hinv (s := 2)
            (by norm_num only [Complex.re_ofNat])).mul_left
        (Real.log 2 : ℂ)),
    tsum_mul_left, ←
    completed_centered_logDeriv_eq_genusSum_right hq hp hne hinv (s := 2)
      (by norm_num only [Complex.re_ofNat])]

/-- For a primitive nonprincipal character, its nonprincipal inverse, and `x > 2`,
the half-scale arithmetic sum equals the negative regularized zero sum plus the
corrected remainder. This exact unconditional identity preserves all multiplicities
and permits cancellation of the origin derivative before taking absolute values. -/
theorem characterLogWeightedSum_half_regularized_formula_unconditionally {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {x : ℝ} (hx : 2 < x) :
    Arithmetic.characterLogWeightedSum x χ - Arithmetic.characterLogWeightedSum (x / 2) χ =
      -(∑' ρ : ℂ, regularizedLogHalfZeroTerm χ x ρ) +
        (logarithmicHalfRemainder hne x -
          (Real.log 2 : ℂ) *
            (logDeriv χ.completedLFunction 2 - logDeriv χ.completedLFunction 0)) := by
  rw [characterLogWeightedSum_half_exact_zero_formula_unconditionally hq hp hne hinv hx,
    tsum_regularizedLogHalfZeroTerm_eq_unconditionally hq hp hne hinv hx.le]
  ring

/-- At a nonzero parameter, the regularized half-scale term has a numerator with
its linear term explicitly subtracted, and a regular reciprocal correction at two.
This algebraic identity exposes the quadratic cancellation needed near zero. -/
theorem regularizedLogHalfZeroTerm_eq_cancelled_kernel {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) {ρ : ℂ} (hρ : ρ ≠ 0) :
    regularizedLogHalfZeroTerm χ x ρ =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
        ((((1 - (2 : ℂ) ^ (-ρ)) * (x : ℂ) ^ ρ - (Real.log 2 : ℂ) * ρ) / ρ ^ 2) -
          (Real.log 2 : ℂ) / ((2 : ℂ) - ρ)) := by
  have he : ((Real.log 2 : ℂ) * ρ) / ρ ^ 2 = (Real.log 2 : ℂ) / ρ := by
    rw [pow_two, mul_div_mul_right _ _ hρ]
  dsimp only [regularizedLogHalfZeroTerm, completedLogHalfZeroTerm]
  rw [sub_div, he]
  ring

/-- For positive real `x`, the complex logarithm at `x/2` differs from that at `x`
by the real logarithm of two. Use the real logarithm identities on the positive axis.
This supplies the exact logarithmic differences in the origin residues. -/
theorem complex_log_half_eq_sub_log_two {x : ℝ} (hx : 0 < x) :
    Complex.log ((x / 2 : ℝ) : ℂ) = Complex.log (x : ℂ) - (Real.log 2 : ℂ) := by
  have hhalf : 0 < x / 2 := div_pos hx (by norm_num only)
  rw [← Complex.ofReal_log hhalf.le, ← Complex.ofReal_log hx.le,
    Real.log_div hx.ne' (by norm_num only), Complex.ofReal_sub]

/-- For primitive nonprincipal odd characters and positive scale, the regularized
remainder contains only the completed derivative at two, the gamma derivative at
zero, and trivial-zero corrections. The ordinary origin residue difference and
the completed-to-ordinary bridge cancel the completed derivative at zero. -/
theorem logarithmicHalfRemainder_regularized_of_odd {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (ho : χ.Odd) {x : ℝ} (hx : 0 < x) :
    logarithmicHalfRemainder hne x -
        (Real.log 2 : ℂ) * (logDeriv χ.completedLFunction 2 - logDeriv χ.completedLFunction 0) =
      (Real.log 2 : ℂ) * logDeriv (DirichletCharacter.gammaFactor χ) 0 -
            (Real.log 2 : ℂ) * logDeriv χ.completedLFunction 2 +
          logarithmicTrivialCorrection χ x -
        logarithmicTrivialCorrection χ (x / 2) := by
  have hhalf : 0 < x / 2 := div_pos hx (by norm_num only)
  have hbridge := (eventuallyEq_logDeriv_LFunction_zero_of_odd hp hne ho).eq_of_nhds
  dsimp only [logarithmicHalfRemainder]
  rw [dirichletLogResidueAt_zero_of_odd hne x ho, dirichletLogResidueAt_zero_of_odd hne (x / 2) ho,
    deriv_dirichletLogMellinZeroRegularization_zero_of_odd_eq hp hne ho hx,
    deriv_dirichletLogMellinZeroRegularization_zero_of_odd_eq hp hne ho hhalf,
    complex_log_half_eq_sub_log_two hx, hbridge]
  ring

/-- For primitive nonprincipal even characters and positive scale, the regularized
remainder contains the completed derivative at two, explicit logarithmic constants,
and trivial-zero corrections. Subtract the two cubic-pole residue formulas and
use the canonical even local factor to cancel the completed derivative at zero. -/
theorem logarithmicHalfRemainder_regularized_of_even {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (he : χ.Even) {x : ℝ} (hx : 0 < x) :
    logarithmicHalfRemainder hne x -
        (Real.log 2 : ℂ) * (logDeriv χ.completedLFunction 2 - logDeriv χ.completedLFunction 0) =
      -(Real.log 2 : ℂ) * logDeriv χ.completedLFunction 2 -
            (Real.log 2 : ℂ) * (Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) /
              2 -
            Complex.log (x : ℂ) * (Real.log 2 : ℂ) +
          (Real.log 2 : ℂ) ^ 2 / 2 +
          logarithmicTrivialCorrection χ x -
        logarithmicTrivialCorrection χ (x / 2) := by
  have hhalf : 0 < x / 2 := div_pos hx (by norm_num only)
  dsimp only [logarithmicHalfRemainder]
  rw [dirichletLogResidueAt_zero_of_even hne x he,
    dirichletLogResidueAt_zero_of_even hne (x / 2) he,
    iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_eq hp hne hx,
    iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_eq hp hne hhalf,
    complex_log_half_eq_sub_log_two hx, logDeriv_dirichletEvenZeroLocalFactor_zero hp hne]
  ring

/-- For a primitive nonprincipal odd character and its nonprincipal inverse, the
unconditional half-scale formula has an origin-free remainder. Only the completed
derivative at two, the fixed odd gamma derivative, and trivial-zero corrections
remain. Substitute the explicit odd remainder into the summable regularized formula. -/
theorem characterLogWeightedSum_half_regularized_formula_of_odd {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ho : χ.Odd)
    {x : ℝ} (hx : 2 < x) :
    Arithmetic.characterLogWeightedSum x χ - Arithmetic.characterLogWeightedSum (x / 2) χ =
      -(∑' ρ : ℂ, regularizedLogHalfZeroTerm χ x ρ) +
        ((Real.log 2 : ℂ) * logDeriv (DirichletCharacter.gammaFactor χ) 0 -
              (Real.log 2 : ℂ) * logDeriv χ.completedLFunction 2 +
            logarithmicTrivialCorrection χ x -
          logarithmicTrivialCorrection χ (x / 2)) := by
  rw [characterLogWeightedSum_half_regularized_formula_unconditionally hq hp hne hinv hx,
    logarithmicHalfRemainder_regularized_of_odd hp hne ho (by linarith only [hx] : 0 < x)]

/-- For a primitive nonprincipal even character and its nonprincipal inverse, the
unconditional half-scale formula has an explicit remainder without any derivative
at zero. It contains the completed derivative at two, elementary logarithms, and
trivial-zero corrections. Substitute the even origin cancellation into the formula. -/
theorem characterLogWeightedSum_half_regularized_formula_of_even {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (he : χ.Even)
    {x : ℝ} (hx : 2 < x) :
    Arithmetic.characterLogWeightedSum x χ - Arithmetic.characterLogWeightedSum (x / 2) χ =
      -(∑' ρ : ℂ, regularizedLogHalfZeroTerm χ x ρ) +
        (-(Real.log 2 : ℂ) * logDeriv χ.completedLFunction 2 -
              (Real.log 2 : ℂ) * (Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) /
                2 -
              Complex.log (x : ℂ) * (Real.log 2 : ℂ) +
            (Real.log 2 : ℂ) ^ 2 / 2 +
            logarithmicTrivialCorrection χ x -
          logarithmicTrivialCorrection χ (x / 2)) := by
  rw [characterLogWeightedSum_half_regularized_formula_unconditionally hq hp hne hinv hx,
    logarithmicHalfRemainder_regularized_of_even hp hne he (by linarith only [hx] : 0 < x)]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
