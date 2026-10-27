/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularFiniteZeroMass
public import PseudoPrime.LLS.TriangularArchimedeanBounds

/-! # Signed arithmetic formula for triangular absolute zero mass

Keep the character and inverse-character arithmetic sums on the left.
Only the two gamma integrals remain in addition to the conductor.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a nonzero real parameter the entire triangular transform is even.
Expand the exponential quotient away from zero and treat zero separately.
This identifies reflected vertical integrals without taking norms. -/
theorem triangularMellinFunction_neg {a : ℝ} (ha : a ≠ 0) (s : ℂ) :
    triangularMellinFunction a (-s) = triangularMellinFunction a s := by
  by_cases hs : s = 0
  · subst s
    rw [neg_zero]
  · rw [triangularMellinFunction_of_ne_zero ha (neg_ne_zero.mpr hs),
      triangularMellinFunction_of_ne_zero ha hs]
    simp only [mul_neg, neg_neg, div_neg]
    congr 1
    ring

end PseudoPrime.Analysis

namespace PseudoPrime.LLS.PaperStatements

/-- For every complex function, the alpha-18 reflected integral equals the
right-line integral. Substitute t with -t and use the even triangular transform.
No integrability premise is needed for this change of variables.
This preserves the arithmetic sign in the zero-mass formula. -/
theorem triangular18_reflectedIntegral_eq_right (f : ℂ → ℂ) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          f (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
            K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          f ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          f (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
            K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          f ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
  congr 1
  let F := fun t : ℝ ↦
    f ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
      K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have h (t : ℝ) :
    f (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) =
      F (-t) := by
    have hz : (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) = -(((9 / 16 : ℝ) : ℂ) + Complex.I * (-t)) := by
      simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    have hw :
      (((17 / 16 : ℝ) : ℂ) - Complex.I * t) = (((9 / 16 : ℝ) : ℂ) + Complex.I * (-t)) + 1 / 2 := by
      push_cast
      ring
    dsimp only [F]
    rw [hz, hw]
    simp only [Complex.ofReal_neg]
    exact
      congrArg (fun z : ℂ ↦ f ((((9 / 16 : ℝ) : ℂ) + Complex.I * (-t)) + 1 / 2) * z)
        (Analysis.triangularMellinFunction_neg (a := 18) (by norm_num only) _)
  calc
    _ = ∫ t : ℝ, F (-t) := MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h)
    _ = ∫ t : ℝ, F t := MeasureTheory.integral_neg_eq_self F MeasureTheory.volume
    _ = _ := by rfl

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.DirichletLFunction in
/-- For a nonprincipal character, the alpha-18 completed right integral equals
the negative scale-one arithmetic sum plus the gamma integral. Split the regular
logarithmic derivative and integrate its two integrable components.
This replaces a norm estimate by an exact arithmetic identity. -/
theorem triangular18_completed_rightIntegral_eq_arithmetic_add_gamma {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.completedLFunction ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      -(∑' n : ℕ, K.summand χ 1 n) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
              K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let A := fun t : ℝ ↦
    -logDeriv χ.LFunction ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
      K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let G := fun t : ℝ ↦
    logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
      K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have ha :=
    MellinKernel.integrable_arithmeticMellin_logDeriv K χ (x := 1) (c := 9 / 16) (by norm_num only)
      (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at ha
  have hg :=
    MellinKernel.integrable_gammaFactor_power_line K χ (x := 1) (c := 9 / 16) (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only)
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at hg
  change MeasureTheory.Integrable A at ha
  change MeasureTheory.Integrable G at hg
  have he (t : ℝ) :
    logDeriv χ.completedLFunction ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
        K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) =
      -A t + G t := by
    let s : ℂ := (((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2
    have hz : s = ((17 / 16 : ℝ) : ℂ) + Complex.I * t := by
      dsimp only [s]
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    have hr : 1 ≤ s.re := by
      rw [hz]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
      norm_num only
    have hp : 0 < s.re := zero_lt_one.trans_le hr
    have hd :=
      logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
        (AnalyticNumberTheory.DirichletLFunction.completedLFunction_ne_zero_of_one_le_re hne hr)
        (AnalyticNumberTheory.DirichletLFunction.gammaFactor_ne_zero_of_re_pos χ hp)
        (AnalyticNumberTheory.DirichletLFunction.analyticAt_gammaFactor_of_re_pos χ
            hp).differentiableAt
    dsimp only [A, G]
    change logDeriv χ.completedLFunction s * _ = _
    rw [hd]
    ring
  have hs :=
    MellinKernel.tsum_summand_eq_integral_logDeriv K χ (x := 1) (c := 9 / 16) (by norm_num only)
      (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at hs
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * _ =
      -(∑' n : ℕ, K.summand χ 1 n) + ((1 / (2 * Real.pi) : ℝ) : ℂ) * _
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he),
    MeasureTheory.integral_add (f := fun t : ℝ ↦ -A t) (g := G) ha.neg hg,
    MeasureTheory.integral_neg, mul_add]
  rw [hs]
  exact congrArg (fun z : ℂ ↦ z + ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, G t)) (mul_neg _ _)

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal GRH data of modulus at least two and nonprincipal
inverse, the scale-one arithmetic sums for the character and its inverse plus
the absolute zero mass equal 36 log(q) plus the two gamma integrals.
Reflect the ordinary Euler integral and retain both signed arithmetic sums.
This is the entry point for cancellation across a finite character family. -/
theorem triangular18_absoluteMass_signed_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    let G := fun ψ : DirichletCharacter ℂ q ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
    (∑' n : ℕ, K.summand χ 1 n) + (∑' n : ℕ, K.summand χ⁻¹ 1 n) +
        ((∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ : ℝ) : ℂ) =
      36 * Complex.log q + G χ + G χ⁻¹ := by
  have he := triangular18_absoluteMass_conductor_formula hq hGRH hp hne hinv
  dsimp only at he ⊢
  rw [triangular_weightedResidue_pole_eq_zero, add_zero, triangular18_reflectedIntegral_eq_right,
    triangular18_completed_rightIntegral_eq_arithmetic_add_gamma hinv] at he
  linear_combination he

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- For a finite family of primitive nonprincipal GRH characters of the same
modulus, sum the signed absolute-mass formulas before taking any norms.
The cardinality multiplies the exact conductor term; arithmetic and gamma terms
retain their signs. This is the finite-family interface for improved zero budgets. -/
theorem triangular18_sum_absoluteMass_signed_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (S : Finset (DirichletCharacter ℂ q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : ∀ (χ : DirichletCharacter ℂ q), χ ∈ S → χ.IsPrimitive)
    (hne : ∀ (χ : DirichletCharacter ℂ q), χ ∈ S → χ ≠ 1)
    (hinv : ∀ (χ : DirichletCharacter ℂ q), χ ∈ S → χ⁻¹ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    let G := fun ψ : DirichletCharacter ℂ q ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
    (∑ χ ∈ S,
        ((∑' n : ℕ, K.summand (χ : DirichletCharacter ℂ q) 1 n) + (∑' n : ℕ, K.summand χ⁻¹ 1 n) +
          ((∑' ρ : ℂ, ‖K.kernelZeroTerm (q := q) χ ρ‖ : ℝ) : ℂ))) =
      (S.card : ℂ) * (36 * Complex.log q) + ∑ χ ∈ S, (G χ + G χ⁻¹) := by
  dsimp only
  calc
    _ = ∑ χ ∈ S, (36 * Complex.log q + _ + _) :=
      Finset.sum_congr rfl
        (fun χ hχ ↦
          triangular18_absoluteMass_signed_formula hq hGRH (hp χ hχ) (hne χ hχ) (hinv χ hχ))
    _ = _ := by simp only [add_assoc, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal GRH data, the alpha-18 absolute zero mass is
at most 36 log(q) minus the character and inverse arithmetic real parts plus
110000. Shift each gamma integral to the central line and retain the signs
of both scale-one sums. This supplies a sharper signed comparison budget. -/
theorem triangular18_absoluteMass_le_signed_arithmetic {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤
      36 * Real.log q - (∑' n : ℕ, K.summand χ 1 n).re - (∑' n : ℕ, K.summand χ⁻¹ 1 n).re +
        110000 := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let G := fun ψ : DirichletCharacter ℂ q ↦
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
  have hg (ψ : DirichletCharacter ℂ q) : (G ψ).re ≤ 55000 := by
    have hn :=
      triangular18_gammaIntegral_norm_le_uniform ψ (b := 9 / 16) (x := 1) (by norm_num only)
        (by norm_num only) (le_refl _)
    simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at hn
    exact (Complex.re_le_norm (G ψ)).trans hn
  have he := triangular18_absoluteMass_signed_formula hq hGRH hp hne hinv
  change
    (∑' n : ℕ, K.summand χ 1 n) + (∑' n : ℕ, K.summand χ⁻¹ 1 n) +
        ((∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ : ℝ) : ℂ) =
      36 * Complex.log q + G χ + G χ⁻¹ at he
  rw [← Complex.natCast_log, ← Complex.ofReal_ofNat 36, ← Complex.ofReal_mul] at he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re] at hr
  change (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤ _
  linarith only [hr, hg χ, hg χ⁻¹]

end PseudoPrime.LLS.PaperStatements
