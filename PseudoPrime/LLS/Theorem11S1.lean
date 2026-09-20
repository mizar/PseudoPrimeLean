/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import PseudoPrime.AnalyticNumberTheory.RiemannXi.HadamardLimit
import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogLevelChange
import PseudoPrime.LLS.Statement

/-!
# The final contradiction in LLS Theorem 1.1 S1

This file separates the analytic bounds and the explicit real-variable comparison in Section 3.1 of
Lamzouri--Li--Soundararajan. Their incompatibility gives the
character-specialized statement `llsTheorem11S1Character` without any additional analytic reasoning.
-/

namespace PseudoPrime.LLS

/-- The square root `log q + B(q)` of the search radius used in LLS Part 1. -/
noncomputable def llsTheorem11S1RadiusRoot (q : ℕ) : ℝ :=
  Real.log q + llsCorrectionTerm q

/-- The lower bound denoted `lower2` in Section 3.1 of the LLS paper. -/
noncomputable def llsTheorem11S1LowerBound (q : ℕ) : ℝ :=
  let y := llsTheorem11S1RadiusRoot q
  y ^ 2 -
    y *
      (2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass +
        2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q) -
    Real.log (2 * Real.pi) * Real.log (y ^ 2) -
    1 -
    2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass

/-- The final Part 1 upper bound in Section 3.1 of the LLS paper. -/
noncomputable def llsTheorem11S1UpperBound (q : ℕ) : ℝ :=
  llsTheorem11S1RadiusRoot q *
      (Real.log q + 2 * Real.log (Real.log q) + 9 / 5 - 2 * llsAuxiliaryTerm q) -
    39 / 20

/--
A hypothetical counterexample has no exceptional prime up to the LLS search radius.

The inputs are a level `q`, a complex Dirichlet character, and a prime.  The conclusion says that
every prime not dividing the level and lying in the search interval has character value `1`.
-/
def llsTheorem11S1NoSmallPrime {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ¬ℓ ∣ q → (ℓ : ℝ) ≤ (llsTheorem11S1RadiusRoot q) ^ 2 → χ ℓ = 1

/--
The upper bound for the primitive weighted sum after applying LLS Lemmas 2.2 and 2.3.

The definition is equation (3.3) with
`|Re B(χ̃)| ≤ log(conductor χ) / 2 + 2 / 5 - A(q)` substituted, at the Part 1 radius.
-/
noncomputable def llsTheorem11S1PrimitiveUpperBound {q : ℕ} (χ : DirichletCharacter ℂ q) : ℝ :=
  let x := (llsTheorem11S1RadiusRoot q) ^ 2
  (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log x) *
        (Real.log χ.conductor / 2 + 2 / 5 - llsAuxiliaryTerm q) +
      Real.log ((χ.conductor : ℝ) / Real.pi) * Real.log x / 2 -
    11 / 4

/--
The primitive-character analytic upper-bound responsibility in LLS Part 1.

For a hypothetical counterexample, Lemmas 2.2--2.4 must bound the real part of the primitive
weighted sum by `llsTheorem11S1PrimitiveUpperBound`.  The no-small-prime hypothesis is included
because
Lemma 2.4 and the weighted estimate use it when deriving the `A(q)` contribution.
-/
def llsTheorem11S1PrimitiveUpperBounds : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q →
      χ ≠ 1 →
      llsTheorem11S1NoSmallPrime χ →
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
            χ.primitiveCharacter).re ≤
        llsTheorem11S1PrimitiveUpperBound χ

/-- The upper bound for the original character before the final Section 3.1 simplification. -/
noncomputable def llsTheorem11S1ComparisonUpperBound {q : ℕ} (χ : DirichletCharacter ℂ q) : ℝ :=
  llsTheorem11S1PrimitiveUpperBound χ +
    (1 / 2 : ℝ) * (q / χ.conductor).primeFactors.card *
      (Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) ^ 2

/--
The primitive upper bound and equation (3.2) give an upper bound for the original character.

The inputs are the analytic primitive bound and a hypothetical counterexample.  The conclusion
is the unsimplified upper bound whose remaining reduction to `llsTheorem11S1UpperBound` is purely
real-variable arithmetic and belongs to the numerical-separation layer.
-/
theorem characterLogWeightedSum_re_le_comparisonUpper
    (hprimitive : llsTheorem11S1PrimitiveUpperBounds) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) (hχ : χ ≠ 1)
    (hsmall : llsTheorem11S1NoSmallPrime χ) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
          χ).re ≤
      llsTheorem11S1ComparisonUpperBound χ := by
  have hqone : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hy : 0 < llsTheorem11S1RadiusRoot q := by
    exact add_pos_of_pos_of_nonneg (Real.log_pos hqone) (llsCorrectionTerm_nonneg q)
  have hcomparison :=
    AnalyticNumberTheory.Arithmetic.norm_characterLogWeightedSum_sub_primitive_le
      ((llsTheorem11S1RadiusRoot q) ^ 2) χ (sq_pos_of_pos hy)
  have hre :=
    Complex.re_le_norm
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
          χ -
        AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
          χ.primitiveCharacter)
  have hprimitiveUpper := hprimitive q χ hq hχ hsmall
  rw [llsTheorem11S1ComparisonUpperBound]
  calc
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
            χ).re =
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
                χ -
              AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
                ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter).re +
          (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
              ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter).re :=
      by
      rw [Complex.sub_re]
      ring
    _ ≤
        ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
                χ -
              AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
                ((llsTheorem11S1RadiusRoot q) ^ 2) χ.primitiveCharacter‖ +
          llsTheorem11S1PrimitiveUpperBound χ :=
      add_le_add hre hprimitiveUpper
    _ ≤
        llsTheorem11S1PrimitiveUpperBound χ +
          (1 / 2 : ℝ) * (q / χ.conductor).primeFactors.card *
            (Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) ^ 2 :=
      by linarith only [hcomparison]

/--
The analytic output needed from LLS Lemmas 2.1--2.4 and the primitive-character comparison.

For a nontrivial character at level `q ≥ 3000` with no small exceptional prime, the proposition
requires a real witness `s` between the two Section 3.1 expressions. The intended witness is the
real part of the weighted sum, but this abstract interface does not assert that equality.
-/
def llsTheorem11S1AnalyticBounds : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q →
      χ ≠ 1 →
      llsTheorem11S1NoSmallPrime χ →
      ∃ s : ℝ, llsTheorem11S1LowerBound q ≤ s ∧ s ≤ llsTheorem11S1UpperBound q

/--
The lower-bound responsibility in LLS Part 1.

For a hypothetical counterexample, Lemma 2.1 and the logarithmic estimate in Lemma 3.1 give the
explicit lower bound `lower2` for the real part of the character weighted sum.
-/
def llsTheorem11S1WeightedLowerBounds : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q →
      χ ≠ 1 →
      llsTheorem11S1NoSmallPrime χ →
      llsTheorem11S1LowerBound q ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
            χ).re

/--
The algebraic and numerical simplification of the comparison upper bound.

This includes the conductor monotonicity and elementary estimates in lines 787--795 of the LLS
v3 source.  It is independent of RH, GRH, explicit formulae, and character sum evaluation.
-/
def llsTheorem11S1ComparisonUpperSimplification : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q → llsTheorem11S1ComparisonUpperBound χ ≤ llsTheorem11S1UpperBound q

/--
The staged lower, primitive upper, and numerical simplification bounds give the analytic sandwich.

The witness is the real part of `S(X, χ)` itself.  The lower side is supplied directly, while the
upper side first passes through the primitive character using equation (3.2), then through the
purely numerical comparison bound.
-/
theorem llsTheorem11S1AnalyticBounds_of_staged_bounds (hlower : llsTheorem11S1WeightedLowerBounds)
    (hprimitive : llsTheorem11S1PrimitiveUpperBounds)
    (hsimplify : llsTheorem11S1ComparisonUpperSimplification) : llsTheorem11S1AnalyticBounds := by
  intro q _ χ hq hχ hsmall
  refine
    ⟨(AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((llsTheorem11S1RadiusRoot q) ^ 2)
          χ).re,
      hlower q χ hq hχ hsmall, ?_⟩
  exact
    (characterLogWeightedSum_re_le_comparisonUpper hprimitive χ hq hχ hsmall).trans
      (hsimplify q χ hq)

/--
The purely real-variable and numerical part of the final LLS Part 1 comparison.

For every level in the theorem's range, the explicit upper expression is strictly smaller than
the explicit lower expression. This proposition expresses the numerical separation needed by the
final contradiction.
-/
def llsTheorem11S1NumericalSeparation : Prop :=
  ∀ q : ℕ, 3000 ≤ q → llsTheorem11S1UpperBound q < llsTheorem11S1LowerBound q

/--
Analytic counterexample bounds and their numerical separation imply the LLS character bound.

The proof negates the desired prime, converts that negation into `llsTheorem11S1NoSmallPrime`,
obtains
the weighted-sum sandwich, and contradicts the strict separation.  This is the final logical
composition step of LLS Theorem 1.1, Part 1.
-/
theorem llsTheorem11S1Character_of_bounds (hanalytic : llsTheorem11S1AnalyticBounds)
    (hnumeric : llsTheorem11S1NumericalSeparation) : llsTheorem11S1Character := by
  intro q _ χ hq hχ
  by_contra hcounterexample
  have hsmall : llsTheorem11S1NoSmallPrime χ := by
    intro ℓ hℓprime hℓndvd hℓle
    by_contra hℓvalue
    exact hcounterexample ⟨ℓ, hℓprime, hℓndvd, hℓvalue, hℓle⟩
  obtain ⟨s, hlower, hupper⟩ := hanalytic q χ hq hχ hsmall
  exact (not_le_of_gt (hnumeric q hq)) (hlower.trans hupper)

/--
All four staged Part 1 responsibilities together imply the character-specialized LLS theorem.

This theorem is the integration point for the lower explicit formula, the primitive upper bound,
the comparison simplification, and the final numerical separation.
-/
theorem llsTheorem11S1Character_of_staged_bounds (hlower : llsTheorem11S1WeightedLowerBounds)
    (hprimitive : llsTheorem11S1PrimitiveUpperBounds)
    (hsimplify : llsTheorem11S1ComparisonUpperSimplification)
    (hseparate : llsTheorem11S1NumericalSeparation) : llsTheorem11S1Character :=
  llsTheorem11S1Character_of_bounds
    (llsTheorem11S1AnalyticBounds_of_staged_bounds hlower hprimitive hsimplify) hseparate

end PseudoPrime.LLS
