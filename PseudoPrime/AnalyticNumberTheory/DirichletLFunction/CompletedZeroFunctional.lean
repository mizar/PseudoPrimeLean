/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedZeroDistribution
public import PseudoPrime.Analysis.WeightedEvaluation

/-!
# Continuous test functions for completed-zero distribution

The Poisson-weighted Cayley zero series is a continuous linear functional on circle functions.
Its normalization by log q has uniformly bounded norm for sufficiently large moduli.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character of modulus at least two, with nonprincipal
inverse satisfying individual RH, evaluate each continuous complex circle function at
its Cayley zero points and sum with nonnegative Poisson weights. Summability of the weights
makes this a continuous complex linear functional. It connects zero moments to continuous
test functions without introducing a separate measure representation. -/
noncomputable def completedZeroFunctional {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) : C(Circle, ℂ) →L[ℂ] ℂ :=
  PseudoPrime.Analysis.weightedEval (completedZeroCayleyPoint hRH hp hinv)
    (completedZeroPoissonWeight χ) (completedZeroPoissonWeight_nonneg χ)
    (summable_completedZeroPoissonWeight hq hRH hp hne hinv)

/-- The completed-zero functional evaluates a circle function by its Poisson-weighted
Cayley zero series. This is its defining formula for primitive nonprincipal characters
under individual RH. It connects explicit zero sums to the linear functional. -/
theorem completedZeroFunctional_apply {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (f : C(Circle, ℂ)) :
    completedZeroFunctional hq hRH hp hne hinv f =
      ∑' ρ : CompletedZero χ,
        (completedZeroPoissonWeight χ ρ : ℂ) * f (completedZeroCayleyPoint hRH hp hinv ρ) :=
  rfl

/-- Under the hypotheses defining the completed-zero functional, its operator norm is
at most total Poisson mass. Apply the positive weighted-evaluation bound.
This controls uniform approximation errors for circle test functions. -/
theorem norm_completedZeroFunctional_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ‖completedZeroFunctional hq hRH hp hne hinv‖ ≤
      ∑' ρ : CompletedZero χ, completedZeroPoissonWeight χ ρ :=
  PseudoPrime.Analysis.norm_weightedEval_le _ _ _ _

/-- Under the hypotheses defining the completed-zero functional, the difference of
its values on two continuous circle functions has norm at most total Poisson mass times
their uniform distance. Use the general positive atomic error bound.
This passes moment estimates to uniformly approximated test functions. -/
theorem norm_completedZeroFunctional_sub_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (f g : C(Circle, ℂ)) :
    ‖completedZeroFunctional hq hRH hp hne hinv f - completedZeroFunctional hq hRH hp hne hinv g‖ ≤
      (∑' ρ : CompletedZero χ, completedZeroPoissonWeight χ ρ) * ‖f - g‖ :=
  PseudoPrime.Analysis.norm_weightedEval_sub_le _ _ _ _ _ _

/-- For all sufficiently large moduli, the completed-zero functional has operator norm
at most log q, uniformly over primitive nonprincipal characters with nonprincipal inverse
satisfying individual RH. Bound the Poisson mass by log q using its one-half logarithmic
main term and the error estimate with coefficient one half. This supplies a common bound
for the conductor-normalized functionals. -/
theorem exists_uniform_norm_completedZeroFunctional_le_log :
    ∃ Q : ℕ,
      ∃ hQ : 2 ≤ Q,
        ∀ (q : ℕ) [NeZero q],
          ∀ hq : Q ≤ q,
            ∀ (χ : DirichletCharacter ℂ q),
              ∀ hRH : GRH.DirichletRiemannHypothesis χ,
                ∀ hp : χ.IsPrimitive,
                  ∀ hne : χ ≠ 1,
                    ∀ hinv : χ⁻¹ ≠ 1,
                      ‖completedZeroFunctional (hQ.trans hq) hRH hp hne hinv‖ ≤ Real.log q := by
  obtain ⟨Q, hQ, hb⟩ :=
    exists_uniform_completedZeroPoissonSum_error_le_log (show (0 : ℝ) < 1 / 2 by norm_num only)
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  apply (norm_completedZeroFunctional_le (hQ.trans hq) hRH hp hne hinv).trans
  have h := (abs_le.mp (hb q hq χ hRH hp hne hinv)).2
  nlinarith only [h]

/-- When a continuous circle function equals the integer monomial of degree k, the
completed-zero functional equals the corresponding weighted Cayley zero sum.
Apply the evaluation formula pointwise. This exposes the proved moment estimates through
the continuous-function interface used for approximation. -/
theorem completedZeroFunctional_eq_CayleySum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℤ) (f : C(Circle, ℂ))
    (hf : ∀ p : Circle, f p = (p : ℂ) ^ k) :
    completedZeroFunctional hq hRH hp hne hinv f =
      ∑' ρ : CompletedZero χ, completedZeroCayleyZTerm hRH hp hinv k ρ := by
  rw [completedZeroFunctional_apply]
  apply tsum_congr
  intro ρ
  rw [hf]
  rfl

/-- The completed-zero functional divided by the positive conductor logarithm, for
primitive nonprincipal characters of modulus at least two with nonprincipal inverse
satisfying individual RH. This complex continuous linear functional is the normalized
weighted zero distribution; constant and nonconstant test functions have different limits. -/
noncomputable def normalizedCompletedZeroFunctional {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) : C(Circle, ℂ) →L[ℂ] ℂ :=
  (1 / (Real.log q : ℂ)) • completedZeroFunctional hq hRH hp hne hinv

/-- For all sufficiently large moduli, the normalized completed-zero functional has
operator norm at most one, uniformly over primitive nonprincipal characters with
nonprincipal inverse satisfying individual RH. Divide the logarithmic mass bound by
the positive logarithm. This uniform bound extends convergence from circle monomials
to continuous functions by approximation. -/
theorem exists_uniform_norm_normalizedCompletedZeroFunctional_le_one :
    ∃ Q : ℕ,
      ∃ hQ : 2 ≤ Q,
        ∀ (q : ℕ) [NeZero q],
          ∀ hq : Q ≤ q,
            ∀ (χ : DirichletCharacter ℂ q),
              ∀ hRH : GRH.DirichletRiemannHypothesis χ,
                ∀ hp : χ.IsPrimitive,
                  ∀ hne : χ ≠ 1,
                    ∀ hinv : χ⁻¹ ≠ 1,
                      ‖normalizedCompletedZeroFunctional (hQ.trans hq) hRH hp hne hinv‖ ≤ 1 := by
  obtain ⟨Q, hQ, hb⟩ := exists_uniform_norm_completedZeroFunctional_le_log
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  have hq2 : (2 : ℝ) ≤ q := Nat.cast_le.mpr (hQ.trans hq)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith only [hq2])
  rw [normalizedCompletedZeroFunctional, norm_smul, norm_div, norm_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hlog, one_div_mul_eq_div]
  exact (div_le_one hlog).mpr (hb q hq χ hRH hp hne hinv)

/-- For every nonzero integer degree, continuous circle monomial of that degree,
and epsilon > 0, sufficiently large moduli make the normalized completed-zero functional's
value have norm at most epsilon, uniformly over primitive nonprincipal characters with
nonprincipal inverse satisfying individual RH. Divide the proved Cayley moment estimate
by the positive conductor logarithm. This gives convergence on nonconstant monomials. -/
theorem exists_uniform_normalizedCompletedZeroFunctional_monomial_le {k : ℤ} (hk : k ≠ 0)
    (f : C(Circle, ℂ)) (hf : ∀ p : Circle, f p = (p : ℂ) ^ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      ∃ hQ : 2 ≤ Q,
        ∀ (q : ℕ) [NeZero q],
          ∀ hq : Q ≤ q,
            ∀ (χ : DirichletCharacter ℂ q),
              ∀ hRH : GRH.DirichletRiemannHypothesis χ,
                ∀ hp : χ.IsPrimitive,
                  ∀ hne : χ ≠ 1,
                    ∀ hinv : χ⁻¹ ≠ 1,
                      ‖normalizedCompletedZeroFunctional (hQ.trans hq) hRH hp hne hinv f‖ ≤ ε := by
  obtain ⟨Q, hQ, hb⟩ := exists_uniform_completedZeroCayleyZSum_le_log hk hε
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  have hq2 : (2 : ℝ) ≤ q := Nat.cast_le.mpr (hQ.trans hq)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith only [hq2])
  rw [normalizedCompletedZeroFunctional, smul_apply, smul_eq_mul,
    completedZeroFunctional_eq_CayleySum (hQ.trans hq) hRH hp hne hinv k f hf, norm_mul, norm_div,
    norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog, one_div_mul_eq_div]
  exact (div_le_iff₀ hlog).mpr (hb q hq χ hRH hp hne hinv)

/-- The completed-zero functional evaluated at the constant one function is the complex
cast of the real total Poisson mass. Simplify each weighted evaluation and commute
the real cast with the summable series. This identifies the constant test function. -/
theorem completedZeroFunctional_const_one {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    completedZeroFunctional hq hRH hp hne hinv (ContinuousMap.const Circle (1 : ℂ)) =
      (((∑' ρ : CompletedZero χ, completedZeroPoissonWeight χ ρ) : ℝ) : ℂ) := by
  rw [completedZeroFunctional_apply]
  simp only [ContinuousMap.const_apply, mul_one, ← Complex.ofReal_tsum]

/-- For every epsilon > 0, sufficiently large moduli make the normalized completed-zero
functional's value on the constant one function differ from one half by norm at most epsilon,
uniformly over primitive nonprincipal characters with nonprincipal inverse satisfying
individual RH. Express the constant value as real Poisson mass, subtract its logarithmic
main term, and divide by the positive logarithm. This supplies the constant moment
needed alongside the vanishing nonconstant monomials. -/
theorem exists_uniform_normalizedCompletedZeroFunctional_const_one_error_le {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      ∃ hQ : 2 ≤ Q,
        ∀ (q : ℕ) [NeZero q],
          ∀ hq : Q ≤ q,
            ∀ (χ : DirichletCharacter ℂ q),
              ∀ hRH : GRH.DirichletRiemannHypothesis χ,
                ∀ hp : χ.IsPrimitive,
                  ∀ hne : χ ≠ 1,
                    ∀ hinv : χ⁻¹ ≠ 1,
                      ‖normalizedCompletedZeroFunctional (hQ.trans hq) hRH hp hne hinv
                              (ContinuousMap.const Circle (1 : ℂ)) -
                            (1 / 2 : ℂ)‖ ≤
                        ε := by
  obtain ⟨Q, hQ, hb⟩ := exists_uniform_completedZeroPoissonSum_error_le_log hε
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  have hq2 : (2 : ℝ) ≤ q := Nat.cast_le.mpr (hQ.trans hq)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith only [hq2])
  rw [normalizedCompletedZeroFunctional, smul_apply, smul_eq_mul, completedZeroFunctional_const_one,
    one_div_mul_eq_div, ← Complex.ofReal_div,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by
      rw [Complex.ofReal_div, Complex.ofReal_one]; rfl,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [show
      (∑' ρ : CompletedZero χ, completedZeroPoissonWeight χ ρ) / Real.log q - 1 / 2 =
        ((∑' ρ : CompletedZero χ, completedZeroPoissonWeight χ ρ) - Real.log q / 2) / Real.log q
      by rw [sub_div, div_right_comm, div_self (ne_of_gt hlog)]]
  rw [abs_div, abs_of_pos hlog]
  exact (div_le_iff₀ hlog).mpr (hb q hq χ hRH hp hne hinv)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
