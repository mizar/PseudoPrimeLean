/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleGammaCharacterBounds
public import PseudoPrime.LLS.QuadraticExcludedBudget
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PairedEulerExcludedBounds

/-! # Paired Euler savings with a combined quadratic exclusion budget -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Combine two real-axis Euler weights before charging excluded prime powers.
The parameters are two exponents and the coefficient of the logarithmic term.
This weight retains both savings from the signed two-pole zero-mass comparison. -/
noncomputable def pairedEulerPrefixWeight (σ τ c : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ +
    c * Real.log n * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ

/-- For nonnegative logarithmic coefficient, the combined Euler weight is
nonnegative at every natural index. Each Mangoldt, logarithm and power factor has
the required sign. This permits the quadratic structural exclusion estimate. -/
theorem pairedEulerPrefixWeight_nonneg (σ τ : ℝ) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ pairedEulerPrefixWeight σ τ c n := by
  exact
    add_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ))
      (div_nonneg
        (mul_nonneg (mul_nonneg hc (Real.log_natCast_nonneg n))
          ArithmeticFunction.vonMangoldt_nonneg)
        (Real.rpow_nonneg (Nat.cast_nonneg n) τ))

/-- If the Mangoldt value vanishes, the combined Euler weight vanishes for any
real parameters. This discharges the support premise in the exact defect identity. -/
theorem pairedEulerPrefixWeight_eq_zero_of_mangoldt_eq_zero (σ τ c : ℝ) {n : ℕ}
    (hn : ArithmeticFunction.vonMangoldt n = 0) : pairedEulerPrefixWeight σ τ c n = 0 := by
  simp only [pairedEulerPrefixWeight, hn, zero_div, mul_zero, add_zero]

/-- For any finite support, combine the ordinary and logarithmic paired Euler
prefixes into one weighted sum. Distribute finite sums and multiply algebraically.
This avoids bounding the two excluded-support costs separately. -/
theorem paired_euler_prefixes_eq_weight {q : ℕ} (χ : DirichletCharacter ℂ q) (σ τ c : ℝ)
    (S : Finset ℕ) :
    (∑ n ∈ S, DirichletLFunction.realPairedEulerTerm χ σ n) +
        c * (∑ n ∈ S, Real.log n * DirichletLFunction.realPairedEulerTerm χ τ n) =
      ∑ n ∈ S, (1 + (χ n).re) * pairedEulerPrefixWeight σ τ c n := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only [DirichletLFunction.realPairedEulerTerm, pairedEulerPrefixWeight]
  ring

end PseudoPrime.AnalyticNumberTheory.Arithmetic
