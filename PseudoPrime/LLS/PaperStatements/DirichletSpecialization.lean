/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.PaperStatements
public import PseudoPrime.LLS.Extensions.ArithmeticCoefficients
public import PseudoPrime.LLS.DirichletExplicitFormula
public import PseudoPrime.AnalyticNumberTheory.General.AnalyticMultiplicity
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import PseudoPrime.LLS.Extensions.GeneralLFunction.DirichletSpecialization

/-!
# Arithmetic specialization of general L-function data to Dirichlet characters

Degree-one data, finite sums, gamma endpoints and completed-zero multiplicities are compared.
The identities transfer arithmetic sums, RH and zero mass without requiring general admissibility.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For `x ≥ 1` and a positive integer below its cutoff, the logarithmic L-value weight
is nonnegative. The logarithms of the index and `x/n` are nonnegative.
Total division also covers the endpoints with zero logarithm. -/
private theorem logValueWeight_nonneg {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊) :
    0 ≤
      ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n) *
        (Real.log (x / n) / Real.log x) := by
  have h := Finset.mem_Ioc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h.1
  have hnx : (n : ℝ) ≤ x :=
    (by exact_mod_cast h.2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (zero_le_one.trans hx))
  have hl : 0 ≤ Real.log (x / n) := Real.log_nonneg ((one_le_div₀ hn0).mpr hnx)
  exact
    mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (mul_nonneg hn0.le (Real.log_natCast_nonneg n)))
      (div_nonneg hl (Real.log_nonneg hx))

/-- For any complex Dirichlet character and `x ≥ 1`, the norm of its logarithmic L-value
sum is at most the unsigned sum. Apply the extension's finite coefficient estimate to
degree-one data and use weight nonnegativity. This supplies the arithmetic upper comparison
for Theorem 1.5 without primitivity or GRH. -/
theorem norm_characterLogLValueSum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 1 ≤ x) : ‖characterLogLValueSum χ x‖ ≤ logLValueSum x := by
  let w : ℕ → ℝ := fun n ↦
    ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n) * (Real.log (x / n) / Real.log x)
  have h :=
    Extensions.GeneralLFunction.norm_finiteWeightedSum_le_of_bound
      (Extensions.GeneralLFunction.ofDirichletCharacter χ)
      (Extensions.GeneralLFunction.ofDirichletCharacter_mangoldtCoefficient_norm_le χ)
      (Finset.Ioc 0 ⌊x⌋₊) w
  have hs : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, |w n|) = logLValueSum x := by
    apply Finset.sum_congr rfl
    intro n hn
    exact abs_of_nonneg (logValueWeight_nonneg hx hn)
  change
    ‖(Extensions.GeneralLFunction.ofDirichletCharacter χ).logValueSum x‖ ≤
      1 * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, |w n| at h
  simpa only [Extensions.GeneralLFunction.ofDirichletCharacter_logValueSum, one_mul, hs] using h

end PseudoPrime.LLS.PaperStatements
