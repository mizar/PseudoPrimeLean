/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiberCoefficientBudget

/-! # A concrete prime threshold for the fixed finite-fiber energy scale -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The prime threshold P(u)=2^(2^u), specialized later to u=1388714689827.
The parameter keeps comparisons symbolic before substituting the large
closed exponent. No range below the threshold is enumerated. -/
noncomputable def explicitFiniteFiberPrimeThreshold (u : ℕ) : ℕ :=
  2 ^ (2 ^ u)

/-- The explicit prime threshold exceeds one for every symbolic parameter.
Compare the positive natural powers before substituting a closed tower. -/
theorem one_lt_explicit_finite_fiber_threshold (u : ℕ) :
    1 < explicitFiniteFiberPrimeThreshold u := by
  exact Nat.one_lt_pow (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2))) (by decide)

/-- Symbolic product budgets compare directly with the threshold P(u).
Unfold only while u remains a variable, so closed tower values are not
evaluated during later specialization to u=1388714689827. -/
theorem mul_power_lt_explicit_finite_fiber_threshold {A C a s B k u : ℕ} (hC : C ≤ 2 ^ (2 ^ B))
    (hA : A ^ a ≤ 2 ^ k) (hgap : B + s + k < u) :
    A ^ a * C ^ s < explicitFiniteFiberPrimeThreshold u := by
  exact mul_power_lt_double_exp_of_budget hC hA hgap

end PseudoPrime.NumberTheory.Heilbronn
