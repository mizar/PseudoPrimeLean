/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison

/-! # Weighted sums for the principal Dirichlet character

The principal character selects precisely the indices coprime to its level.
Its logarithmic sum is the unsigned sum minus the common-factor correction.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For any level and cutoff, the real logarithmic sum of the principal
character is the unsigned Mangoldt sum minus the common-factor contribution.
The character is one on units and zero on nonunits; split the finite sum by
coprimality. This supplies the principal term in subgroup character averages. -/
theorem characterLogWeightedSum_one_re_eq (q : ℕ) (x : ℝ) :
    (characterLogWeightedSum x (1 : DirichletCharacter ℂ q)).re =
      logWeightedMangoldtSum x - commonFactorLogWeightedSum x q := by
  classical
  rw [characterLogWeightedSum, Complex.re_sum]
  trans ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q), logWeightedMangoldtTerm x n
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    rw [characterLogWeightedTerm]
    by_cases hn : Nat.Coprime n q
    · rw [ite_eq_left hn, MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn), mul_one,
        Complex.ofReal_re]
    · rw [ite_eq_right hn,
        MulChar.map_nonunit (1 : DirichletCharacter ℂ q)
          (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h)),
        mul_zero, Complex.zero_re]
  have hp :=
    Finset.sum_filter_add_sum_filter_not (s := Finset.Ioc 0 ⌊x⌋₊) (f := logWeightedMangoldtTerm x)
      (p := fun n => Nat.Coprime n q)
  unfold logWeightedMangoldtSum commonFactorLogWeightedSum
  linarith only [hp]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
