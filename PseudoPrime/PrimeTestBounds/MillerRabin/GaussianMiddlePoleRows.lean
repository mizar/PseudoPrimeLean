/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms

/-! # Integer certificates for the inverse transform of a squared kernel -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The sum and indexed representations give the same rational polynomial. -/
private theorem row_eq_profile (r : MiddleIntRow) (N : ℕ) :
    r.poly N = gaussianIntProfile N r.den r.num := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  simp only [gaussianIntProfile, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_range]
  by_cases hi : i < N + 1
  · rw [ite_eq_left hi]
    exact r.poly_coeff (Nat.le_of_lt_succ hi)
  · rw [ite_eq_right hi]
    exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi)

/-- Integer cross products identify the physical polynomial with the inverse
transform of the rational squared kernel, without evaluating rational coefficients. -/
public theorem MiddleIntRow.poly_eq_pole_profile (r p : MiddleIntRow) (N : ℕ) (hr : r.den ≠ 0)
    (hp : p.den ≠ 0)
    (hc :
      ∀ i : Fin (N + 1),
        r.num i.val * p.den ^ 2 * (i.val.factorial : ℤ) =
          r.den * middleSquareCoeff p.num (N - i.val)) :
    r.poly N = middlePoleProfile N (p.poly N) := by
  rw [row_eq_profile r N, row_eq_profile p N]
  exact
    middle_pole_profile_eq N p.den r.den p.num r.num hp hr (fun i hi ↦ hc ⟨i, Nat.lt_succ_of_le hi⟩)

end PseudoPrime.PrimeTestBounds.MillerRabin
