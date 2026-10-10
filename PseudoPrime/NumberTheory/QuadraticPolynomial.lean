/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Tactic.LinearCombination

/-!
# Quadratic polynomial factorization by the discriminant

Classify monic quadratic polynomials by nonsquare, zero, and nonzero square
discriminants. The two square cases require characteristic different from two.
These factorizations provide the polynomial input to quadratic prime splitting.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Over a field, `X² - bX - a` has degree two for arbitrary `a` and `b`.
Apply its monic-degree certificate. This supplies the degree hypothesis for the
root criterion used to prove irreducibility. -/
private theorem quadratic_natDegree {F : Type} [Field F] (a b : F) :
    (Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X - Polynomial.C a).natDegree = 2 := by
  simpa only [map_neg, sub_eq_add_neg] using
    (Polynomial.isMonicOfDegree_sub_add_two b (-a)).natDegree_eq

/-- If the discriminant of a monic quadratic is nonsquare, the polynomial is irreducible.
A root would express the discriminant as a square; the degree-two root criterion then
proves irreducibility. This identifies the inert case over finite fields. -/
theorem quadratic_irreducible_of_nonsquare {F : Type} [Field F] (a b : F)
    (hn : ¬IsSquare (b ^ 2 + 4 * a)) :
    Irreducible (Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X - Polynomial.C a) := by
  apply
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      (by
        rw [quadratic_natDegree]; exact Finset.mem_Icc.mpr ⟨by decide, by decide⟩)
  intro x hx
  have he : x ^ 2 - b * x - a = 0 := by
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C] using hx
  apply hn
  refine ⟨2 * x - b, ?_⟩
  linear_combination -4 * he

/-- If `r² - br - a = 0` in a field, `X² - bX - a` factors with roots `r` and `b - r`.
Eliminate `a` using the root equation and expand the product. This also applies in
characteristic two and supplies the factorization in both square-discriminant cases. -/
private theorem quadratic_linear_factors_of_root {F : Type} [Field F] (a b r : F)
    (hr : r ^ 2 - b * r - a = 0) :
    Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X - Polynomial.C a =
      (Polynomial.X - Polynomial.C r) * (Polynomial.X - Polynomial.C (b - r)) := by
  have ha : a = r ^ 2 - b * r := (sub_eq_zero.mp hr).symm
  rw [ha]
  simp only [map_sub, map_pow, map_mul]
  ring

/-- A root `r` of `X² - bX - a` makes `b² + 4a` the square of `r - (b - r)`.
Expand this identity using the root equation. It distinguishes equal roots from
distinct roots in the discriminant factorization proofs. -/
private theorem quadratic_discr_eq_root_difference {F : Type} [Field F] (a b r : F)
    (hr : r ^ 2 - b * r - a = 0) : b ^ 2 + 4 * a = (r - (b - r)) ^ 2 := by
  linear_combination -4 * hr

/-- For a field in which two is nonzero, a square `b² + 4a` gives a root of
`X² - bX - a`. Apply the quadratic formula to coefficients `1, -b, -a`.
This supplies the root used to construct repeated or distinct linear factors. -/
private theorem quadratic_exists_root_of_square {F : Type} [Field F] [NeZero (2 : F)] (a b : F)
    (h : IsSquare (b ^ 2 + 4 * a)) : ∃ r : F, r ^ 2 - b * r - a = 0 := by
  obtain ⟨s, hs⟩ := h
  have hd : discrim (1 : F) (-b) (-a) = s * s := by
    calc
      _ = b ^ 2 + 4 * a := by
        simp only [discrim]; ring
      _ = s * s := hs
  obtain ⟨r, hr⟩ := exists_quadratic_eq_zero (one_ne_zero : (1 : F) ≠ 0) ⟨s, hd⟩
  refine ⟨r, ?_⟩
  simpa only [one_mul, neg_mul, sub_eq_add_neg, pow_two] using hr

/-- In characteristic different from two, a monic quadratic with zero discriminant is
a squared linear factor. The quadratic formula gives a root, and the discriminant
identity forces the other root to coincide. This identifies the ramified factor type. -/
theorem quadratic_factorization_of_discr_zero {F : Type} [Field F] [NeZero (2 : F)] (a b : F)
    (hd : b ^ 2 + 4 * a = 0) :
    ∃ r : F,
      Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X - Polynomial.C a =
        (Polynomial.X - Polynomial.C r) ^ 2 := by
  obtain ⟨r, hr⟩ := quadratic_exists_root_of_square a b (hd.symm ▸ IsSquare.zero)
  have he : r = b - r :=
    sub_eq_zero.mp (sq_eq_zero_iff.mp ((quadratic_discr_eq_root_difference a b r hr).symm.trans hd))
  refine ⟨r, ?_⟩
  rw [quadratic_linear_factors_of_root a b r hr, ← he, pow_two]

/-- In characteristic different from two, a monic quadratic with nonzero square
discriminant factors into distinct linear polynomials. The quadratic formula supplies
a root, and the nonzero discriminant separates the two roots. This identifies the
split factor type over a finite field. -/
theorem quadratic_factorization_of_nonzero_square_discr {F : Type} [Field F] [NeZero (2 : F)]
    (a b : F) (hd : b ^ 2 + 4 * a ≠ 0) (hs : IsSquare (b ^ 2 + 4 * a)) :
    ∃ r s : F,
      r ≠ s ∧
        Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X - Polynomial.C a =
          (Polynomial.X - Polynomial.C r) * (Polynomial.X - Polynomial.C s) := by
  obtain ⟨r, hr⟩ := quadratic_exists_root_of_square a b hs
  refine ⟨r, b - r, ?_, quadratic_linear_factors_of_root a b r hr⟩
  intro he
  apply hd
  have hz : r - (b - r) = 0 := sub_eq_zero.mpr he
  rw [quadratic_discr_eq_root_difference a b r hr, hz, zero_pow (by decide)]

end PseudoPrime.NumberTheory
