/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Rat.Cast.Order

/-! # Common-denominator polynomial rows for the Gaussian middle range -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A power-basis row stores integer numerators and one common denominator.
Consumers require positivity of the denominator when comparing polynomials. -/
public structure MiddleIntRow where
  den : ℤ
  nums : Array ℤ

/-- Read a numerator, with zero padding outside the stored entries. -/
@[expose]
public def MiddleIntRow.num (r : MiddleIntRow) (i : ℕ) : ℤ :=
  r.nums[i]?.getD 0

/-- Interpret the first `N+1` entries as a rational polynomial. -/
@[expose]
public noncomputable def MiddleIntRow.poly (r : MiddleIntRow) (N : ℕ) : Polynomial ℚ :=
  Polynomial.ofFn (N + 1) (fun i ↦ (r.num i.val : ℚ) / r.den)

/-- In-range coefficients use the common denominator of the row. -/
public theorem MiddleIntRow.poly_coeff (r : MiddleIntRow) {N i : ℕ} (hi : i ≤ N) :
    (r.poly N).coeff i = (r.num i : ℚ) / r.den := by
  exact Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_of_le hi)

/-- Check the common-denominator equalities using only integer products. -/
@[expose]
public def MiddleIntRow.matches (N : ℕ) (r s : MiddleIntRow) : Bool :=
  (List.range (N + 1)).all (fun i ↦ decide (r.num i * s.den = s.num i * r.den))

/-- A matching row certificate establishes equality of the rational polynomials. -/
public theorem MiddleIntRow.poly_eq_of_matches {N : ℕ} {r s : MiddleIntRow} (hr : r.den ≠ 0)
    (hs : s.den ≠ 0) (h : r.matches N s = true) : r.poly N = s.poly N := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  by_cases hi : i ≤ N
  · rw [r.poly_coeff hi, s.poly_coeff hi]
    apply (div_eq_div_iff (Int.cast_ne_zero.mpr hr) (Int.cast_ne_zero.mpr hs)).mpr
    have hc :=
      of_decide_eq_true ((List.all_eq_true.mp h) i (List.mem_range.mpr (Nat.lt_succ_of_le hi)))
    simpa only [Int.cast_mul] using congrArg (fun x : ℤ ↦ (x : ℚ)) hc
  · exact
      (Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.succ_le_of_lt (Nat.lt_of_not_ge hi))).trans
        (Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.succ_le_of_lt (Nat.lt_of_not_ge hi))).symm

/-- Add two rows by cross-multiplying their common denominators. -/
@[expose]
public def MiddleIntRow.add (N : ℕ) (r s : MiddleIntRow) : MiddleIntRow :=
  ⟨r.den * s.den, Array.ofFn fun i : Fin (N + 1) ↦ r.num i.val * s.den + s.num i.val * r.den⟩

/-- The cross-multiplied row represents the sum of the source polynomials. -/
public theorem MiddleIntRow.poly_add (N : ℕ) (r s : MiddleIntRow) (hr : r.den ≠ 0)
    (hs : s.den ≠ 0) : (r.add N s).poly N = r.poly N + s.poly N := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  rw [Polynomial.coeff_add]
  by_cases hi : i ≤ N
  · rw [MiddleIntRow.poly_coeff _ hi, r.poly_coeff hi, s.poly_coeff hi]
    simp only [MiddleIntRow.add, MiddleIntRow.num, Array.getElem?_ofFn,
      dite_eq_left (Nat.lt_succ_of_le hi), Option.getD_some, Int.cast_mul, Int.cast_add]
    rw [div_add_div _ _ (Int.cast_ne_zero.mpr hr) (Int.cast_ne_zero.mpr hs),
      mul_comm (r.den : ℚ) (s.nums[i]?.getD 0 : ℤ)]
  · have h := Nat.succ_le_of_lt (Nat.lt_of_not_ge hi)
    simp only [MiddleIntRow.poly, Polynomial.ofFn_coeff_eq_zero_of_ge _ h, zero_add]

/-- Multiply a row by an integer ratio without rational normalization. -/
@[expose]
public def MiddleIntRow.scale (r : MiddleIntRow) (a b : ℤ) : MiddleIntRow :=
  ⟨r.den * b, r.nums.map (a * ·)⟩

/-- Scaling integer numerators scales every zero-padded entry. -/
private theorem MiddleIntRow.num_scale (r : MiddleIntRow) (a b : ℤ) (i : ℕ) :
    (r.scale a b).num i = a * r.num i := by
  simp only [MiddleIntRow.scale, MiddleIntRow.num, Array.getElem?_map]
  cases r.nums[i]? <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some, mul_zero]

/-- Integer scaling represents multiplication by the corresponding constant polynomial. -/
public theorem MiddleIntRow.poly_scale (r : MiddleIntRow) (a b : ℤ) (N : ℕ) :
    (r.scale a b).poly N = Polynomial.C ((a : ℚ) / b) * r.poly N := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  rw [Polynomial.coeff_C_mul]
  by_cases hi : i ≤ N
  · rw [MiddleIntRow.poly_coeff _ hi, r.poly_coeff hi, r.num_scale]
    simp only [MiddleIntRow.scale, Int.cast_mul, div_mul_div_comm, mul_comm (b : ℚ)]
  · have h := Nat.succ_le_of_lt (Nat.lt_of_not_ge hi)
    simp only [MiddleIntRow.poly, Polynomial.ofFn_coeff_eq_zero_of_ge _ h, mul_zero]

/-- Differentiate a source row and keep one coefficient per target degree. -/
@[expose]
public def MiddleIntRow.deriv (r : MiddleIntRow) (N : ℕ) : MiddleIntRow :=
  ⟨r.den, Array.ofFn fun i : Fin (N + 1) ↦ ((i.val : ℤ) + 1) * r.num (i.val + 1)⟩

/-- Integer differentiation represents the derivative of the source polynomial
with one additional possible source coefficient. -/
public theorem MiddleIntRow.poly_deriv (r : MiddleIntRow) (N : ℕ) :
    (r.deriv N).poly N = (r.poly (N + 1)).derivative := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  rw [Polynomial.coeff_derivative]
  by_cases hi : i ≤ N
  · rw [MiddleIntRow.poly_coeff _ hi, r.poly_coeff (Nat.succ_le_succ hi)]
    simp only [MiddleIntRow.deriv, MiddleIntRow.num, Array.getElem?_ofFn,
      dite_eq_left (Nat.lt_succ_of_le hi), Option.getD_some, Int.cast_mul, Int.cast_add,
      Int.cast_natCast, Int.cast_one]
    rw [mul_div_assoc, mul_comm ((i : ℚ) + 1)]
  · have h := Nat.succ_le_of_lt (Nat.lt_of_not_ge hi)
    simp only [MiddleIntRow.poly, Polynomial.ofFn_coeff_eq_zero_of_ge _ h,
      Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.succ_le_succ h), zero_mul]

/-- Shift powers up by two, padding the constant and linear coefficients. -/
@[expose]
public def MiddleIntRow.mulX2 (r : MiddleIntRow) (N : ℕ) : MiddleIntRow :=
  ⟨r.den, Array.ofFn fun i : Fin (N + 3) ↦ if 2 ≤ i.val then r.num (i.val - 2) else 0⟩

/-- A two-place coefficient shift represents multiplication by `X^2`. -/
public theorem MiddleIntRow.poly_mulX2 (r : MiddleIntRow) (N : ℕ) :
    (r.mulX2 N).poly (N + 2) = Polynomial.X ^ 2 * r.poly N := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  rw [Polynomial.coeff_X_pow_mul']
  by_cases h : 2 ≤ i
  · rw [ite_eq_left h]
    by_cases hi : i ≤ N + 2
    · have hs : i - 2 ≤ N := by
        have hh := Nat.sub_le_sub_right hi 2
        exact hh
      rw [MiddleIntRow.poly_coeff _ hi, r.poly_coeff hs]
      simp only [MiddleIntRow.mulX2, MiddleIntRow.num, Array.getElem?_ofFn,
        dite_eq_left (Nat.lt_succ_of_le hi), Option.getD_some, ite_eq_left h]
    · have hs : N < i - 2 := Nat.lt_sub_of_add_lt (Nat.lt_of_not_ge hi)
      simp only [MiddleIntRow.poly,
        Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.succ_le_of_lt (Nat.lt_of_not_ge hi)),
        Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.succ_le_of_lt hs)]
  · rw [ite_eq_right h]
    have hi : i ≤ N + 2 := (Nat.le_of_lt (Nat.lt_of_not_ge h)).trans (Nat.le_add_left 2 N)
    rw [MiddleIntRow.poly_coeff _ hi]
    simp only [MiddleIntRow.mulX2, MiddleIntRow.num, Array.getElem?_ofFn,
      dite_eq_left (Nat.lt_succ_of_le hi), Option.getD_some, ite_eq_right h, Int.cast_zero,
      zero_div]

/-- A zero entry above the degree limit does not change the row polynomial. -/
public theorem MiddleIntRow.poly_succ_of_zero (r : MiddleIntRow) (N : ℕ) (h : r.num (N + 1) = 0) :
    r.poly (N + 1) = r.poly N := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  by_cases hi : i ≤ N
  · rw [r.poly_coeff (hi.trans (Nat.le_succ N)), r.poly_coeff hi]
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt (Nat.lt_of_not_ge hi)) with he | he
    · subst i
      rw [r.poly_coeff le_rfl, h, Int.cast_zero, zero_div]
      exact (Polynomial.ofFn_coeff_eq_zero_of_ge _ le_rfl).symm
    · simp only [MiddleIntRow.poly, Polynomial.ofFn_coeff_eq_zero_of_ge _ he.le,
        Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.succ_le_of_lt he)]

end PseudoPrime.PrimeTestBounds.MillerRabin
