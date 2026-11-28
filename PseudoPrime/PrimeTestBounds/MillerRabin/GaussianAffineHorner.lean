/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.OfFn
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectCurvatureRat
import Mathlib.Tactic.Ring

/-! # Integer Horner substitution for an affine polynomial coordinate -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Interpret ascending power coefficients through the polynomial Horner rule. -/
private noncomputable def rowPolynomial (q : List ℤ) : Polynomial ℤ :=
  q.foldr (fun c rest ↦ Polynomial.C c + Polynomial.X * rest) 0

/-- Compute the coefficients of a linear multiple, carrying the preceding
coefficient from the previous degree. -/
private def affineTail (a w : ℤ) : List ℤ → ℤ → List ℤ
  | [], prev => [w * prev]
  | c :: cs, prev => (a * c + w * prev) :: affineTail a w cs c

/-- One Horner step multiplies by the affine coordinate and adds a constant. -/
private def affineStep (a w c : ℤ) : List ℤ → List ℤ
  | [] => [c]
  | q :: qs => (c + a * q) :: affineTail a w qs q

/-- The tail recurrence represents the corresponding linear multiple. -/
private theorem affine_tail_poly (a w : ℤ) (cs : List ℤ) (prev : ℤ) :
    rowPolynomial (affineTail a w cs prev) =
      Polynomial.C (w * prev) +
        (Polynomial.C a + Polynomial.C w * Polynomial.X) * rowPolynomial cs := by
  induction cs generalizing prev with
  | nil =>
    simp only [affineTail, rowPolynomial, List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
  | cons c cs
    ih =>
    change
      Polynomial.C (a * c + w * prev) + Polynomial.X * rowPolynomial (affineTail a w cs c) =
        Polynomial.C (w * prev) +
          (Polynomial.C a + Polynomial.C w * Polynomial.X) *
            (Polynomial.C c + Polynomial.X * rowPolynomial cs)
    rw [ih]
    simp only [Polynomial.C_add, Polynomial.C_mul]
    ring

/-- One Horner step represents exact substitution into the affine variable. -/
private theorem affine_step_poly (a w c : ℤ) (cs : List ℤ) :
    rowPolynomial (affineStep a w c cs) =
      Polynomial.C c + (Polynomial.C a + Polynomial.C w * Polynomial.X) * rowPolynomial cs := by
  cases cs with
  | nil =>
    simp only [affineStep, rowPolynomial, List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
  | cons q
    qs =>
    change
      Polynomial.C (c + a * q) + Polynomial.X * rowPolynomial (affineTail a w qs q) =
        Polynomial.C c +
          (Polynomial.C a + Polynomial.C w * Polynomial.X) *
            (Polynomial.C q + Polynomial.X * rowPolynomial qs)
    rw [affine_tail_poly]
    simp only [Polynomial.C_add, Polynomial.C_mul]
    ring

/-- Substitute an integer affine coordinate in an ascending integer power row.
The construction uses only integer products by the two coordinate numerators. -/
public def integerAffineHorner (a w : ℤ) (q : List ℤ) : List ℤ :=
  q.foldr (affineStep a w) []

/-- The Horner row computes the integer polynomial evaluated in the affine coordinate. -/
private theorem integer_affine_poly (a w : ℤ) (q : List ℤ) :
    rowPolynomial (integerAffineHorner a w q) =
      (rowPolynomial q).comp (Polynomial.C a + Polynomial.C w * Polynomial.X) := by
  induction q with
  | nil => simp only [integerAffineHorner, rowPolynomial, List.foldr_nil, Polynomial.zero_comp]
  | cons c cs
    ih =>
    change
      rowPolynomial (affineStep a w c (integerAffineHorner a w cs)) =
        (Polynomial.C c + Polynomial.X * rowPolynomial cs).comp _
    rw [affine_step_poly, ih, Polynomial.add_comp, Polynomial.C_comp, Polynomial.mul_comp,
      Polynomial.X_comp]

/-- Read the coefficients of an integer row through its polynomial representation. -/
private theorem row_poly_coeff (q : List ℤ) (i : ℕ) : (rowPolynomial q).coeff i = q[i]?.getD 0 := by
  induction q generalizing i with
  | nil =>
    simp only [rowPolynomial, List.foldr_nil, Polynomial.coeff_zero, List.getElem?_nil,
      Option.getD_none]
  | cons c cs ih =>
    cases i with
    | zero =>
      change (Polynomial.C c + Polynomial.X * rowPolynomial cs).coeff 0 = _
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_mul_zero,
        add_zero, List.getElem?_cons_zero, Option.getD_some]
    | succ i =>
      change (Polynomial.C c + Polynomial.X * rowPolynomial cs).coeff (i + 1) = _
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_succ, Polynomial.coeff_X_mul, zero_add,
        ih, List.getElem?_cons_succ]

/-- The affine Horner transformation preserves the number of coefficients. -/
public theorem integer_affine_horner_length (a w : ℤ) (q : List ℤ) :
    (integerAffineHorner a w q).length = q.length := by
  have htail (s : List ℤ) (p : ℤ) : (affineTail a w s p).length = s.length + 1 := by
    induction s generalizing p with
    | nil => rfl
    | cons z zs ih => simp only [affineTail, List.length_cons, ih]
  have hstep (c : ℤ) (s : List ℤ) : (affineStep a w c s).length = s.length + 1 := by
    cases s with
    | nil => rfl
    | cons z zs => simp only [affineStep, List.length_cons, htail]
  induction q with
  | nil => rfl
  | cons z zs
    ih =>
    change (affineStep a w z (integerAffineHorner a w zs)).length = zs.length + 1
    rw [hstep, ih]

/-- An integer list representing a polynomial supplies the affine coefficients
through the Horner recurrence. -/
public theorem integer_affine_horner_coeff (a w : ℤ) (q : List ℤ) (i : ℕ) {P : Polynomial ℤ}
    (hP : ∀ j, P.coeff j = q[j]?.getD 0) :
    (integerAffineHorner a w q)[i]?.getD 0 =
      (P.comp (Polynomial.C a + Polynomial.C w * Polynomial.X)).coeff i := by
  have h : rowPolynomial q = P := by
    ext j
    rw [row_poly_coeff, hP]
  rw [← row_poly_coeff, integer_affine_poly, h]

/-- Apply the integer Horner recurrence to a zero-padded power row. -/
@[expose]
public def gaussianFastAffineRow (N : ℕ) (a w : ℤ) (q : ℕ → ℤ) : Array ℤ :=
  (integerAffineHorner a w (List.ofFn (fun i : Fin (N + 1) ↦ q i.val))).toArray

/-- The Horner and binomial algorithms compute exactly the same integer
affine row. Either may be used in the fixed-point certificate. -/
public theorem gaussian_fast_affine_eq (N : ℕ) (a w : ℤ) (q : ℕ → ℤ) :
    gaussianFastAffineRow N a w q = gaussianAffineIntRow N a w q := by
  let f := fun i : Fin (N + 1) ↦ q i.val
  let P : Polynomial ℤ := Polynomial.ofFn (N + 1) f
  let Q := P.map (Int.castRingHom ℚ)
  have hP (j : ℕ) : P.coeff j = (List.ofFn f)[j]?.getD 0 := by
    by_cases hj : j < N + 1
    · simp only [P, Polynomial.ofFn_coeff_eq_val_of_lt _ hj, List.getElem?_ofFn, dite_eq_left hj,
        Option.getD_some]
    · simp only [P, Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hj), List.getElem?_ofFn,
        dite_eq_right hj, Option.getD_none]
  have hd : Q.natDegree ≤ N :=
    Polynomial.natDegree_map_le.trans
      (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _))
  have hq (j : ℕ) (hj : j ≤ N) : (q j : ℚ) = (1 : ℚ) * Q.coeff j := by
    simp only [Q, Polynomial.coeff_map, Int.coe_castRingHom, hP, List.getElem?_ofFn,
      dite_eq_left (Nat.lt_succ_of_le hj), Option.getD_some, f, one_mul]
  apply Array.ext
  · simp only [gaussianFastAffineRow, gaussianAffineIntRow, List.size_toArray,
      integer_affine_horner_length, List.length_ofFn, Array.size_ofFn]
  · intro i hi hj
    have hn : i ≤ N :=
      Nat.le_of_lt_succ (by simpa only [gaussianAffineIntRow, Array.size_ofFn] using hj)
    have h := gaussian_affine_int_coeff Q N a w 1 q hd hq hn
    simp only [Int.cast_one, one_mul] at h
    have hf :
      ((gaussianFastAffineRow N a w q)[i]?.getD 0 : ℚ) =
        (Q.comp (Polynomial.C (w : ℚ) * Polynomial.X + Polynomial.C (a : ℚ))).coeff i := by
      change ((integerAffineHorner a w (List.ofFn f)).toArray[i]?.getD 0 : ℚ) = _
      rw [List.getElem?_toArray, integer_affine_horner_coeff a w _ i hP]
      change (Int.castRingHom ℚ) ((P.comp _).coeff i) = _
      rw [← Polynomial.coeff_map]
      simp only [Q, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X, Int.coe_castRingHom, add_comm]
    apply (Int.cast_injective (α := ℚ))
    simpa only [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj, Option.getD_some] using
      hf.trans h.symm

/-- Clear the coordinate denominator and apply the faster integer substitution. -/
@[expose]
public def gaussianFastAffineRatio (N : ℕ) (a w d : ℤ) (q : ℕ → ℤ) : Array ℤ :=
  let dp := Array.ofFn (fun j : Fin (N + 1) ↦ d ^ j.val)
  let cleared := Array.ofFn (fun j : Fin (N + 1) ↦ q j.val * dp[N - j.val]?.getD 0)
  gaussianFastAffineRow N a w (fun j ↦ cleared[j]?.getD 0)

/-- The denominator-cleared Horner row agrees exactly with the affine certificate. -/
public theorem gaussian_fast_ratio_eq (N : ℕ) (a w d : ℤ) (q : ℕ → ℤ) :
    gaussianFastAffineRatio N a w d q = gaussianAffineRatioRow N a w d q := by
  unfold gaussianFastAffineRatio gaussianAffineRatioRow
  exact gaussian_fast_affine_eq N a w _

end PseudoPrime.PrimeTestBounds.MillerRabin
