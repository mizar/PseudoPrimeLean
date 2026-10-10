/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Lucas.Spec
public import Mathlib.Data.Matrix.Reflection

/-!
# Binary Lucas evaluation in `ZMod`

The executable evaluator uses binary powering of the companion matrix.  The
ordinary recursive Lucas sequences remain the proof-side specification.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
The modular recurrence matrix [[P,-Q],[1,0]] for signed Lucas parameters.
Its powers encode consecutive U values and its trace gives V, enabling binary evaluation.
-/
def lucasCompanion (n : ℕ) (P Q : ℤ) : Matrix (Fin 2) (Fin 2) (ZMod n) :=
  !![(P : ZMod n), -(Q : ZMod n); 1, 0]

/--
Compute the kth power of the Lucas companion matrix by npowBinRec.
The result is a 2-by-2 matrix over ZMod n for any natural modulus and index.
The following correctness theorem connects binary execution with ordinary matrix powers.
-/
def lucasCompanionPowFast (n : ℕ) (P Q : ℤ) (k : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod n) :=
  npowBinRec k (lucasCompanion n P Q)

/--
For every n,P,Q,k, binary companion powering equals ordinary matrix power.
Induction uses the zero and successor equations of npowBinRec.
This allows matrix sequence identities to certify the executable evaluator.
-/
theorem lucasCompanionPowFast_eq_pow (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasCompanionPowFast n P Q k = lucasCompanion n P Q ^ k := by
  unfold lucasCompanionPowFast
  induction k with
  | zero => rw [npowBinRec_zero, pow_zero]
  | succ k ih => rw [npowBinRec_succ, pow_succ, ih]

/--
For every k, the full companion power at k+1 has rows
[U_{k+2}, -Q U_{k+1}] and [U_{k+1}, -Q U_k], interpreted in ZMod n.
Induction multiplies the matrix and applies the U recurrence entrywise.
The first column recovers U and the trace recovers V in the fast correctness proofs.
-/
theorem lucasCompanion_pow_succ (n : ℕ) (P Q : ℤ) :
    ∀ k : ℕ,
      lucasCompanion n P Q ^ (k + 1) =
        !![(lucasU P Q (k + 2) : ZMod n), -(Q : ZMod n) * (lucasU P Q (k + 1) : ZMod n);
          (lucasU P Q (k + 1) : ZMod n), -(Q : ZMod n) * (lucasU P Q k : ZMod n)] := by
  intro k
  induction k with
  | zero =>
    rw [Nat.zero_add, pow_one, lucasCompanion, lucasU_two, lucasU_one, lucasU_zero]
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, Matrix.vecCons]
    · simp only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, Matrix.vecCons]
    · simp only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, Matrix.vecCons]
    · simp only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, Matrix.vecCons]
  | succ k ih =>
    rw [show k + 1 + 1 = (k + 1) + 1 by rfl, pow_succ, ih]
    have hrec3 : lucasU P Q (3 + k) = P * lucasU P Q (2 + k) - Q * lucasU P Q (1 + k) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lucasU_succ_succ P Q (k + 1)
    have hrec2 : lucasU P Q (2 + k) = P * lucasU P Q (1 + k) - Q * lucasU P Q k := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lucasU_succ_succ P Q k
    have hrec3Z :
      (lucasU P Q (k + 1 + 2) : ZMod n) =
        (P : ZMod n) * (lucasU P Q (k + 1 + 1) : ZMod n) -
          (Q : ZMod n) * (lucasU P Q (k + 1) : ZMod n) := by
      have h := lucasU_succ_succ P Q (k + 1)
      simpa only [Int.cast_sub, Int.cast_mul] using congrArg (fun z : ℤ => (z : ZMod n)) h
    have hrec2Z :
      (lucasU P Q (k + 1 + 1) : ZMod n) =
        (P : ZMod n) * (lucasU P Q (k + 1) : ZMod n) - (Q : ZMod n) * (lucasU P Q k : ZMod n) := by
      have h := lucasU_succ_succ P Q k
      simpa only [Int.cast_sub, Int.cast_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        congrArg (fun z : ℤ => (z : ZMod n)) h
    rw [hrec3Z, hrec2Z]
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [neg_mul, lucasCompanion, Fin.zero_eta, Fin.isValue, Matrix.mul_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
        Fin.sum_univ_two, Matrix.cons_val_one, mul_one]
      ring
    · simp only [neg_mul, lucasCompanion, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.mul_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.sum_univ_two, mul_neg, mul_zero, add_zero, neg_inj]
      ring
    · simp only [neg_mul, lucasCompanion, Fin.mk_one, Fin.isValue, Fin.zero_eta, Matrix.mul_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
        Matrix.cons_val_zero, Fin.sum_univ_two, mul_one]
      ring
    · simp only [neg_mul, lucasCompanion, Fin.mk_one, Fin.isValue, Matrix.mul_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
        Fin.sum_univ_two, Matrix.cons_val_zero, mul_neg, mul_zero, add_zero, neg_inj]
      ring

/--
Four entries of a 2-by-2 matrix, stored without a matrix-indexing function.
The fields a,b,c,d are respectively the top-left, top-right, bottom-left and bottom-right entries.
No sequence invariant is required for arbitrary states; scalar multiplication and powering
provide the executable representation of the Lucas companion matrix.
-/
structure LucasScalarState (R : Type*) where
  a : R
  b : R
  c : R
  d : R

/-- Equality of all four entries gives equality of scalar states over any type.
Destructure both records and use constructor injectivity.
This extensionality rule reduces scalar algebra laws to entrywise equations. -/
@[ext]
theorem LucasScalarState.ext {x y : LucasScalarState R} (ha : x.a = y.a) (hb : x.b = y.b)
    (hc : x.c = y.c) (hd : x.d = y.d) : x = y := by
  cases x
  cases y
  simp only [mk.injEq] at *
  exact ⟨ha, hb, hc, hd⟩

/--
Multiply two four-entry matrix states over a semiring using the usual row-column sums.
The returned a,b,c,d entries represent the product without indexed matrix evaluation.
This operation is the multiplication used by scalar binary companion powering.
-/
def lucasScalarMul [Semiring R] (x y : LucasScalarState R) : LucasScalarState R :=
  { a := x.a * y.a + x.b * y.c
    b := x.a * y.b + x.b * y.d
    c := x.c * y.a + x.d * y.c
    d := x.c * y.b + x.d * y.d }

/--
Equip four-entry states over a semiring with lucasScalarMul as their multiplication.
The operation is ordinary 2-by-2 matrix multiplication in the scalar representation.
-/
instance lucasScalarMulInstance [Semiring R] : Mul (LucasScalarState R) :=
  ⟨lucasScalarMul⟩

/--
The identity scalar state (a,b,c,d)=(1,0,0,1) over a semiring.
This initializes binary powers and represents the identity companion-matrix power.
-/
def lucasScalarOne [Semiring R] : LucasScalarState R :=
  { a := 1, b := 0, c := 0, d := 1 }

/--
Use lucasScalarOne as the unit of four-entry states over a semiring.
Its matrix representation is the 2-by-2 identity used in binary powering.
-/
instance lucasScalarOneInstance [Semiring R] : One (LucasScalarState R) :=
  ⟨lucasScalarOne⟩

/-- Four-entry states form a monoid over a commutative semiring under matrix multiplication.
Associativity and both unit laws are checked in each entry by polynomial normalization.
The instance enables binary exponentiation of executable Lucas companion states. -/
instance [CommSemiring R] : Monoid (LucasScalarState R) where
  mul_assoc x y z := by
    cases x with
    | mk xa xb xc xd =>
      cases y with
      | mk ya yb yc yd =>
        cases z with
        | mk za zb zc
          zd =>
          change
            lucasScalarMul
                (lucasScalarMul { a := xa, b := xb, c := xc, d := xd }
                  { a := ya, b := yb, c := yc, d := yd })
                { a := za, b := zb, c := zc, d := zd } =
              lucasScalarMul { a := xa, b := xb, c := xc, d := xd }
                (lucasScalarMul { a := ya, b := yb, c := yc, d := yd }
                  { a := za, b := zb, c := zc, d := zd })
          apply LucasScalarState.ext <;> simp only [lucasScalarMul] <;> ring
  one_mul x := by
    cases x with
    | mk xa xb xc
      xd =>
      change
        lucasScalarMul lucasScalarOne { a := xa, b := xb, c := xc, d := xd } =
          { a := xa, b := xb, c := xc, d := xd }
      apply LucasScalarState.ext <;> simp only [lucasScalarMul, lucasScalarOne] <;> ring
  mul_one x := by
    cases x with
    | mk xa xb xc
      xd =>
      change
        lucasScalarMul { a := xa, b := xb, c := xc, d := xd } lucasScalarOne =
          { a := xa, b := xb, c := xc, d := xd }
      apply LucasScalarState.ext <;> simp only [lucasScalarMul, lucasScalarOne] <;> ring

/--
Represent a four-entry state as the matrix [[a,b],[c,d]].
No algebraic assumptions are required; multiplication and unit preservation
connect executable scalar states to matrix-based correctness proofs.
-/
def lucasScalarStateMatrix {R : Type*} (x : LucasScalarState R) : Matrix (Fin 2) (Fin 2) R :=
  !![x.a, x.b; x.c, x.d]

/--
Over a commutative semiring, the matrix representation preserves scalar multiplication.
Expand the two-term row-column sums entrywise; each equality is definitional.
This transports scalar powering to companion-matrix powering.
-/
theorem lucasScalarStateMatrix_mul [CommSemiring R] (x y : LucasScalarState R) :
    lucasScalarStateMatrix (x * y) = lucasScalarStateMatrix x * lucasScalarStateMatrix y := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [lucasScalarStateMatrix, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_one]
    rfl
  · simp only [lucasScalarStateMatrix, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero,
      Matrix.mul_apply, Fin.sum_univ_two]
    rfl
  · simp only [lucasScalarStateMatrix, Fin.mk_one, Fin.isValue, Fin.zero_eta, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.mul_apply, Fin.sum_univ_two]
    rfl
  · simp only [lucasScalarStateMatrix, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero]
    rfl

/--
Over a commutative semiring, the scalar unit represents the identity matrix.
Check the four entries, distinguishing diagonal and off-diagonal indices.
This supplies the zero-power case of the representation bridge.
-/
theorem lucasScalarStateMatrix_one [CommSemiring R] :
    lucasScalarStateMatrix (1 : LucasScalarState R) = (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [lucasScalarStateMatrix, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.one_apply_eq]
    rfl
  · simp only [lucasScalarStateMatrix, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero, ne_eq,
      zero_ne_one, not_false_eq_true, Matrix.one_apply_ne]
    rfl
  · simp only [lucasScalarStateMatrix, Fin.mk_one, Fin.isValue, Fin.zero_eta, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, ne_eq,
      one_ne_zero, not_false_eq_true, Matrix.one_apply_ne]
    rfl
  · simp only [lucasScalarStateMatrix, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.one_apply_eq]
    rfl

/--
For any scalar state over a commutative semiring, representation commutes with binary powering.
Induction on the exponent uses preservation of multiplication and the unit.
This transfers executable companion-state powers to the matrix formula.
-/
theorem lucasScalarStatePowFast_matrix [CommSemiring R] (x : LucasScalarState R) (k : ℕ) :
    lucasScalarStateMatrix (npowBinRec k x) = npowBinRec k (lucasScalarStateMatrix x) := by
  induction k with
  | zero => rw [npowBinRec_zero, npowBinRec_zero, lucasScalarStateMatrix_one]
  | succ k ih => rw [npowBinRec_succ, npowBinRec_succ, lucasScalarStateMatrix_mul, ih]

/--
Encode the companion matrix as (P,-Q,1,0) in ZMod n.
Signed parameters are reduced modulo n; this state is the base for scalar Lucas powers.
-/
def lucasScalarSeed (n : ℕ) (P Q : ℤ) : LucasScalarState (ZMod n) :=
  { a := (P : ZMod n), b := -(Q : ZMod n), c := 1, d := 0 }

/--
Compute the kth power of the scalar companion seed by binary exponentiation.
The four modular entries represent the companion-matrix power, without matrix indexing
in the executable path; U is recovered from c and V from a+d.
-/
def lucasScalarPowFast (n : ℕ) (P Q : ℤ) (k : ℕ) : LucasScalarState (ZMod n) :=
  npowBinRec k (lucasScalarSeed n P Q)

/--
For every n,P,Q,k, the scalar companion power represents the fast matrix companion power.
Use the general binary-power representation theorem and the definitional seed equality.
This is the bridge used to certify the scalar U and V evaluators.
-/
theorem lucasScalarPowFast_to_matrix (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasScalarStateMatrix (lucasScalarPowFast n P Q k) = lucasCompanionPowFast n P Q k := by
  unfold lucasScalarPowFast lucasScalarSeed lucasCompanionPowFast
  rw [lucasScalarStatePowFast_matrix]
  rfl

/--
Compute U_k(P,Q) modulo n using the bottom-left entry of the scalar companion power.
Return zero explicitly at index zero; all positive indices use binary exponentiation.
The following theorem compares this executable value with the recursive integer specification.
-/
def lucasUZModFast (n : ℕ) (P Q : ℤ) (k : ℕ) : ZMod n :=
  match k with
  | 0 => 0
  | k + 1 => (lucasScalarPowFast n P Q (k + 1)).c

/--
Compute V_k(P,Q) modulo n as the trace a+d of the binary companion-state power.
The zero-index identity state gives V_0=2 without a separate branch.
This is the executable V evaluator used by probable-prime tests.
-/
def lucasVZModFast (n : ℕ) (P Q : ℤ) (k : ℕ) : ZMod n :=
  let state := lucasScalarPowFast n P Q k
  state.a + state.d

/--
For all moduli, signed parameters and natural indices, fast U equals the integer U cast.
Handle zero directly; for a successor extract matrix entry (1,0) from the companion formula.
This certifies the executable Lucas-U condition against its recursive specification.
-/
theorem lucasUZModFast_eq_lucasUZMod (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasUZModFast n P Q k = lucasUZMod n P Q k := by
  cases k with
  | zero =>
    change 0 = (lucasU P Q 0 : ZMod n)
    simp only [lucasU_zero, Int.cast_zero]
  | succ k =>
    change (lucasScalarPowFast n P Q (k + 1)).c = (lucasU P Q (k + 1) : ZMod n)
    have hmatrix := congrArg (fun M => M 1 0) (lucasScalarPowFast_to_matrix n P Q (k + 1))
    rw [lucasCompanionPowFast_eq_pow, lucasCompanion_pow_succ] at hmatrix
    simpa only [lucasScalarStateMatrix, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, neg_mul] using hmatrix

/--
For all moduli, signed parameters and natural indices, fast V equals the integer V cast.
At zero use the identity trace; at a successor extract the diagonal entries and apply
V_{k+1}=U_{k+2}-Q U_k. This certifies V computations in Lucas-V and Strong Lucas tests.
-/
theorem lucasVZModFast_eq_lucasVZMod (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasVZModFast n P Q k = lucasVZMod n P Q k := by
  cases k with
  | zero =>
    change (lucasScalarPowFast n P Q 0).a + (lucasScalarPowFast n P Q 0).d = (lucasV P Q 0 : ZMod n)
    rw [show lucasScalarPowFast n P Q 0 = 1 by simp only [lucasScalarPowFast, npowBinRec_zero]]
    change
      (lucasScalarOne (R := ZMod n)).a + (lucasScalarOne (R := ZMod n)).d = (lucasV P Q 0 : ZMod n)
    rw [lucasScalarOne]
    simp only [lucasV_zero, Int.cast_ofNat]
    norm_num only
  | succ
    k =>
    change
      (lucasScalarPowFast n P Q (k + 1)).a + (lucasScalarPowFast n P Q (k + 1)).d =
        (lucasV P Q (k + 1) : ZMod n)
    have hmatrix := lucasScalarPowFast_to_matrix n P Q (k + 1)
    have h00 := congrArg (fun M => M 0 0) hmatrix
    have h11 := congrArg (fun M => M 1 1) hmatrix
    rw [lucasCompanionPowFast_eq_pow, lucasCompanion_pow_succ] at h00 h11
    have h00' : (lucasScalarPowFast n P Q (k + 1)).a = (lucasU P Q (k + 2) : ZMod n) := by
      simpa only [lucasScalarStateMatrix, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, neg_mul] using h00
    have h11' : (lucasScalarPowFast n P Q (k + 1)).d = -(Q : ZMod n) * (lucasU P Q k : ZMod n) := by
      simpa only [neg_mul, lucasScalarStateMatrix, Fin.isValue, Matrix.of_apply,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] using h11
    rw [h00', h11']
    have hV := lucasV_succ_eq_lucasU_succ_succ_sub P Q k
    have hVcast := congrArg (fun z : ℤ => (z : ZMod n)) hV
    calc
      (lucasU P Q (k + 2) : ZMod n) + -(Q : ZMod n) * (lucasU P Q k : ZMod n) =
          (lucasU P Q (k + 2) + -(Q * lucasU P Q k) : ℤ) :=
        by
        rw [Int.cast_add, Int.cast_neg, Int.cast_mul]
        ring
      _ = (lucasV P Q (k + 1) : ZMod n) := hVcast.symm

end PseudoPrime.PrimeTest
