/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Lucas.Spec
public import Mathlib.Data.Nat.BinaryRec

/-! # Binary modular Lucas triples -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- Twice the next U value is P times the current U plus the current V.
The recurrence proves the identity without division over the integers. -/
theorem lucasU_succ_twice (P Q : ℤ) (k : ℕ) :
    2 * lucasU P Q (k + 1) = P * lucasU P Q k + lucasV P Q k := by
  cases k with
  | zero =>
    rw [lucasU_one, lucasU_zero, lucasV_zero]; ring
  | succ k =>
    rw [lucasV_succ_eq_lucasU_succ_succ_sub, lucasU_succ_succ]
    ring

/-- Twice the next V value uses the signed discriminant P^2 - 4Q.
This integer identity supplies the simultaneous modular increment. -/
theorem lucasV_succ_twice (P Q : ℤ) (k : ℕ) :
    2 * lucasV P Q (k + 1) = (P * P - 4 * Q) * lucasU P Q k + P * lucasV P Q k := by
  cases k with
  | zero =>
    rw [lucasV_one, lucasU_zero, lucasV_zero]; ring
  | succ
    k =>
    rw [lucasV_succ_eq_lucasU_succ_succ_sub, lucasV_succ_eq_lucasU_succ_succ_sub, lucasU_succ_succ,
      lucasU_succ_succ]
    ring

/-- Multiply by the inverse of two in ZMod n. For odd n this recovers
modular division by two, including the singleton ring at n = 1. -/
def lucasModHalf (n : ℕ) (x : ZMod n) : ZMod n :=
  (2 : ZMod n)⁻¹ * x

/-- For an odd modulus, modular halving cancels multiplication by two.
Coprimality of two and n gives the inverse equation. -/
theorem lucasModHalf_twice (n : ℕ) (hn : Odd n) (x : ZMod n) : lucasModHalf n (2 * x) = x := by
  have h := ZMod.coe_mul_inv_eq_one 2 (Nat.coprime_two_left.mpr hn)
  simp only [Nat.cast_ofNat] at h
  rw [lucasModHalf, ← mul_assoc, mul_comm (2 : ZMod n)⁻¹, h, one_mul]

/-- Halve the canonical residue by adding the odd modulus when the residue is odd.
The result implements the reference integer division step; correctness requires odd n. -/
def lucasModHalfResidue (n : ℕ) (x : ZMod n) : ZMod n :=
  (((if x.val % 2 = 0 then x.val else x.val + n) / 2 : ℕ) : ZMod n)

/-- For odd n, twice the residue half recovers x, including n = 1.
The adjusted numerator is even and adding n preserves its modular value. -/
theorem lucasModHalfResidue_twice (n : ℕ) (hn : Odd n) (x : ZMod n) :
    2 * lucasModHalfResidue n x = x := by
  let : NeZero n := ⟨Nat.ne_of_gt hn.pos⟩
  have he : Even (if x.val % 2 = 0 then x.val else x.val + n) := by
    split_ifs with h
    · exact Nat.even_iff.mpr h
    · rcases Nat.even_or_odd x.val with hv | hv
      · exact False.elim (h (Nat.even_iff.mp hv))
      · exact hv.add_odd hn
  have hd := Nat.div_mul_cancel he.two_dvd
  have hc := congrArg (fun k : ℕ ↦ (k : ZMod n)) hd
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hc
  rw [lucasModHalfResidue, mul_comm, hc]
  split_ifs <;> simp only [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]

/-- For odd n, integer residue halving equals inverse-based halving.
Cancel two using the doubled residue identity to connect existing Lucas proofs. -/
theorem lucasModHalfResidue_eq (n : ℕ) (hn : Odd n) (x : ZMod n) :
    lucasModHalfResidue n x = lucasModHalf n x := by
  calc
    lucasModHalfResidue n x = lucasModHalf n (2 * lucasModHalfResidue n x) :=
      (lucasModHalf_twice n hn _).symm
    _ = lucasModHalf n x := congrArg (lucasModHalf n) (lucasModHalfResidue_twice n hn x)

/-- Use integer residue halving for odd n and the existing operation otherwise.
This total wrapper preserves all input behavior of the increment API. -/
def lucasModHalfExec (n : ℕ) (x : ZMod n) : ZMod n :=
  if Odd n then lucasModHalfResidue n x else lucasModHalf n x

/-- The executable half agrees with the existing operation for every modulus.
The odd branch uses the residue theorem; the fallback is definitionally equal. -/
theorem lucasModHalfExec_eq (n : ℕ) (x : ZMod n) : lucasModHalfExec n x = lucasModHalf n x := by
  unfold lucasModHalfExec
  split_ifs with hn
  · exact lucasModHalfResidue_eq n hn x
  · rfl

/-- The U increment formula holds modulo every odd n for signed P and Q.
Cast the integer identity and cancel two using modular halving. -/
theorem lucasUZMod_succ_half (n : ℕ) (hn : Odd n) (P Q : ℤ) (k : ℕ) :
    lucasModHalf n ((P : ZMod n) * lucasUZMod n P Q k + lucasVZMod n P Q k) =
      lucasUZMod n P Q (k + 1) := by
  have h := congrArg (fun x : ℤ ↦ (x : ZMod n)) (lucasU_succ_twice P Q k)
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_add] at h
  change lucasModHalf n ((P : ZMod n) * (lucasU P Q k : ZMod n) + (lucasV P Q k : ZMod n)) = _
  rw [← h, lucasModHalf_twice n hn]
  rfl

/-- The V increment uses the signed discriminant and the old U and V.
The integer companion identity and the inverse of two justify this update. -/
theorem lucasVZMod_succ_half (n : ℕ) (hn : Odd n) (P Q : ℤ) (k : ℕ) :
    lucasModHalf n
        (((P * P - 4 * Q : ℤ) : ZMod n) * lucasUZMod n P Q k + (P : ZMod n) * lucasVZMod n P Q k) =
      lucasVZMod n P Q (k + 1) := by
  have h := congrArg (fun x : ℤ ↦ (x : ZMod n)) (lucasV_succ_twice P Q k)
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_add, Int.cast_sub] at h
  change
    lucasModHalf n
        (((P * P - 4 * Q : ℤ) : ZMod n) * (lucasU P Q k : ZMod n) +
          (P : ZMod n) * (lucasV P Q k : ZMod n)) =
      _
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat]
  rw [← h, lucasModHalf_twice n hn]
  rfl

/-- A modular triple with fields u, v and qk for U_m, V_m and Q^m respectively.
The record itself imposes no common-index invariant; lucasUVQSpec and the update
correctness lemmas establish it for evaluated states. The evaluator and Strong scan
use these components without constructing the integer Lucas values. -/
@[ext]
structure LucasUVQState (n : ℕ) where
  u : ZMod n
  v : ZMod n
  qk : ZMod n
  deriving DecidableEq

/-- The mathematical state at exponent k, used only to specify executable
updates and their relation to the existing integer sequences. -/
def lucasUVQSpec (n : ℕ) (P Q : ℤ) (k : ℕ) : LucasUVQState n :=
  ⟨lucasUZMod n P Q k, lucasVZMod n P Q k, (lucasQPow Q k : ZMod n)⟩

/-- Double the represented exponent using old u, v, and qk simultaneously.
All three results are reduced by the ZMod arithmetic. -/
def lucasUVQDouble (n : ℕ) (x : LucasUVQState n) : LucasUVQState n :=
  ⟨x.u * x.v, x.v ^ 2 - 2 * x.qk, x.qk ^ 2⟩

/-- Increment the represented exponent for odd n. Both half formulas use
the same old u and v; the signed Q power is multiplied by Q. -/
def lucasUVQIncrement (n : ℕ) (P Q : ℤ) (x : LucasUVQState n) : LucasUVQState n :=
  ⟨lucasModHalfExec n ((P : ZMod n) * x.u + x.v),
    lucasModHalfExec n (((P * P - 4 * Q : ℤ) : ZMod n) * x.u + (P : ZMod n) * x.v),
    x.qk * (Q : ZMod n)⟩

/-- The triple doubling update represents exponent 2k for every modulus.
The existing U and V doubling identities justify the first two components. -/
theorem lucasUVQDouble_spec (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasUVQDouble n (lucasUVQSpec n P Q k) = lucasUVQSpec n P Q (2 * k) := by
  apply LucasUVQState.ext
  · exact (lucasUZMod_two_mul n P Q k).symm
  · exact (lucasVZMod_two_mul n P Q k).symm
  · simp only [lucasUVQDouble, lucasUVQSpec, lucasQPow, Int.cast_pow, pow_mul, Nat.mul_comm 2 k]

/-- For odd n the simultaneous increment represents exponent k + 1.
The half identities and the Q power recurrence prove each component. -/
theorem lucasUVQIncrement_spec (n : ℕ) (hn : Odd n) (P Q : ℤ) (k : ℕ) :
    lucasUVQIncrement n P Q (lucasUVQSpec n P Q k) = lucasUVQSpec n P Q (k + 1) := by
  apply LucasUVQState.ext
  · change lucasModHalfExec n _ = _
    rw [lucasModHalfExec_eq]
    exact lucasUZMod_succ_half n hn P Q k
  · change lucasModHalfExec n _ = _
    rw [lucasModHalfExec_eq]
    exact lucasVZMod_succ_half n hn P Q k
  · simp only [lucasUVQIncrement, lucasUVQSpec, lucasQPow, pow_succ, Int.cast_mul]

/-- Append a binary digit to the represented exponent by doubling and,
for a one digit, incrementing the doubled state. -/
def lucasUVQBit (n : ℕ) (P Q : ℤ) (b : Bool) (x : LucasUVQState n) : LucasUVQState n :=
  let doubled := lucasUVQDouble n x
  if b then lucasUVQIncrement n P Q doubled else doubled

/-- Appending a digit transforms the specification from k to Nat.bit b k.
The proof composes the doubling and increment contracts. -/
theorem lucasUVQBit_spec (n : ℕ) (hn : Odd n) (P Q : ℤ) (b : Bool) (k : ℕ) :
    lucasUVQBit n P Q b (lucasUVQSpec n P Q k) = lucasUVQSpec n P Q (Nat.bit b k) := by
  cases b <;>
    simp only [lucasUVQBit, Bool.false_eq_true, ↓reduceIte, lucasUVQDouble_spec,
      lucasUVQIncrement_spec n hn, Nat.bit_val, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]

/-- Evaluate U_k, V_k, and Q^k together by recursion on binary digits.
The zero prefix starts at (0, 2, 1); each digit uses modular triple updates.
Correctness requires an odd modulus; callers guard that domain. -/
def lucasUVQ (n : ℕ) (P Q : ℤ) (k : ℕ) : LucasUVQState n :=
  Nat.binaryRec (motive := fun _ ↦ LucasUVQState n) ⟨0, 2, 1⟩ (fun b _ x ↦ lucasUVQBit n P Q b x) k

/-- The zero prefix agrees with the Lucas initial values for every modulus. -/
theorem lucasUVQ_zero (n : ℕ) (P Q : ℤ) : lucasUVQ n P Q 0 = lucasUVQSpec n P Q 0 := by
  simp only [lucasUVQ, Nat.binaryRec_zero, lucasUVQSpec, lucasUZMod, lucasVZMod, lucasU_zero,
    lucasV_zero, lucasQPow_zero, Int.cast_zero, Int.cast_ofNat, Int.cast_one]

/-- Appending a zero to the zero prefix preserves its initial state.
This supplies the zero-case coherence required by Nat.binaryRec. -/
theorem lucasUVQBit_zero (n : ℕ) (P Q : ℤ) : lucasUVQBit n P Q false ⟨0, 2, 1⟩ = ⟨0, 2, 1⟩ := by
  simp only [lucasUVQBit, Bool.false_eq_true, ↓reduceIte, lucasUVQDouble, zero_mul, one_pow]
  congr 1
  ring

/-- For any odd modulus, signed parameters, and nonnegative exponent,
the binary triple evaluator agrees with the existing Lucas specifications.
Binary induction transports the prefix invariant across each digit. -/
theorem lucasUVQ_eq (n : ℕ) (hn : Odd n) (P Q : ℤ) (k : ℕ) :
    lucasUVQ n P Q k = lucasUVQSpec n P Q k := by
  induction k using Nat.binaryRec with
  | zero => exact lucasUVQ_zero n P Q
  | bit b k ih =>
    rw [lucasUVQ, Nat.binaryRec_eq b k (Or.inl (lucasUVQBit_zero n P Q))]
    change lucasUVQBit n P Q b (lucasUVQ n P Q k) = _
    rw [ih, lucasUVQBit_spec n hn]

end PseudoPrime.PrimeTest
