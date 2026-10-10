/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Precheck
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.IntervalCases
public import PseudoPrime.PrimeTest.StrongLucas.NoGcd

/-! # Batched natural and signed Jacobi procedures and their correctness -/

@[expose] public section

namespace PseudoPrime.PrimeTest.ReferenceArithmetic

/-- For an odd modulus, removing a factor of two flips the sign at residues three and five. -/
theorem jacobiSign2 (n : ℕ) (hn : n % 2 = 1) :
    jacobiSym 2 n = if n % 8 = 3 ∨ n % 8 = 5 then -1 else 1 := by
  have hj := jacobiSym.even_odd (a := 2) (by decide) hn
  norm_num only [Int.reduceDiv, jacobiSym.one_left] at hj
  exact hj.symm

/--
For a nonzero numerator, removing all factors of two leaves a positive odd part.
The factorization identity excludes zero; reciprocity uses this positive divisor.
-/
theorem oddPart_pos (a : ℕ) (ha : a ≠ 0) : 0 < Nat.divMaxPow a 2 := by
  apply Nat.pos_of_ne_zero
  intro hz
  have h := Nat.divMaxPow_mul_pow_padicValNat 2 a
  rw [hz, zero_mul] at h
  exact ha h.symm

/--
For a nonzero numerator, its odd part is at most the original numerator.
Divisibility supplies the bound required by the divisor-reducing Fibonacci interface.
-/
theorem oddPart_le (a : ℕ) (ha : a ≠ 0) : Nat.divMaxPow a 2 ≤ a :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero ha)
    ⟨2 ^ padicValNat 2 a, (Nat.divMaxPow_mul_pow_padicValNat 2 a).symm⟩

/--
For a nonzero numerator, its maximal-power quotient is odd.
Maximality excludes divisibility by two, so the next Jacobi modulus remains odd.
-/
theorem oddPart_odd (a : ℕ) (ha : a ≠ 0) : Nat.divMaxPow a 2 % 2 = 1 := by
  apply Nat.mod_two_ne_zero.mp
  intro he
  exact Nat.not_dvd_divMaxPow (by decide : 1 < 2) ha (Nat.dvd_iff_mod_eq_zero.mpr he)

/--
Sign multiplier for one batched Jacobi round on numerator `a` and modulus `n`.
The factor-two rule contributes a power with exponent `padicValNat 2 a`; reciprocity
contributes minus one exactly when the odd part and modulus are both three modulo four.
-/
def jacobiRoundSign (a n : ℕ) : ℤ :=
  (if n % 8 = 3 ∨ n % 8 = 5 then (-1 : ℤ) else 1) ^ padicValNat 2 a *
    (if Nat.divMaxPow a 2 % 4 = 3 ∧ n % 4 = 3 then -1 else 1)

/-- One batched sign update with an odd modulus agrees with factorization and reciprocity.
The two-adic decomposition, the factor-two sign, and remainder invariance identify the result.
This identity supplies the semantic step for both recursive and fuel-bounded procedures. -/
theorem jacobiRoundSign_mul (a n : ℕ) (ha : a ≠ 0) (hn : n % 2 = 1) :
    jacobiRoundSign a n * jacobiSym ((n % Nat.divMaxPow a 2 : ℕ) : ℤ) (Nat.divMaxPow a 2) =
      jacobiSym (a : ℤ) n := by
  have hr := jacobiSym.quadratic_reciprocity_if (oddPart_odd a ha) hn
  have hf := Nat.pow_padicValNat_mul_divMaxPow 2 a
  conv_rhs =>
    rw [← hf, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, jacobiSym.mul_left, jacobiSym.pow_left,
      jacobiSign2 n hn]
  rw [jacobiRoundSign, mul_assoc, Int.natCast_emod, ← jacobiSym.mod_left]
  congr 1
  simpa only [ite_mul, neg_one_mul, one_mul] using hr

/-- Reference Jacobi recursion for natural numerators, removing all factors of two per round.
The valuation is `padicValNat 2 a`, and the odd part is `Nat.divMaxPow a 2`.
A positive round applies reciprocity and recurses on the remainder modulo the odd part.
Zero returns one only at modulus one. The numerator decreases at every recursive call. -/
def jacobiNat (a n : ℕ) : ℤ :=
  if _ha : a = 0 then if n = 1 then 1 else 0
  else jacobiRoundSign a n * jacobiNat (n % Nat.divMaxPow a 2) (Nat.divMaxPow a 2)
termination_by a
decreasing_by exact (Nat.mod_lt n (oddPart_pos a _ha)).trans_le (oddPart_le a _ha)

/-- For an odd modulus, the batched reference recursion equals jacobiSym, including modulus one.
Strong induction uses odd-part positivity and its upper bound to decrease the numerator;
the batched sign identity combines factor-two removal, reciprocity, and remainder invariance. -/
theorem jacobiNat_eq (a n : ℕ) (hn : n % 2 = 1) : jacobiNat a n = jacobiSym (a : ℤ) n := by
  induction a using Nat.strong_induction_on generalizing n with
  | h a ih =>
    rw [jacobiNat]
    split
    · next ha =>
        subst a
        by_cases h : n = 1
        · subst n
          simp only [ite_true, jacobiSym.one_right]
        · have hp : 1 < n := by
            have hz : n ≠ 0 := by
              intro hh; subst n; contradiction
            exact Nat.lt_of_le_of_ne (Nat.pos_of_ne_zero hz) (Ne.symm h)
          rw [ite_eq_right h, Nat.cast_zero, jacobiSym.zero_left hp]
    · next
        ha =>
        rw [ih _ ((Nat.mod_lt n (oddPart_pos a ha)).trans_le (oddPart_le a ha)) _
            (oddPart_odd a ha)]
        exact jacobiRoundSign_mul a n ha hn

/-- Signed reference Jacobi procedure; a negative numerator contributes the mod-four sign. -/
def jacobiSigned (a : ℤ) (n : ℕ) : ℤ :=
  (if a < 0 ∧ n % 4 = 3 then -1 else 1) * jacobiNat a.natAbs n

/-- For an odd modulus, the negative-numerator sign is minus one exactly at residue three. -/
theorem jacobiSign4 (n : ℕ) (hn : n % 2 = 1) : ZMod.χ₄ n = if n % 4 = 3 then -1 else 1 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  have he : ¬n % 2 = 0 := by
    rw [hn]; decide
  rw [ite_eq_right he]
  rcases Nat.odd_mod_four_iff.mp hn with h | h
  · simp only [h, ite_true, Nat.reduceEqDiff, ite_false]
  · simp only [h, Nat.reduceEqDiff, ite_false, ite_true]

/--
For every integer numerator a and odd natural modulus n, the signed reference
procedure equals jacobiSym a n. Rewrite the natural recursion, then handle negative a
using the modulus-four character and the natAbs identity. This certifies signed reference input.
-/
theorem jacobiSigned_eq (a : ℤ) (n : ℕ) (hn : n % 2 = 1) : jacobiSigned a n = jacobiSym a n := by
  rw [jacobiSigned, jacobiNat_eq a.natAbs n hn]
  by_cases ha : a < 0
  · have hab : (a.natAbs : ℤ) = -a := by rw [Int.natCast_natAbs, abs_of_neg ha]
    rw [hab]
    have hj := jacobiSym.neg (-a) (Nat.odd_iff.mpr hn)
    rw [neg_neg, jacobiSign4 n hn] at hj
    simp only [ha, true_and, ite_mul, neg_one_mul, one_mul]
    simpa only [ite_mul, neg_one_mul, one_mul] using hj.symm
  · rw [Int.natAbs_of_nonneg (Int.le_of_not_gt ha)]
    simp only [ha, false_and, ite_false, one_mul]

end PseudoPrime.PrimeTest.ReferenceArithmetic
