/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Precheck
import Mathlib.Data.Nat.PadicValNat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import PseudoPrime.PrimeTest.StrongLucas.NoGcd

/-! # Reference square root, square filter, signed remainder, and Jacobi procedures -/

namespace PseudoPrime.PrimeTest.ReferenceArithmetic

/-- Newton update with natural-number division; positive iterates feed the decreasing newtonLoop. -/
def newtonStep (n s : ℕ) :=
  (s + n / s) / 2

/-- Every positive Newton iterate stays at or above the floor square root.
The division bound and a nonnegative square exclude undershooting. -/
theorem newtonStep_lower (n t : ℕ) (ht : 0 < t) : Nat.sqrt n ≤ newtonStep n t := by
  apply Nat.le_of_not_gt
  intro h
  have hs := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp h
  have hsum := Nat.succ_le_of_lt hs
  have hdiv := Nat.lt_mul_div_succ n ht
  have hr := Nat.sqrt_le' n
  nlinarith only [hsum, hdiv, hr, sq_nonneg ((t : ℤ) - (Nat.sqrt n : ℤ))]

/-- A positive iterate that does not decrease has square at most n.
This is the upper bound needed to identify the newtonLoop result. -/
theorem newtonStep_stop (n s : ℕ) (hs : 0 < s) (h : s ≤ newtonStep n s) : s ≤ Nat.sqrt n := by
  have hh := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp h
  have hq : s ≤ n / s := by nlinarith only [hh]
  apply Nat.le_sqrt'.mpr
  simpa only [pow_two] using (Nat.le_div_iff_mul_le hs).mp hq

/-- Repeat Newton updates while they decrease. The current iterate is the termination measure. -/
def newtonLoop (n s : ℕ) : ℕ :=
  if _h : newtonStep n s < s then newtonLoop n (newtonStep n s) else s
termination_by s

/-- For a positive square root and an initial upper bound, the Newton newtonLoop returns Nat.sqrt.
Strong induction preserves the lower bound and uses the stop bound at termination. -/
theorem newtonLoop_eq (n s : ℕ) (hn : 0 < Nat.sqrt n) (hs : Nat.sqrt n ≤ s) :
    newtonLoop n s = Nat.sqrt n := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    rw [newtonLoop]
    split
    · next h => exact ih (newtonStep n s) h (newtonStep_lower n s (Nat.lt_of_lt_of_le hn hs))
    · next h =>
        exact
          Nat.le_antisymm (newtonStep_stop n s (Nat.lt_of_lt_of_le hn hs) (Nat.le_of_not_gt h)) hs

/-- Power-of-two initial bound used by the reference square root for n at least two.
For positive n-1, bit_length(n-1) is log2(n-1)+1. -/
def newtonSeed (n : ℕ) :=
  2 ^ (((n - 1).log2 + 2) / 2)

/-- For n at least two, the reference power-of-two newtonSeed bounds Nat.sqrt from above. -/
theorem newtonSeed_upper (n : ℕ) (hn : 2 ≤ n) : Nat.sqrt n ≤ newtonSeed n := by
  have hd := Nat.div_add_mod ((n - 1).log2 + 2) 2
  have hm := Nat.mod_lt ((n - 1).log2 + 2) (by decide : 0 < 2)
  have he : (n - 1).log2 + 1 ≤ 2 * (((n - 1).log2 + 2) / 2) := by nlinarith only [hd, hm]
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) he
  have hl := Nat.lt_log2_self (n := n - 1)
  have hn' := Nat.sub_add_cancel (Nat.le_trans (by decide : 1 ≤ 2) hn)
  have hb : n ≤ newtonSeed n ^ 2 := by
    dsimp only [newtonSeed]
    rw [← pow_mul, Nat.mul_comm (((n - 1).log2 + 2) / 2) 2]
    nlinarith only [hp, hl, hn']
  have hr := Nat.sqrt_le' n
  nlinarith only [hr, hb]

/-- Reference Newton square root, including the direct zero and one cases. -/
def newtonSqrt (n : ℕ) :=
  if n < 2 then n else newtonLoop n (newtonSeed n)

/-- The reference square-root procedure agrees with Nat.sqrt for every natural input. -/
theorem newtonSqrt_eq (n : ℕ) : newtonSqrt n = Nat.sqrt n := by
  unfold newtonSqrt
  split
  · next
      h =>
      have hn : n = 0 ∨ n = 1 := by
        exact (Nat.le_one_iff_eq_zero_or_eq_one).mp (Nat.le_of_lt_succ h)
      rcases hn with rfl | rfl <;> rfl
  · next h =>
      apply newtonLoop_eq
      · have hh : 1 ≤ Nat.sqrt n :=
          Nat.le_sqrt'.mpr (Nat.le_trans (by decide : 1 ^ 2 ≤ 2) (Nat.le_of_not_gt h))
        exact hh
      · exact newtonSeed_upper n (Nat.le_of_not_gt h)

/-- Reference 0x13 bit mask accepts the square residues zero, one, and four modulo eight. -/
def squareMask8 (n : ℕ) : Bool :=
  (19 >>> (n % 8)) &&& 1 != 0

/-- The mod-eight mask never rejects a square; the eight residue cases are kernel checked. -/
theorem squareMask8_sq (k : ℕ) : squareMask8 (k ^ 2) = true := by
  have h := Nat.mod_lt k (by decide : 0 < 8)
  unfold squareMask8
  rw [Nat.pow_mod]
  interval_cases hk : k % 8 <;> rfl

/-- Reference square test combines the mod-eight mask and the Newton square root. -/
def referenceSquare (n : ℕ) : Bool :=
  squareMask8 n && (newtonSqrt n ^ 2 == n)

/-- The masked Newton square test equals the production square predicate on all inputs. -/
theorem referenceSquare_eq (n : ℕ) : referenceSquare n = PseudoPrime.PrimeTest.natIsSquare n := by
  rw [referenceSquare, newtonSqrt_eq]
  by_cases h : Nat.sqrt n ^ 2 = n
  · have hm := squareMask8_sq (Nat.sqrt n)
    rw [h] at hm
    simp only [hm, PseudoPrime.PrimeTest.natIsSquare, h, beq_self_eq_true, Bool.and_self]
  · have hb : (Nat.sqrt n ^ 2 == n) = false := beq_eq_false_iff_ne.mpr h
    simp only [PseudoPrime.PrimeTest.natIsSquare, hb, Bool.and_false]

/-- C++ remainder normalization: add the positive modulus to a negative truncating remainder. -/
def referenceNormalize (a : ℤ) (n : ℕ) : ℤ :=
  let r := a.tmod (n : ℤ)
  if r < 0 then r + n else r

/-- For a positive modulus, C++ normalization equals the Euclidean remainder used by Python. -/
theorem referenceNormalize_eq (a : ℤ) (n : ℕ) (hn : 0 < n) :
    referenceNormalize a n = a % (n : ℤ) := by
  have hp : 0 < (n : ℤ) := Int.natCast_pos.mpr hn
  have he := Int.emod_nonneg a (Int.ne_of_gt hp)
  have hl := Int.emod_lt_of_pos a hp
  unfold referenceNormalize
  rw [Int.tmod_eq_emod]
  by_cases h : 0 ≤ a ∨ (n : ℤ) ∣ a
  · simp only [h, ↓reduceIte, Nat.cast_zero, sub_zero, Int.not_lt_of_ge he]
  · simp only [h, ↓reduceIte, Int.natAbs_natCast]
    have hr : a % (n : ℤ) - n < 0 := sub_neg.mpr hl
    rw [ite_eq_left hr, sub_add_cancel]

/-- The normalized reference remainder represents the original integer in ZMod. -/
theorem referenceNormalize_zmod (a : ℤ) (n : ℕ) (hn : 0 < n) :
    ((referenceNormalize a n : ℤ) : ZMod n) = (a : ZMod n) := by
  rw [referenceNormalize_eq a n hn, ZMod.intCast_mod]

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

/-- The signed reference Jacobi procedure equals jacobiSym for every integer numerator. -/
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

/-- Batch s factor-two removals before continuing the reference Jacobi procedure. -/
def jacobiBatch (s a n : ℕ) : ℤ :=
  (if n % 8 = 3 ∨ n % 8 = 5 then -1 else 1) ^ s * jacobiNat a n

/-- Batch removal and the batched reference recursion give the same Jacobi result.
The input is explicitly factored as two to the power s times a. -/
theorem jacobiBatch_eq (s a n : ℕ) (hn : n % 2 = 1) :
    jacobiBatch s a n = jacobiNat (2 ^ s * a) n := by
  rw [jacobiBatch, jacobiNat_eq a n hn, jacobiNat_eq (2 ^ s * a) n hn, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, jacobiSym.mul_left, jacobiSym.pow_left, jacobiSign2 n hn]

/-- The batch sign depends only on the parity of s, matching the C++ update. -/
theorem jacobiBatch_parity (s n : ℕ) :
    (if n % 8 = 3 ∨ n % 8 = 5 then (-1 : ℤ) else 1) ^ s =
      if s % 2 = 1 ∧ (n % 8 = 3 ∨ n % 8 = 5) then -1 else 1 := by
  by_cases h : n % 8 = 3 ∨ n % 8 = 5
  · simp only [h, ite_true, and_true]
    rw [neg_one_pow_eq_pow_mod_two]
    rcases Nat.mod_two_eq_zero_or_one s with hs | hs
    · simp only [hs, pow_zero, Nat.reduceEqDiff, ite_false]
    · simp only [hs, pow_one, ite_true]
  · simp only [h, ite_false, one_pow, and_false]

/-- The initial right shift is division by the power-of-two newtonSeed. -/
theorem newtonSeed_shift (n : ℕ) : n >>> (((n - 1).log2 + 2) / 2) = n / newtonSeed n := by
  exact Nat.shiftRight_eq_div_pow n (((n - 1).log2 + 2) / 2)

/-- Use the reference square procedure in the shared small-input precheck. -/
def referencePrecheck (n : ℕ) : Option Bool :=
  if n < 2 then some false
  else
    if n = 2 then some true
    else if Even n then some false else if referenceSquare n then some false else none

/-- Replacing the square procedure preserves the precheck on every input. -/
theorem referencePrecheck_eq (n : ℕ) :
    referencePrecheck n = PseudoPrime.PrimeTest.primalityPrecheck n := by
  rw [referencePrecheck, referenceSquare_eq]
  rfl

/-- Batch removal with the mathematical two-adic decomposition preserves the reference result. -/
theorem jacobiBatch_decomposition (a n : ℕ) (hn : n % 2 = 1) :
    jacobiBatch (padicValNat 2 a) (Nat.divMaxPow a 2) n = jacobiNat a n := by
  rw [jacobiBatch_eq _ _ _ hn, PseudoPrime.PrimeTest.twoAdicPart_mul_oddPart]

/-- Python's bit mask flips the factor-two sign exactly at residues three and five modulo eight. -/
theorem jacobi_two_mask (n : ℕ) : ((n + 2) &&& 5 = 5) ↔ n % 8 = 3 ∨ n % 8 = 5 := by
  have hb : (n + 2) &&& 5 < 2 ^ 3 := Nat.and_lt_two_pow (n + 2) (by decide : 5 < 2 ^ 3)
  have hm : (n + 2) &&& 5 = ((n % 8 + 2) % 8) &&& 5 := by
    calc
      _ = ((n + 2) &&& 5) % 2 ^ 3 := (Nat.mod_eq_of_lt hb).symm
      _ = ((n % 8 + 2) % 8) &&& 5 := by rw [Nat.and_mod_two_pow, Nat.add_mod n 2]
  rw [hm]
  have h := Nat.mod_lt n (by decide : 0 < 8)
  interval_cases hn : n % 8 <;> decide

/-- Low-bit masks equal remainders modulo powers of two, as used by the Python reference. -/
theorem low_mask (n k : ℕ) : n &&& (2 ^ k - 1) = n % 2 ^ k :=
  Nat.and_two_pow_sub_one_eq_mod n k

/-- Factor-two sign computed by the Python reference bit mask. -/
def jacobiPythonTwoSign (n : ℕ) : ℤ :=
  if (n + 2) &&& 5 = 5 then -1 else 1

/-- For an odd modulus, the Python bit-mask sign equals the Jacobi symbol of two. -/
theorem jacobiPythonTwoSign_eq (n : ℕ) (hn : n % 2 = 1) :
    jacobiPythonTwoSign n = jacobiSym 2 n := by
  simp only [jacobiPythonTwoSign, jacobi_two_mask, jacobiSign2 n hn]

/-- The C++ parity-only batch sign preserves the batched reference recursion. -/
theorem jacobiCppBatch_eq (s a n : ℕ) (hn : n % 2 = 1) :
    (if s % 2 = 1 ∧ (n % 8 = 3 ∨ n % 8 = 5) then (-1 : ℤ) else 1) * jacobiNat a n =
      jacobiNat (2 ^ s * a) n := by
  rw [← jacobiBatch_parity]
  exact jacobiBatch_eq s a n hn

end PseudoPrime.PrimeTest.ReferenceArithmetic
