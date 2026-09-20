/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.Jacobi.Numerator
import Mathlib.FieldTheory.Finite.Basic

/-!
# Smaller prime witnesses for odd nonsquares

This file constructs explicit Jacobi denominators and extracts prime witnesses from them.
For any `r > 3` congruent to `3` modulo `4`, the denominator is `r - 8` or `r - 2`, according
to the residue modulo `8`; neither primality nor nonsquareness of `r` is required in this case.
For `r` congruent to `1` modulo `4`, an odd nonsquare `r` admits a Jacobi `-1` numerator by a
finite CRT construction.  Quadratic reciprocity and prime-factor extraction then show that
every odd nonsquare `r > 3` has a smaller odd-prime denominator with Jacobi value `-1`.
-/

namespace PseudoPrime.NumberTheory

namespace Internal

/--
An odd positive denominator below `r` with Jacobi value `J(r | m) = -1` contains a smaller odd
prime divisor with the same `-1` value.
-/
theorem exists_smaller_odd_prime_of_jacobi_eq_neg_one {r m : ℕ} (hmpos : 0 < m) (hmlt : m < r)
    (hmodd : Odd m) (hvalue : jacobiSym r m = -1) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ q < r ∧ jacobiSym r q = -1 := by
  obtain ⟨q, hqprime, hqdvd, hqvalue⟩ := exists_prime_dvd_jacobi_eq_neg_one hvalue
  have hqle : q ≤ m := Nat.le_of_dvd hmpos hqdvd
  exact ⟨q, hqprime, hmodd.of_dvd_nat hqdvd, hqle.trans_lt hmlt, hqvalue⟩

end Internal

/--
For a prime `r` congruent to `1` modulo `4`, there is a positive odd nonsquare representative
strictly below `r`.  If the representative supplied by the finite-field theorem is even, its
negative is odd; multiplication by the square `-1` preserves nonsquareness.
-/
theorem exists_odd_nonsquare_lt_of_prime_mod_four_one {r : ℕ} (hr : r.Prime) (hr4 : r % 4 = 1) :
    ∃ m : ℕ, Odd m ∧ 0 < m ∧ m < r ∧ jacobiSym m r = -1 := by
  let _ : Fact r.Prime := ⟨hr⟩
  obtain ⟨a, ha⟩ :=
    FiniteField.exists_nonsquare (F := ZMod r) (by exact (ZMod.ringChar_zmod_n r).substr (by omega))
  have ha0 : a ≠ 0 := by
    intro ha0
    apply ha
    exact ha0.symm ▸ ⟨0, by norm_num only⟩
  have hnegOne : IsSquare (-1 : ZMod r) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  let b : ZMod r := if Odd a.val then a else -a
  have hb : ¬IsSquare b := by
    simp only [b]
    split
    · exact ha
    · intro hnega
      apply ha
      have hproduct := hnegOne.mul hnega
      simpa only [neg_mul, one_mul, neg_neg] using hproduct
  have hbodd : Odd b.val := by
    simp only [b]
    split
    · assumption
    · rw [ZMod.neg_val, ite_eq_right ha0]
      have hrodd : Odd r := Nat.odd_iff.mpr (by omega)
      have haeven : Even a.val := Nat.not_odd_iff_even.mp (by assumption)
      obtain ⟨k, hk⟩ := hrodd
      obtain ⟨l, hl⟩ := haeven
      have hale : a.val ≤ r := a.val_lt.le
      exact ⟨k - l, by omega⟩
  have hb0 : b.val ≠ 0 := by
    intro hb0
    apply hb
    have : b = 0 := by
      rw [← ZMod.natCast_zmod_val b, hb0]
      norm_num only
    exact this.symm ▸ ⟨0, by norm_num only⟩
  refine ⟨b.val, hbodd, Nat.pos_of_ne_zero hb0, b.val_lt, ?_⟩
  apply ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hb

/--
For any odd `r = 1 mod 4`, a residue class with Jacobi value `-1` has a positive odd
representative below `r` with the same value.  This statement does not require `r` to be prime.
-/
theorem exists_odd_neg_one_numerator_lt_of_mod_four_one {r : ℕ} (hrodd : Odd r) (hr4 : r % 4 = 1)
    (ha : ∃ a : ZMod r, jacobiSym a.val r = -1) :
    ∃ m : ℕ, Odd m ∧ 0 < m ∧ m < r ∧ jacobiSym m r = -1 := by
  let _ : NeZero r :=
    ⟨by
      have hrmod : r % 2 = 1 := Nat.odd_iff.mp hrodd
      omega⟩
  obtain ⟨a, havalue⟩ := ha
  have ha0 : a ≠ 0 := by
    intro ha0
    have hrne1 : r ≠ 1 := by
      intro hr1
      subst r
      rw [jacobiSym.one_right] at havalue
      norm_num only at havalue
    have hr1 : 1 < r := by
      have hrpos : 0 < r := Odd.pos hrodd
      omega
    rw [ha0, ZMod.val_zero] at havalue
    norm_num only [jacobiSym.zero_left hr1] at havalue
  let m : ℕ := if Odd a.val then a.val else r - a.val
  have hmodd : Odd m := by
    simp only [m]
    split
    · assumption
    · have haeven : Even a.val := Nat.not_odd_iff_even.mp (by assumption)
      obtain ⟨k, hk⟩ := hrodd
      obtain ⟨l, hl⟩ := haeven
      have hale : a.val ≤ r := a.val_lt.le
      exact ⟨k - l, by omega⟩
  have hmpos : 0 < m := by
    simp only [m]
    split
    · exact
        Nat.pos_of_ne_zero
          (by
            intro hval
            apply ha0
            rw [← ZMod.natCast_zmod_val a, hval]
            norm_num only)
    · exact Nat.sub_pos_of_lt a.val_lt
  have hmlt : m < r := by
    simp only [m]
    split
    · exact a.val_lt
    · exact
        Nat.sub_lt (by omega)
          (Nat.pos_of_ne_zero
            (by
              intro hval
              apply ha0
              rw [← ZMod.natCast_zmod_val a, hval]
              norm_num only))
  have hmvalue : jacobiSym m r = -1 := by
    simp only [m]
    split
    · exact havalue
    · have hnegmod : ((r - a.val : ℕ) : ℤ) % r = (-(a.val : ℤ)) % r := by
        rw [Nat.cast_sub a.val_lt.le, Int.emod_eq_emod_iff_emod_sub_eq_zero]
        apply Int.emod_eq_zero_of_dvd
        use 1
        ring
      rw [jacobiSym.mod_left' hnegmod, jacobiSym.neg _ hrodd, ZMod.χ₄_nat_one_mod_four hr4, one_mul]
      exact havalue
  exact ⟨m, hmodd, hmpos, hmlt, hmvalue⟩

/--
For an odd `r` congruent to `1` modulo `4`, existence of one Jacobi `-1` numerator implies
existence of a smaller odd-prime denominator with `J(r | q) = -1`.
-/
theorem exists_smaller_neg_one_witness_of_mod_four_one_of_exists_numerator {r : ℕ} (hrodd : Odd r)
    (hr4 : r % 4 = 1) (ha : ∃ a : ZMod r, jacobiSym a.val r = -1) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ q < r ∧ jacobiSym r q = -1 := by
  obtain ⟨m, hmodd, hmpos, hmlt, hmvalue⟩ :=
    exists_odd_neg_one_numerator_lt_of_mod_four_one hrodd hr4 ha
  have hvalue : jacobiSym r m = -1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four hr4 hmodd]
    exact hmvalue
  exact Internal.exists_smaller_odd_prime_of_jacobi_eq_neg_one hmpos hmlt hmodd hvalue

/--
Every `r > 3` congruent to `3` modulo `4` has a smaller odd-prime denominator `q` with
`J(r | q) = -1`.  Residue `7` modulo `8` uses `m = r - 2`; residue `3` uses `m = r - 8`.
-/
theorem exists_smaller_neg_one_witness_of_mod_four_three {r : ℕ} (hr4 : r % 4 = 3) (hr3 : 3 < r) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ q < r ∧ jacobiSym r q = -1 := by
  have hr8 : r % 8 = 3 ∨ r % 8 = 7 := by
    have hlt := Nat.mod_lt r (by norm_num only : 0 < 8)
    omega
  rcases hr8 with hr8 | hr8
  · let m := r - 8
    have hr11 : 11 ≤ r := by omega
    have hmpos : 0 < m := by
      simp only [m]; omega
    have hmlt : m < r := by
      simp only [m]; omega
    have hm8 : m % 8 = 3 := by
      simp only [m]; omega
    have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
    have hrem : (r : ℤ) % m = (8 : ℤ) % m := by
      have hrsub : r = m + 8 := by
        simp only [m]; omega
      rw [hrsub, Nat.cast_add, Int.add_emod, Int.emod_self, zero_add, Int.emod_emod]
      norm_num only
    have hvalue : jacobiSym r m = -1 := by
      rw [jacobiSym.mod_left' hrem, show (8 : ℤ) = 2 ^ 3 by norm_num only, jacobiSym.pow_left,
        jacobiSym.at_two hmodd]
      simp only [ZMod.χ₈_nat_eq_if_mod_eight, hm8]
      norm_num only [show m % 2 = 1 by omega, ite_false, false_or, or_false]
    exact Internal.exists_smaller_odd_prime_of_jacobi_eq_neg_one hmpos hmlt hmodd hvalue
  · let m := r - 2
    have hmpos : 0 < m := by
      simp only [m]; omega
    have hmlt : m < r := by
      simp only [m]; omega
    have hm8 : m % 8 = 5 := by
      simp only [m]; omega
    have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
    have hrem : (r : ℤ) % m = (2 : ℤ) % m := by
      have hrsub : r = m + 2 := by
        simp only [m]; omega
      rw [hrsub, Nat.cast_add, Int.add_emod, Int.emod_self, zero_add, Int.emod_emod]
      norm_num only
    have hvalue : jacobiSym r m = -1 := by
      rw [jacobiSym.mod_left' hrem, jacobiSym.at_two hmodd]
      simp only [ZMod.χ₈_nat_eq_if_mod_eight, hm8]
      norm_num only [show m % 2 = 1 by omega, ite_false, false_or, or_false]
    exact Internal.exists_smaller_odd_prime_of_jacobi_eq_neg_one hmpos hmlt hmodd hvalue

/--
Every odd nonsquare `r > 3` has a smaller odd-prime denominator with Jacobi value `-1`.
The proof combines the CRT numerator construction with quadratic reciprocity in the `1 mod 4`
branch, and explicit denominators in the `3 mod 4` branch.
-/
theorem oddNonsquareHasSmallerNegOneWitness {r : ℕ} (hrodd : Odd r) (hr3 : 3 < r)
    (hns : ¬IsSquare r) : ∃ q : ℕ, q.Prime ∧ Odd q ∧ q < r ∧ jacobiSym r q = -1 := by
  have hr4 : r % 4 = 1 ∨ r % 4 = 3 := by
    have hlt := Nat.mod_lt r (by norm_num only : 0 < 4)
    have hoddmod : Odd (r % 4) := hrodd.mod_even ⟨2, by omega⟩
    rcases hoddmod with ⟨k, hk⟩
    omega
  rcases hr4 with hr4 | hr4
  · exact
      exists_smaller_neg_one_witness_of_mod_four_one_of_exists_numerator hrodd hr4
        (oddNonsquareHasNegOneNumerator hrodd hns)
  · exact exists_smaller_neg_one_witness_of_mod_four_three hr4 hr3

/--
A prime `r` congruent to `1` modulo `4` has a smaller odd-prime Jacobi `-1` witness.  The odd
nonsquare representative above is transferred by quadratic reciprocity and then factored.
-/
theorem exists_smaller_neg_one_witness_of_prime_mod_four_one {r : ℕ} (hr : r.Prime)
    (hr4 : r % 4 = 1) : ∃ q : ℕ, q.Prime ∧ Odd q ∧ q < r ∧ jacobiSym r q = -1 := by
  obtain ⟨m, hmodd, hmpos, hmlt, hmvalue⟩ := exists_odd_nonsquare_lt_of_prime_mod_four_one hr hr4
  have hvalue : jacobiSym r m = -1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four hr4 hmodd]
    exact hmvalue
  exact Internal.exists_smaller_odd_prime_of_jacobi_eq_neg_one hmpos hmlt hmodd hvalue

/--
Every prime above `3` has a strictly smaller odd-prime denominator at which its Jacobi symbol is
`-1`.  Oddness of `r` follows from primality and the lower bound, so no separate oddness premise
is needed.
-/
theorem primeHasSmallerNegOneWitness {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ q < r ∧ jacobiSym r q = -1 := by
  have hrodd : Odd r := hr.odd_iff.mpr (by omega)
  have hr4 : r % 4 = 1 ∨ r % 4 = 3 := by
    have hlt := Nat.mod_lt r (by norm_num only : 0 < 4)
    have hoddmod : Odd (r % 4) := hrodd.mod_even ⟨2, by omega⟩
    rcases hoddmod with ⟨k, hk⟩
    omega
  rcases hr4 with hr4 | hr4
  · exact exists_smaller_neg_one_witness_of_prime_mod_four_one hr hr4
  · exact exists_smaller_neg_one_witness_of_mod_four_three hr4 hr3

end PseudoPrime.NumberTheory
