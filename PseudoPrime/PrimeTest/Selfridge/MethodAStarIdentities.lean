/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Lucas.Defs
public import Mathlib.Tactic.Ring

/-!
# Integer identities for Selfridge Method A and Method A*

The identities in Appendix `S:Astar` of `bfw-Revised-arXiv-v2.tex` are proved
directly from the Lucas recurrences.  This avoids introducing the algebraic
numbers used in the paper's Binet-formula proof.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Eliminate alternate indices from the integer Lucas `U` recurrence.
For arbitrary integer `P`, `Q` and natural `k`, express `U_(k+4)` using `U_(k+2)` and `U_k`
with coefficients `P^2 - 2Q` and `-Q^2`. Rewrite three consecutive recurrence equations and
normalize algebraically. The even/odd Method A* identities use this two-step recurrence.
-/
private theorem lucasU_four_step (P Q : ℤ) (k : ℕ) :
    lucasU P Q (k + 4) = (P * P - 2 * Q) * lucasU P Q (k + 2) - Q * Q * lucasU P Q k := by
  have h3 := lucasU_succ_succ P Q (k + 2)
  have h2 := lucasU_succ_succ P Q k
  have h1 := lucasU_succ_succ P Q (k + 1)
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h3 h2 h1 ⊢
  rw [h3, h1, h2]
  ring

/--
Eliminate alternate indices from the integer Lucas `V` recurrence.
For arbitrary `P`, `Q`, `k`, obtain the same four-step coefficient formula as for `U`.
The proof substitutes three consecutive recurrence equations and normalizes the ring expression.
This supplies the recurrence for comparing Method A and A* at fixed index parity.
-/
private theorem lucasV_four_step (P Q : ℤ) (k : ℕ) :
    lucasV P Q (k + 4) = (P * P - 2 * Q) * lucasV P Q (k + 2) - Q * Q * lucasV P Q k := by
  have h3 := lucasV_succ_succ P Q (k + 2)
  have h2 := lucasV_succ_succ P Q k
  have h1 := lucasV_succ_succ P Q (k + 1)
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h3 h2 h1 ⊢
  rw [h3, h1, h2]
  ring

/--
At every even index `2m`, the Method A* `U` value is `5^m` times the Method A value.
The integer parameters are `(5, 5)` and `(1, -1)` respectively; no modulus or primality
assumption is used. Two-step induction checks the first two even indices and aligns the
four-step recurrences algebraically. Unit cancellation transfers this identity to modular zeros.
-/
theorem lucasU_methodAStar_even (m : ℕ) : lucasU 5 5 (2 * m) = 5 ^ m * lucasU 1 (-1) (2 * m) := by
  induction m using Nat.twoStepInduction with
  | zero => simp only [lucasU, mul_zero]
  | one => simp only [lucasU, mul_one, mul_zero, sub_zero, pow_one, Int.reduceNeg]
  | more m hm hm1 =>
    have hs := lucasU_four_step 5 5 (2 * m)
    have ho := lucasU_four_step 1 (-1) (2 * m)
    have hm1' : lucasU 5 5 (2 + 2 * m) = 5 ^ (m + 1) * lucasU 1 (-1) (2 + 2 * m) := by
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hm1
    simp only [Nat.mul_add, Nat.add_comm] at hs ho hm1' ⊢
    rw [hs, ho, hm1', hm]
    ring_nf

/--
At every even index `2m`, `V_(2m)(5,5) = 5^m * V_(2m)(1,-1)` over the integers.
Two-step induction checks the initial cases and substitutes the common four-step recurrence.
This is the even-index companion identity used in exceptional-discriminant Method A/A*
comparisons, without imposing any modulus or primality hypothesis.
-/
theorem lucasV_methodAStar_even (m : ℕ) : lucasV 5 5 (2 * m) = 5 ^ m * lucasV 1 (-1) (2 * m) := by
  induction m using Nat.twoStepInduction with
  | zero => simp only [lucasV, pow_zero, one_mul]
  | one => norm_num only [lucasV]
  | more m hm hm1 =>
    have hs := lucasV_four_step 5 5 (2 * m)
    have ho := lucasV_four_step 1 (-1) (2 * m)
    have hm1' : lucasV 5 5 (2 + 2 * m) = 5 ^ (m + 1) * lucasV 1 (-1) (2 + 2 * m) := by
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hm1
    simp only [Nat.mul_add, Nat.add_comm] at hs ho hm1' ⊢
    rw [hs, ho, hm1', hm]
    ring_nf

/--
At every odd index `2m+1`, the Method A* `U` value equals `5^m` times Method A's `V` value.
The identity compares integer sequences with parameters `(5,5)` and `(1,-1)`.
Two-step induction and the four-step recurrences prove the cross-sequence formula after
checking the first two odd indices. It supplies the odd-index branch of Method A* equivalence.
-/
theorem lucasU_methodAStar_odd (m : ℕ) :
    lucasU 5 5 (2 * m + 1) = 5 ^ m * lucasV 1 (-1) (2 * m + 1) := by
  induction m using Nat.twoStepInduction with
  | zero => simp only [lucasU, pow_zero, lucasV, mul_one]
  | one => norm_num only [lucasU, lucasV]
  | more m hm hm1 =>
    have hs := lucasU_four_step 5 5 (2 * m + 1)
    have ho := lucasV_four_step 1 (-1) (2 * m + 1)
    have hm' : lucasU 5 5 (1 + 2 * m) = 5 ^ m * lucasV 1 (-1) (1 + 2 * m) := by
      simpa only [Nat.add_comm] using hm
    have hm1' : lucasU 5 5 (2 + (2 * m + 1)) = 5 ^ (m + 1) * lucasV 1 (-1) (2 + (2 * m + 1)) := by
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hm1
    simp only [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hs ho hm1' ⊢
    rw [hs, ho, hm1', hm']
    ring_nf

/--
At every odd index `2m+1`, Method A*'s `V` value equals `5^(m+1)` times Method A's `U` value.
This is an integer identity for parameters `(5,5)` and `(1,-1)`, with no primality premise.
Check two initial odd indices, then use two-step induction and the four-step recurrences.
Modular Strong Lucas comparisons use this companion cross-sequence identity.
-/
theorem lucasV_methodAStar_odd (m : ℕ) :
    lucasV 5 5 (2 * m + 1) = 5 ^ (m + 1) * lucasU 1 (-1) (2 * m + 1) := by
  induction m using Nat.twoStepInduction with
  | zero => simp only [lucasV, zero_add, pow_one, lucasU, mul_one]
  | one => norm_num only [lucasU, lucasV]
  | more m hm hm1 =>
    have hs := lucasV_four_step 5 5 (2 * m + 1)
    have ho := lucasU_four_step 1 (-1) (2 * m + 1)
    have hm' : lucasV 5 5 (1 + 2 * m) = 5 ^ (m + 1) * lucasU 1 (-1) (1 + 2 * m) := by
      simpa only [Nat.add_comm] using hm
    have hm1' : lucasV 5 5 (2 + (2 * m + 1)) = 5 ^ (m + 2) * lucasU 1 (-1) (2 + (2 * m + 1)) := by
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        pow_succ] using hm1
    simp only [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hs ho hm1' ⊢
    rw [hs, ho, hm1', hm']
    ring_nf

end PseudoPrime.PrimeTest
