/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Lucas sequences

The integer-valued Lucas sequences are kept separate from their `ZMod`
images so that the same specification can be used for symbolic proofs and
executable parameter searches.
-/

namespace PseudoPrime.PrimeTest

/-- The Lucas `U` sequence with parameters `P` and `Q`. -/
def lucasU (P Q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => P * lucasU P Q (k + 1) - Q * lucasU P Q k

/-- The Lucas `V` sequence with parameters `P` and `Q`. -/
def lucasV (P Q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => P
  | k + 2 => P * lucasV P Q (k + 1) - Q * lucasV P Q k

/-- The `U` sequence viewed in `ZMod n`. -/
def lucasUZMod (n : ℕ) (P Q : ℤ) (k : ℕ) : ZMod n :=
  lucasU P Q k

/-- The `V` sequence viewed in `ZMod n`. -/
def lucasVZMod (n : ℕ) (P Q : ℤ) (k : ℕ) : ZMod n :=
  lucasV P Q k

/-- The power of the Lucas parameter `Q` used by doubling formulas. -/
def lucasQPow (Q : ℤ) : ℕ → ℤ
  | k => Q ^ k

theorem lucasQPow_zero (Q : ℤ) : lucasQPow Q 0 = 1 := by simp only [lucasQPow, pow_zero]

theorem lucasQPow_succ (Q : ℤ) (k : ℕ) : lucasQPow Q (k + 1) = Q * lucasQPow Q k := by
  simp only [lucasQPow, pow_succ, mul_comm]

/-- The initial values of the Lucas `U` sequence. -/
theorem lucasU_zero (P Q : ℤ) : lucasU P Q 0 = 0 := by rfl

theorem lucasU_one (P Q : ℤ) : lucasU P Q 1 = 1 := by rfl

/-- The initial values of the Lucas `V` sequence. -/
theorem lucasV_zero (P Q : ℤ) : lucasV P Q 0 = 2 := by rfl

theorem lucasV_one (P Q : ℤ) : lucasV P Q 1 = P := by rfl

/-- The recurrence for `U`. -/
theorem lucasU_succ_succ (P Q : ℤ) (k : ℕ) :
    lucasU P Q (k + 2) = P * lucasU P Q (k + 1) - Q * lucasU P Q k := by rfl

/-- The recurrence for `V`. -/
theorem lucasV_succ_succ (P Q : ℤ) (k : ℕ) :
    lucasV P Q (k + 2) = P * lucasV P Q (k + 1) - Q * lucasV P Q k := by rfl

/-- The first doubling identity for `U`. -/
theorem lucasU_two (P Q : ℤ) : lucasU P Q 2 = P := by
  simp only [lucasU, mul_one, mul_zero, sub_zero]

/-- The first doubling identity for `V`. -/
theorem lucasV_two (P Q : ℤ) : lucasV P Q 2 = P * P - Q * 2 := by simp only [lucasV]

/-- The first nontrivial power update for `Q`. -/
theorem lucasQPow_one (Q : ℤ) : lucasQPow Q 1 = Q := by simp only [lucasQPow, pow_one]

/-- Addition formula for `U`, in a form that avoids a negative index. -/
theorem lucasU_add_succ (P Q : ℤ) (m : ℕ) :
    ∀ n : ℕ,
      lucasU P Q (m + n + 1) =
        lucasU P Q (m + 1) * lucasU P Q (n + 1) - Q * lucasU P Q m * lucasU P Q n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => rw [Nat.add_zero, lucasU_zero, lucasU_one, mul_one, mul_zero, sub_zero]
  | one =>
    rw [lucasU_succ_succ, lucasU_two, lucasU_one, mul_one]
    ring
  | more n hn
    hn1 =>
    have hn1' :
      lucasU P Q (m + n + 2) =
        lucasU P Q (m + 1) * lucasU P Q (n + 2) - Q * lucasU P Q m * lucasU P Q (n + 1) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn1
    have hrec1 : lucasU P Q (n + 3) = P * lucasU P Q (n + 2) - Q * lucasU P Q (n + 1) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lucasU_succ_succ P Q (n + 1)
    have hrec0 : lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lucasU_succ_succ P Q n
    calc
      lucasU P Q (m + (n + 2) + 1) = P * lucasU P Q (m + n + 2) - Q * lucasU P Q (m + n + 1) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          lucasU_succ_succ P Q (m + n + 1)
      _ =
          P * (lucasU P Q (m + 1) * lucasU P Q (n + 2) - Q * lucasU P Q m * lucasU P Q (n + 1)) -
            Q * (lucasU P Q (m + 1) * lucasU P Q (n + 1) - Q * lucasU P Q m * lucasU P Q n) :=
        by rw [hn1', hn]
      _ = lucasU P Q (m + 1) * lucasU P Q (n + 3) - Q * lucasU P Q m * lucasU P Q (n + 2) := by
        rw [hrec1, hrec0]
        ring

/-- The `V` sequence is the companion expression in consecutive `U` values. -/
theorem lucasV_succ_eq_lucasU_succ_succ_sub (P Q : ℤ) :
    ∀ n : ℕ, lucasV P Q (n + 1) = lucasU P Q (n + 2) - Q * lucasU P Q n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [lucasV_one, lucasU_succ_succ, lucasU_one, lucasU_zero, mul_zero, sub_zero]
    ring_nf
  | one =>
    rw [lucasV_succ_succ, lucasV_one, lucasV_zero, lucasU_succ_succ, lucasU_succ_succ, lucasU_one,
      lucasU_zero, mul_zero, sub_zero]
    ring_nf
  | more n hn
    hn1 =>
    have hn' : lucasV P Q (n + 2) = lucasU P Q (n + 3) - Q * lucasU P Q (n + 1) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn1
    calc
      lucasV P Q (n + 3) = P * lucasV P Q (n + 2) - Q * lucasV P Q (n + 1) := by
        simpa only [Nat.add_assoc] using lucasV_succ_succ P Q (n + 1)
      _ =
          P * (lucasU P Q (n + 3) - Q * lucasU P Q (n + 1)) -
            Q * (lucasU P Q (n + 2) - Q * lucasU P Q n) :=
        by rw [hn', hn]
      _ = lucasU P Q (n + 4) - Q * lucasU P Q (n + 2) := by
        rw [lucasU_succ_succ P Q (n + 2), lucasU_succ_succ P Q (n + 1), lucasU_succ_succ P Q n]
        ring_nf

/-- The first standard doubling formula for the Lucas `U` sequence. -/
theorem lucasU_two_mul (P Q : ℤ) : ∀ k : ℕ, lucasU P Q (2 * k) = lucasU P Q k * lucasV P Q k := by
  intro k
  induction k with
  | zero => rw [Nat.mul_zero, lucasU_zero, lucasV_zero, zero_mul]
  | succ k ih =>
    have hadd := lucasU_add_succ P Q (k + 1) k
    have hcomp := lucasV_succ_eq_lucasU_succ_succ_sub P Q k
    calc
      lucasU P Q (2 * (k + 1)) = lucasU P Q ((k + 1) + k + 1) := by
        congr 1
        ring
      _ = lucasU P Q (k + 2) * lucasU P Q (k + 1) - Q * lucasU P Q (k + 1) * lucasU P Q k := hadd
      _ = lucasU P Q (k + 1) * lucasV P Q (k + 1) := by
        rw [hcomp]
        ring

/-- The companion doubling-plus-one formula for the Lucas `U` sequence. -/
theorem lucasU_two_mul_add_one (P Q : ℤ) (k : ℕ) :
    lucasU P Q (2 * k + 1) = lucasU P Q (k + 1) ^ 2 - Q * lucasU P Q k ^ 2 := by
  calc
    lucasU P Q (2 * k + 1) = lucasU P Q (k + (k + 1)) := by
      congr 1
      ring
    _ = lucasU P Q (k + 1) * lucasU P Q (k + 1) - Q * lucasU P Q k * lucasU P Q k :=
      lucasU_add_succ P Q k k
    _ = lucasU P Q (k + 1) ^ 2 - Q * lucasU P Q k ^ 2 := by ring

/-- Cassini's identity for the Lucas `U` sequence. -/
theorem lucasU_cassini (P Q : ℤ) :
    ∀ k : ℕ, lucasU P Q (k + 1) ^ 2 - lucasU P Q (k + 2) * lucasU P Q k = Q ^ k := by
  intro k
  induction k with
  | zero => rw [lucasU_one, lucasU_succ_succ, lucasU_zero, mul_zero, sub_zero, one_pow, pow_zero]
  | succ k
    ih =>
    have hrec2 : lucasU P Q (k + 2) = P * lucasU P Q (k + 1) - Q * lucasU P Q k := by
      exact lucasU_succ_succ P Q k
    have hrec3 : lucasU P Q (k + 3) = P * lucasU P Q (k + 2) - Q * lucasU P Q (k + 1) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lucasU_succ_succ P Q (k + 1)
    calc
      lucasU P Q (k + 1 + 1) ^ 2 - lucasU P Q (k + 1 + 2) * lucasU P Q (k + 1) =
          lucasU P Q (k + 2) ^ 2 -
            (P * lucasU P Q (k + 2) - Q * lucasU P Q (k + 1)) * lucasU P Q (k + 1) :=
        by rw [hrec3]
      _ = Q * (lucasU P Q (k + 1) ^ 2 - lucasU P Q (k + 2) * lucasU P Q k) := by
        rw [hrec2]
        ring
      _ = Q ^ (k + 1) := by
        rw [ih, pow_succ]
        ring

/-- The standard doubling formula for the Lucas `V` sequence. -/
theorem lucasV_two_mul (P Q : ℤ) :
    ∀ k : ℕ, lucasV P Q (2 * k) = lucasV P Q k ^ 2 - 2 * lucasQPow Q k := by
  intro k
  induction k with
  | zero =>
    rw [Nat.mul_zero, lucasV_zero, lucasQPow_zero]
    ring
  | succ k
    ih =>
    have hcomp : lucasV P Q (2 * k + 2) = lucasU P Q (2 * k + 3) - Q * lucasU P Q (2 * k + 1) := by
      convert lucasV_succ_eq_lucasU_succ_succ_sub P Q (2 * k + 1) using 1
    have huodd : lucasU P Q (2 * k + 1) = lucasU P Q (k + 1) ^ 2 - Q * lucasU P Q k ^ 2 :=
      lucasU_two_mul_add_one P Q k
    have huodd' : lucasU P Q (2 * k + 3) = lucasU P Q (k + 2) ^ 2 - Q * lucasU P Q (k + 1) ^ 2 := by
      convert lucasU_two_mul_add_one P Q (k + 1) using 1
    have hcomp' : lucasV P Q (k + 1) = lucasU P Q (k + 2) - Q * lucasU P Q k :=
      lucasV_succ_eq_lucasU_succ_succ_sub P Q k
    have hc := lucasU_cassini P Q k
    calc
      lucasV P Q (2 * (k + 1)) = lucasV P Q (2 * k + 2) := by ring_nf
      _ = lucasU P Q (2 * k + 3) - Q * lucasU P Q (2 * k + 1) := hcomp
      _ =
          (lucasU P Q (k + 2) ^ 2 - Q * lucasU P Q (k + 1) ^ 2) -
            Q * (lucasU P Q (k + 1) ^ 2 - Q * lucasU P Q k ^ 2) :=
        by rw [huodd', huodd]
      _ = lucasV P Q (k + 1) ^ 2 - 2 * lucasQPow Q (k + 1) := by
        rw [hcomp']
        change _ = _ - 2 * (Q ^ (k + 1))
        rw [show Q ^ (k + 1) = Q ^ k * Q by rw [pow_succ]]
        have hc' := congrArg (fun z : ℤ => Q * z) hc
        rw [mul_comm (Q ^ k) Q]
        rw [← hc']
        ring

/-- The companion doubling-plus-one formula for the Lucas `V` sequence. -/
theorem lucasV_two_mul_add_one (P Q : ℤ) (k : ℕ) :
    lucasV P Q (2 * k + 1) = lucasV P Q (k + 1) * lucasV P Q k - P * lucasQPow Q k := by
  induction k with
  | zero =>
    rw [Nat.mul_zero, lucasV_one, lucasV_zero, lucasQPow_zero]
    ring
  | succ k
    ih =>
    have heven : lucasV P Q (2 * k + 2) = lucasV P Q (k + 1) ^ 2 - 2 * lucasQPow Q (k + 1) := by
      convert lucasV_two_mul P Q (k + 1) using 1
    calc
      lucasV P Q (2 * (k + 1) + 1) = P * lucasV P Q (2 * k + 2) - Q * lucasV P Q (2 * k + 1) := by
        convert lucasV_succ_succ P Q (2 * k + 1) using 1
      _ =
          P * (lucasV P Q (k + 1) ^ 2 - 2 * lucasQPow Q (k + 1)) -
            Q * (lucasV P Q (k + 1) * lucasV P Q k - P * lucasQPow Q k) :=
        by rw [heven, ih]
      _ = lucasV P Q (k + 2) * lucasV P Q (k + 1) - P * lucasQPow Q (k + 1) := by
        rw [lucasV_succ_succ, lucasQPow_succ]
        ring

end PseudoPrime.PrimeTest
