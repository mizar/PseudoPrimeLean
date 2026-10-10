/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring

/-!
# Lucas sequences

The integer-valued Lucas sequences are kept separate from their `ZMod`
images so that the same specification can be used for symbolic proofs and
executable parameter searches.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Integer Lucas sequence with U_0 = 0, U_1 = 1 and
U_{k+2} = P U_{k+1} - Q U_k for arbitrary signed parameters.
Its casts supply the proof-side modular sequence and the executable doubling contracts.
-/
def lucasU (P Q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => P * lucasU P Q (k + 1) - Q * lucasU P Q k

/--
Integer companion Lucas sequence with V_0 = 2, V_1 = P and
V_{k+2} = P V_{k+1} - Q V_k. No primality or discriminant assumption is imposed;
the modular images are used by Lucas-V and Strong Lucas tests.
-/
def lucasV (P Q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => P
  | k + 2 => P * lucasV P Q (k + 1) - Q * lucasV P Q k

/--
Cast the integer U_k(P,Q) to ZMod n for any natural modulus and index.
This proof-side definition is the specification for the fast modular recurrence.
-/
def lucasUZMod (n : ℕ) (P Q : ℤ) (k : ℕ) : ZMod n :=
  lucasU P Q k

/--
Cast the integer V_k(P,Q) to ZMod n for any natural modulus and index.
The fast V computation and the Strong Lucas scan are compared with this specification.
-/
def lucasVZMod (n : ℕ) (P Q : ℤ) (k : ℕ) : ZMod n :=
  lucasV P Q k

/--
The signed integer power Q^k retained by the Lucas doubling formulas.
Its modular cast supplies the Q component of the combined U/V/Q execution state.
-/
def lucasQPow (Q : ℤ) : ℕ → ℤ
  | k => Q ^ k

/--
For every signed Q, the index-zero Q power is one.
Unfold the power definition and use pow_zero to initialize doubling states.
-/
theorem lucasQPow_zero (Q : ℤ) : lucasQPow Q 0 = 1 := by simp only [lucasQPow, pow_zero]

/--
For every Q and k, the next Q power is Q times the current one.
Unfold the definition and commute pow_succ; this aligns recurrence and doubling calculations.
-/
theorem lucasQPow_succ (Q : ℤ) (k : ℕ) : lucasQPow Q (k + 1) = Q * lucasQPow Q k := by
  simp only [lucasQPow, pow_succ, mul_comm]

/--
For arbitrary P and Q, U_0 is zero by the defining recurrence.
This initializes the symbolic and modular Lucas-U calculations.
-/
theorem lucasU_zero (P Q : ℤ) : lucasU P Q 0 = 0 := by rfl

/--
For arbitrary P and Q, U_1 is one by definition.
This supplies the second base case of the Lucas-U recurrence proofs.
-/
theorem lucasU_one (P Q : ℤ) : lucasU P Q 1 = 1 := by rfl

/--
For arbitrary P and Q, V_0 is two by definition.
This initializes the companion sequence and its modular implementation.
-/
theorem lucasV_zero (P Q : ℤ) : lucasV P Q 0 = 2 := by rfl

/--
For arbitrary P and Q, V_1 is P by definition.
This supplies the second base case of companion-sequence recurrence proofs.
-/
theorem lucasV_one (P Q : ℤ) : lucasV P Q 1 = P := by rfl

/--
For arbitrary signed parameters, U_{k+2} = P U_{k+1} - Q U_k.
The equality is definitional and exposes the recurrence for sequence identities.
-/
theorem lucasU_succ_succ (P Q : ℤ) (k : ℕ) :
    lucasU P Q (k + 2) = P * lucasU P Q (k + 1) - Q * lucasU P Q k := by rfl

/--
For arbitrary signed parameters, V_{k+2} = P V_{k+1} - Q V_k.
The definitional equality is used in companion and doubling proofs.
-/
theorem lucasV_succ_succ (P Q : ℤ) (k : ℕ) :
    lucasV P Q (k + 2) = P * lucasV P Q (k + 1) - Q * lucasV P Q k := by rfl

/--
For every P and Q, U_2 = P.
Evaluate the first recurrence step using U_0 and U_1; this is an addition-formula base case.
-/
theorem lucasU_two (P Q : ℤ) : lucasU P Q 2 = P := by
  simp only [lucasU, mul_one, mul_zero, sub_zero]

/--
For every P and Q, V_2 = P*P - 2*Q.
Evaluate the recurrence at zero; this supplies a base case for companion identities.
-/
theorem lucasV_two (P Q : ℤ) : lucasV P Q 2 = P * P - Q * 2 := by simp only [lucasV]

/--
For every signed Q, its index-one power is Q.
Unfold and use pow_one to initialize power updates.
-/
theorem lucasQPow_one (Q : ℤ) : lucasQPow Q 1 = Q := by simp only [lucasQPow, pow_one]

/--
For all natural m,n and signed P,Q, express U_{m+n+1} as
U_{m+1} U_{n+1} - Q U_m U_n, avoiding negative indices.
Two-step induction on n propagates both recurrences; the result supplies U doubling formulas.
-/
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

/--
For every n, V_{n+1} = U_{n+2} - Q U_n for the same signed parameters.
Two-step induction compares the recurrences and their initial values.
This companion identity reduces V doubling to U identities.
-/
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

/--
For arbitrary signed P,Q and natural k, U_{2k} = U_k V_k.
Separate k=0, then combine the addition and companion identities at the successor.
The result is the U update used by binary Lucas evaluation.
-/
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

/--
For arbitrary P,Q and k, U_{2k+1} = U_{k+1}^2 - Q U_k^2.
Specialize the addition identity to equal indices and normalize products as squares.
This gives the odd-index branch of binary Lucas evaluation.
-/
theorem lucasU_two_mul_add_one (P Q : ℤ) (k : ℕ) :
    lucasU P Q (2 * k + 1) = lucasU P Q (k + 1) ^ 2 - Q * lucasU P Q k ^ 2 := by
  calc
    lucasU P Q (2 * k + 1) = lucasU P Q (k + (k + 1)) := by
      congr 1
      ring
    _ = lucasU P Q (k + 1) * lucasU P Q (k + 1) - Q * lucasU P Q k * lucasU P Q k :=
      lucasU_add_succ P Q k k
    _ = lucasU P Q (k + 1) ^ 2 - Q * lucasU P Q k ^ 2 := by ring

/--
For every k, U_{k+1}^2 - U_{k+2} U_k = Q^k.
Induction factors each successor difference by Q using the recurrence.
The identity supplies the correction term in the V doubling formula.
-/
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

/--
For arbitrary P,Q and k, V_{2k} = V_k^2 - 2 Q^k.
After the zero case, express V in U, apply odd-index U formulas and Cassini.
This is the companion update used by modular doubling scans.
-/
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

/--
For arbitrary P,Q and k, V_{2k+1} = V_{k+1} V_k - P Q^k.
Induction uses the even V doubling identity and the V/Q recurrences.
The result supplies the odd-index companion update.
-/
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
