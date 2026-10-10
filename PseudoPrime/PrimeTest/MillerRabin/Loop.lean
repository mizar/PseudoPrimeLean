/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Spec

/-!
# Miller–Rabin by successive squaring

The loop checks the current residue before squaring and omits the final unused
square. Its Boolean result agrees with the existing finite-index specification.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- Check at most `s` successive squares of `t` against `target` modulo `n`.
The current residue is checked first. No square is computed after the last
failed comparison. This loop supplies the nontrivial branch of Miller–Rabin. -/
def mrSquareScan (n : ℕ) (target t : ZMod n) : ℕ → Bool
  | 0 => false
  | s + 1 =>
    (t == target) ||
      (match s with
      | 0 => false
      | k + 1 => mrSquareScan n target (t * t) (k + 1))

/-- The successor equation used to prove the loop specification.
The zero-length recursive tail is false, although the executable loop omits
its unused square. This equation connects the optimized loop to induction. -/
theorem mrSquareScan_step (n : ℕ) (target t : ZMod n) (s : ℕ) :
    mrSquareScan n target t (s + 1) = ((t == target) || mrSquareScan n target (t * t) s) := by
  cases s <;> rfl

/-- Squaring the seed advances the tested exponent by one doubling.
This identity transports the recursive tail back to powers of the original seed. -/
theorem mrSquare_pow (n : ℕ) (t : ZMod n) (r : ℕ) : (t * t) ^ (2 ^ r) = t ^ (2 ^ (r + 1)) := by
  rw [← pow_two, ← pow_mul, pow_succ, Nat.mul_comm 2]

/-- The loop succeeds exactly when one of the first `s` doubling exponents
equals the target. Induction and the squaring identity establish the finite
existential used by the Miller–Rabin specification, including `s = 0`. -/
theorem mrSquareScan_spec (n : ℕ) (target t : ZMod n) (s : ℕ) :
    mrSquareScan n target t s = true ↔ ∃ r < s, t ^ (2 ^ r) = target := by
  induction s generalizing t with
  | zero => simp only [mrSquareScan, Bool.false_eq_true, Nat.not_lt_zero, false_and, exists_false]
  | succ s
    ih =>
    rw [mrSquareScan_step, Bool.or_eq_true, beq_iff_eq, ih, Nat.exists_lt_succ_left]
    simp only [pow_zero, pow_one, mrSquare_pow]

/-- Miller–Rabin with one initial modular power and a successive-square loop.
The base is a natural number, and all inputs are totalized as in the existing
fixed-base test. Input prechecking and zero-base skipping are separate concerns. -/
def strongMillerRabinWithBaseLoop (n a : ℕ) : Bool :=
  let s := padicValNat 2 (n - 1)
  let d := Nat.divMaxPow (n - 1) 2
  let t := zmodPow n a d
  (t == 1) || mrSquareScan n (n - 1) t s

/-- The successive-square implementation equals the existing fixed-base test
for every modulus and base. The loop's finite existential is rewritten to the
original modular powers, allowing downstream specifications to be reused. -/
theorem strongMillerRabinWithBaseLoop_eq (n a : ℕ) :
    strongMillerRabinWithBaseLoop n a = strongMillerRabinWithBase n a := by
  apply Bool.eq_iff_iff.mpr
  simp only [strongMillerRabinWithBaseLoop, strongMillerRabinWithBase, Bool.or_eq_true, beq_iff_eq,
    mrSquareScan_spec, decide_eq_true_eq, List.mem_range, zmodPow_eq_pow, ← pow_mul]

end PseudoPrime.PrimeTest
