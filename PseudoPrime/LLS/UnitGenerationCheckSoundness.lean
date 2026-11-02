/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.UnitGenerationCheckCore
public import Mathlib.Data.Nat.Prime.Basic

/-! # Basic soundness of finite LLS generation checks

This proof layer certifies the fixed label table used by LLS certificates and extracts pointwise
results from balanced Boolean checks. It is used after finite computation, rather than by the
expensive certificate data blocks.

Keep this layer outside the computational import boundary. Importing it from a finite certificate
block would make additions or changes to its declarations and dependencies invalidate that finite
proof and potentially repeat expensive kernel computation.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- The complete fixed label table passes the finite primality test.
Proof: kernel computation. Role: certify labels once outside the heavy data modules. -/
private theorem unitGenerationPrimes_check :
    (unitGenerationPrimes.all fun p ↦ decide p.Prime) = true :=
  of_decide_eq_true rfl

/-- Each accepted label is prime.
Input: membership in the fixed label list. Claim: primality of that label.
Proof: extract the member's checked Boolean result. Role: validate generator rows. -/
theorem prime_of_mem_unitGenerationPrimes {p : ℕ} (h : p ∈ unitGenerationPrimes) : p.Prime := by
  exact of_decide_eq_true (List.all_eq_true.mp unitGenerationPrimes_check p h)

/-- A successful balanced check supplies every predicate value in its interval.
Input: a true check and lower/upper bounds for an index.
Claim: the predicate is true there; induction selects the corresponding half.
Role: extract one modulus certificate from a checked window. -/
theorem unitGenerationAll_sound {f : ℕ → Bool} {depth start i : ℕ}
    (h : unitGenerationAll f depth start = true) (hl : start ≤ i) (hu : i < start + 2 ^ depth) :
    f i = true := by
  induction depth generalizing start
  case zero =>
    have he : i = start := Nat.le_antisymm (Nat.le_of_lt_succ hu) hl
    exact he.symm ▸ h
  case succ depth ih =>
    have hc := Bool.and_eq_true_iff.mp h
    by_cases hm : i < start + 2 ^ depth
    · exact ih hc.1 hl hm
    · rw [Nat.pow_succ, Nat.mul_two, ← Nat.add_assoc] at hu
      exact ih hc.2 (Nat.le_of_not_gt hm) hu

end PseudoPrime.LLS
