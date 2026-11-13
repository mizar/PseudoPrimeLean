/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.UnitGenerationCoverSoundness
public import PseudoPrime.LLS.Theorem11S1Subgroup

/-! # Shared unit-witness conversion and product checks at moduli three through five -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a small modulus. Definition: product codes 130,131,258 for moduli three,four,five.
Output: an integer code. Role: certify these three unit groups with prime cap five. -/
def retainedSavingSmallCode (q : ℕ) : ℕ :=
  if q = 3 then 130 else if q = 4 then 131 else 258

/-- Select a packed divisor code for the three smallest precise-saving moduli.
Definition: return 4098 at four and the input modulus otherwise.
Input: any natural modulus. Output: divisor two at level one for four, and divisor q at
level zero for three or five. Role: supply nonunit bits in the three checked certificate pairs. -/
def retainedSavingSmallDivisor (q : ℕ) : ℕ :=
  if q = 4 then 4098 else q

/-- The three small certificate pairs pass exact product-and-divisor coverage.
Input: a modulus below six and at least three. Claim: coverage passes with prime cap five.
Proof: kernel reduction of the finite proposition. Role: certify the small precise-saving range. -/
theorem retained_saving_small_coverage :
    ∀ q : Fin 6,
      3 ≤ q.val →
        unitGenerationCoverCheck q.val 5 (q.val.log2 + 1) (retainedSavingSmallCode q.val)
            (retainedSavingSmallDivisor q.val) =
          true :=
  of_decide_eq_true rfl

end PseudoPrime.LLS
