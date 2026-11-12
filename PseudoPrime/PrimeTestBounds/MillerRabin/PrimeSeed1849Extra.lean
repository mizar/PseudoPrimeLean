/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Data
public import Mathlib.Data.Nat.Prime.Basic

/-! # Primality of the additional labels through 1849 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 1 passes its primality and bound checks. -/
private theorem primeSeed1849Extra_checked1 :
    ((primeSeed1849Extra.drop 0).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 2 passes its primality and bound checks. -/
private theorem primeSeed1849Extra_checked2 :
    ((primeSeed1849Extra.drop 45).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 3 passes its primality and bound checks. -/
private theorem primeSeed1849Extra_checked3 :
    ((primeSeed1849Extra.drop 90).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 4 passes its primality and bound checks. -/
private theorem primeSeed1849Extra_checked4 :
    ((primeSeed1849Extra.drop 135).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 5 passes its primality and bound checks. -/
private theorem primeSeed1849Extra_checked5 :
    ((primeSeed1849Extra.drop 180).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- The five checked chunks certify that every added label is prime and lies
strictly above 373 and at most 1849. -/
theorem primeSeed1849Extra_prime : ∀ p ∈ primeSeed1849Extra, p.Prime ∧ 373 < p ∧ p ≤ 1849 := by
  have hs :
    primeSeed1849Extra =
      (primeSeed1849Extra.take 45) ++ ((primeSeed1849Extra.drop 45).take 45) ++
        ((primeSeed1849Extra.drop 90).take 45) ++
        ((primeSeed1849Extra.drop 135).take 45) ++
        ((primeSeed1849Extra.drop 180).take 45) := by
    rfl
  have hall : primeSeed1849Extra.all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) = true := by
    have h1 := primeSeed1849Extra_checked1
    simp only [List.drop_zero] at h1
    rw [hs]
    simp only [List.all_append, h1, primeSeed1849Extra_checked2, primeSeed1849Extra_checked3,
      primeSeed1849Extra_checked4, primeSeed1849Extra_checked5]
    rfl
  intro p hp
  exact of_decide_eq_true ((List.all_eq_true.mp hall) p hp)

end PseudoPrime.PrimeTestBounds.MillerRabin
