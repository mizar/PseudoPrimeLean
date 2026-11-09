/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Checks

/-! # Certified prime supply through 1849 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

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

/-- Every label in the combined supply is prime and at most 1849. -/
theorem primeSeed1849_prime_supply : ∀ p ∈ primeSeed1849Primes, p.Prime ∧ p ≤ 1849 := by
  intro p hp
  simp only [primeSeed1849Primes, List.mem_append] at hp
  rcases hp with hnew | hold
  · exact ⟨(primeSeed1849Extra_prime p hnew).1, (primeSeed1849Extra_prime p hnew).2.2⟩
  · exact
      ⟨(primeSeed373_prime_supply p hold).1, (primeSeed373_prime_supply p hold).2.trans (by decide)⟩

/-- Each scaled weight dominates its prime label's logarithm. The added
labels use the certified logarithm of the common cutoff 1849. -/
theorem primeSeed1849_weight_bounds :
    ∀ p ∈ primeSeed1849Primes, Real.log p ≤ (primeSeed1849Weight p : ℝ) / 10 := by
  have hB :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1849 11 16 7 (76 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hB
  intro p hp
  simp only [primeSeed1849Primes, List.mem_append] at hp
  rcases hp with hnew | hold
  · have hx := primeSeed1849Extra_prime p hnew
    have hl := Real.log_le_log (Nat.cast_pos.mpr hx.1.pos) (Nat.cast_le.mpr hx.2.2)
    simp only [primeSeed1849Weight, ite_eq_right (Nat.not_le_of_gt hx.2.1), Nat.cast_ofNat]
    norm_num only [Nat.cast_ofNat] at hl
    linarith only [hl, hB]
  · have hp373 := (primeSeed373_prime_supply p hold).2
    simpa only [primeSeed1849Weight, ite_eq_left hp373] using primeSeed373_weight_bounds p hold

end PseudoPrime.PrimeTestBounds.MillerRabin
