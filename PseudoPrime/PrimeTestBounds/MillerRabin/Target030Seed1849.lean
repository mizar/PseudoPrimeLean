/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed1849Checks

/-! # Certified prime supply through 1849 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
/-- The five checked chunks certify that every added label is prime and lies
strictly above 373 and at most 1849. -/
theorem target030Extra1849_prime : ∀ p ∈ target030Extra1849, p.Prime ∧ 373 < p ∧ p ≤ 1849 := by
  have hs :
    target030Extra1849 =
      (target030Extra1849.take 45) ++ ((target030Extra1849.drop 45).take 45) ++
        ((target030Extra1849.drop 90).take 45) ++
        ((target030Extra1849.drop 135).take 45) ++
        ((target030Extra1849.drop 180).take 45) := by
    rfl
  have hall : target030Extra1849.all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) = true := by
    have h1 := target030Extra1849_checked1
    simp only [List.drop_zero] at h1
    rw [hs]
    simp only [List.all_append, h1, target030Extra1849_checked2, target030Extra1849_checked3,
      target030Extra1849_checked4, target030Extra1849_checked5]
    rfl
  intro p hp
  exact of_decide_eq_true ((List.all_eq_true.mp hall) p hp)

/-- Every label in the combined supply is prime and at most 1849. -/
theorem target030Seed1849_prime_supply : ∀ p ∈ target030Seed1849Primes, p.Prime ∧ p ≤ 1849 := by
  intro p hp
  simp only [target030Seed1849Primes, List.mem_append] at hp
  rcases hp with hnew | hold
  · exact ⟨(target030Extra1849_prime p hnew).1, (target030Extra1849_prime p hnew).2.2⟩
  · exact
      ⟨(target030Seed373_prime_supply p hold).1,
        (target030Seed373_prime_supply p hold).2.trans (by decide)⟩

/-- Each scaled weight dominates its prime label's logarithm. The added
labels use the certified logarithm of the common cutoff 1849. -/
theorem target030Seed1849_weight_bounds :
    ∀ p ∈ target030Seed1849Primes, Real.log p ≤ (target030Seed1849Weight p : ℝ) / 10 := by
  have hB :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1849 11 16 7 (76 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hB
  intro p hp
  simp only [target030Seed1849Primes, List.mem_append] at hp
  rcases hp with hnew | hold
  · have hx := target030Extra1849_prime p hnew
    have hl := Real.log_le_log (Nat.cast_pos.mpr hx.1.pos) (Nat.cast_le.mpr hx.2.2)
    simp only [target030Seed1849Weight, ite_eq_right (Nat.not_le_of_gt hx.2.1), Nat.cast_ofNat]
    norm_num only [Nat.cast_ofNat] at hl
    linarith only [hl, hB]
  · have hp373 := (target030Seed373_prime_supply p hold).2
    simpa only [target030Seed1849Weight, ite_eq_left hp373] using
      target030Seed373_weight_bounds p hold

end PseudoPrime.PrimeTestBounds.MillerRabin
