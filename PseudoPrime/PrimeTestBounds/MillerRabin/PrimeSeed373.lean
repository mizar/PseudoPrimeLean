/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed281

/-! # Weighted prime supply through 373 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The supply through 373 extends the earlier distinct prime labels. -/
def primeSeed373Primes : List ℕ :=
  [373, 367, 359, 353, 349, 347, 337, 331, 317, 313, 311, 307, 293, 283] ++ primeSeed281Primes

/-- Scaled logarithmic weights extend the supply through 281. -/
def primeSeed373Weight (p : ℕ) : ℕ :=
  if p ≤ 281 then primeSeed281Weight p
  else if p ≤ 293 then 57 else if p ≤ 317 then 58 else if p ≤ 359 then 59 else 60

/-- Ordered scaled weights retain each prime label. -/
def primeSeed373Weights : List ℕ :=
  [60, 60, 59, 59, 59, 59, 59, 59, 58, 58, 58, 58, 57, 57] ++ primeSeed281Weights

/-- The distinct labels carry the positive weights in the table order. -/
theorem primeSeed373_labels :
    primeSeed373Primes.Nodup ∧
      primeSeed373Primes.map primeSeed373Weight = primeSeed373Weights ∧
      ∀ p ∈ primeSeed373Primes, 0 < primeSeed373Weight p := by
  decide +kernel

/-- Every listed label is prime and at most 373. -/
theorem primeSeed373_prime_supply : ∀ p ∈ primeSeed373Primes, p.Prime ∧ p ≤ 373 := by decide +kernel

/-- Certified scaled weights bound the logarithms of the listed primes. -/
theorem primeSeed373_weight_bounds :
    ∀ p ∈ primeSeed373Primes, Real.log p ≤ (primeSeed373Weight p : ℝ) / 10 := by
  have h293 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 293 9 16 5 (57 / 10) = true from by
          decide +kernel)).2
  have h317 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 317 9 16 5 (58 / 10) = true from by
          decide +kernel)).2
  have h359 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 359 9 16 5 (59 / 10) = true from by
          decide +kernel)).2
  have h373 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 373 9 16 5 (60 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h293 h317 h359 h373
  intro p hp
  have hprime : p.Prime ∧ p ≤ 373 := by
    exact (show ∀ p ∈ primeSeed373Primes, p.Prime ∧ p ≤ 373 from by decide +kernel) p hp
  simp only [primeSeed373Primes, List.mem_append] at hp
  rcases hp with hnew | hold
  · by_cases h1 : p ≤ 281
    · have hn :
        ∀ p ∈ ([373, 367, 359, 353, 349, 347, 337, 331, 317, 313, 311, 307, 293, 283] : List ℕ),
          281 < p := by
        decide +kernel
      exact False.elim ((Nat.not_lt_of_ge h1) (hn p hnew))
    · by_cases h2 : p ≤ 293
      · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h2)
        simp only [primeSeed373Weight, ite_eq_right h1, ite_eq_left h2, Nat.cast_ofNat]
        norm_num only [Nat.cast_ofNat] at hl
        linarith only [hl, h293]
      · by_cases h3 : p ≤ 317
        · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h3)
          simp only [primeSeed373Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3,
            Nat.cast_ofNat]
          norm_num only [Nat.cast_ofNat] at hl
          linarith only [hl, h317]
        · by_cases h4 : p ≤ 359
          · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h4)
            simp only [primeSeed373Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
              ite_eq_left h4, Nat.cast_ofNat]
            norm_num only [Nat.cast_ofNat] at hl
            linarith only [hl, h359]
          · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr hprime.2)
            simp only [primeSeed373Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
              ite_eq_right h4, Nat.cast_ofNat]
            norm_num only [Nat.cast_ofNat] at hl
            linarith only [hl, h373]
  · have hp281 := (primeSeed281_prime_supply p hold).2
    simpa only [primeSeed373Weight, ite_eq_left hp281] using primeSeed281_weight_bounds p hold

end PseudoPrime.PrimeTestBounds.MillerRabin
