/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed199

/-! # Weighted prime supply through 281 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The supply through 281 extends the earlier distinct prime labels. -/
def target030Seed281Primes : List ℕ :=
  [281, 277, 271, 269, 263, 257, 251, 241, 239, 233, 229, 227, 223, 211] ++ target030Seed199Primes

/-- Scaled logarithmic weights extend the supply through 199. -/
def target030Seed281Weight (p : ℕ) : ℕ :=
  if p ≤ 199 then target030Seed199Weight p
  else if p ≤ 211 then 54 else if p ≤ 241 then 55 else if p ≤ 269 then 56 else 57

/-- Ordered scaled weights retain each prime label. -/
def target030Seed281Weights : List ℕ :=
  [57, 57, 57, 56, 56, 56, 56, 55, 55, 55, 55, 55, 55, 54] ++ target030Seed199Weights

/-- The distinct labels carry the positive weights in the table order. -/
theorem target030Seed281_labels :
    target030Seed281Primes.Nodup ∧
      target030Seed281Primes.map target030Seed281Weight = target030Seed281Weights ∧
      ∀ p ∈ target030Seed281Primes, 0 < target030Seed281Weight p := by
  decide +kernel

/-- Every listed label is prime and at most 281. -/
theorem target030Seed281_prime_supply : ∀ p ∈ target030Seed281Primes, p.Prime ∧ p ≤ 281 := by
  decide +kernel

/-- Certified scaled weights bound the logarithms of the listed primes. -/
theorem target030Seed281_weight_bounds :
    ∀ p ∈ target030Seed281Primes, Real.log p ≤ (target030Seed281Weight p : ℝ) / 10 := by
  have h211 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 211 8 16 5 (54 / 10) = true from by
          decide +kernel)).2
  have h241 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 241 8 16 5 (55 / 10) = true from by
          decide +kernel)).2
  have h269 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 269 9 16 5 (56 / 10) = true from by
          decide +kernel)).2
  have h281 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 281 9 16 5 (57 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h211 h241 h269 h281
  intro p hp
  have hprime : p.Prime ∧ p ≤ 281 := by
    exact (show ∀ p ∈ target030Seed281Primes, p.Prime ∧ p ≤ 281 from by decide +kernel) p hp
  simp only [target030Seed281Primes, List.mem_append] at hp
  rcases hp with hnew | hold
  · by_cases h1 : p ≤ 199
    · have hn :
        ∀ p ∈ ([281, 277, 271, 269, 263, 257, 251, 241, 239, 233, 229, 227, 223, 211] : List ℕ),
          199 < p := by
        decide +kernel
      exact False.elim ((Nat.not_lt_of_ge h1) (hn p hnew))
    · by_cases h2 : p ≤ 211
      · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h2)
        simp only [target030Seed281Weight, ite_eq_right h1, ite_eq_left h2, Nat.cast_ofNat]
        norm_num only [Nat.cast_ofNat] at hl
        linarith only [hl, h211]
      · by_cases h3 : p ≤ 241
        · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h3)
          simp only [target030Seed281Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3,
            Nat.cast_ofNat]
          norm_num only [Nat.cast_ofNat] at hl
          linarith only [hl, h241]
        · by_cases h4 : p ≤ 269
          · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h4)
            simp only [target030Seed281Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
              ite_eq_left h4, Nat.cast_ofNat]
            norm_num only [Nat.cast_ofNat] at hl
            linarith only [hl, h269]
          · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr hprime.2)
            simp only [target030Seed281Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
              ite_eq_right h4, Nat.cast_ofNat]
            norm_num only [Nat.cast_ofNat] at hl
            linarith only [hl, h281]
  · have hp199 := (target030Seed199_prime_supply p hold).2
    simpa only [target030Seed281Weight, ite_eq_left hp199] using
      target030Seed199_weight_bounds p hold

end PseudoPrime.PrimeTestBounds.MillerRabin
