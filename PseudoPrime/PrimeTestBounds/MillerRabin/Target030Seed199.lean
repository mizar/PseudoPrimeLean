/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed113Table

/-! # Weighted prime supply through 199 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The supply through 199 extends the earlier distinct prime labels. -/
def target030Seed199Primes : List ℕ :=
  [199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127] ++
    target030Seed113Primes

/-- Scaled logarithmic weights extend the supply through 113. -/
def target030Seed199Weight (p : ℕ) : ℕ :=
  if p ≤ 113 then target030Seed113Weight p
  else
    if p ≤ 131 then 49
    else if p ≤ 139 then 50 else if p ≤ 163 then 51 else if p ≤ 181 then 52 else 53

/-- Ordered scaled weights retain each prime label. -/
def target030Seed199Weights : List ℕ :=
  [53, 53, 53, 53, 52, 52, 52, 52, 51, 51, 51, 51, 50, 50, 49, 49] ++ target030Seed113Weights

/-- The distinct labels carry the positive weights in the table order. -/
theorem target030Seed199_labels :
    target030Seed199Primes.Nodup ∧
      target030Seed199Primes.map target030Seed199Weight = target030Seed199Weights ∧
      ∀ p ∈ target030Seed199Primes, 0 < target030Seed199Weight p := by
  decide +kernel

/-- Every listed label is prime and at most 199. -/
theorem target030Seed199_prime_supply : ∀ p ∈ target030Seed199Primes, p.Prime ∧ p ≤ 199 := by
  decide +kernel

/-- Certified scaled weights bound the logarithms of the listed primes. -/
theorem target030Seed199_weight_bounds :
    ∀ p ∈ target030Seed199Primes, Real.log p ≤ (target030Seed199Weight p : ℝ) / 10 := by
  have h131 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 131 8 16 4 (49 / 10) = true from by
          decide +kernel)).2
  have h139 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 139 8 16 4 (50 / 10) = true from by
          decide +kernel)).2
  have h163 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 163 8 16 5 (51 / 10) = true from by
          decide +kernel)).2
  have h181 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 181 8 16 5 (52 / 10) = true from by
          decide +kernel)).2
  have h199 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 199 8 16 5 (53 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h131 h139 h163 h181 h199
  intro p hp
  have hprime : p.Prime ∧ p ≤ 199 := by
    exact (show ∀ p ∈ target030Seed199Primes, p.Prime ∧ p ≤ 199 from by decide +kernel) p hp
  simp only [target030Seed199Primes, List.mem_append] at hp
  rcases hp with hnew | hold
  · by_cases h1 : p ≤ 113
    · have hn :
        ∀
          p ∈
            ([199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127] :
              List ℕ),
          113 < p := by
        decide +kernel
      exact False.elim ((Nat.not_lt_of_ge h1) (hn p hnew))
    · by_cases h2 : p ≤ 131
      · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h2)
        simp only [target030Seed199Weight, ite_eq_right h1, ite_eq_left h2, Nat.cast_ofNat]
        norm_num only [Nat.cast_ofNat] at hl
        linarith only [hl, h131]
      · by_cases h3 : p ≤ 139
        · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h3)
          simp only [target030Seed199Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3,
            Nat.cast_ofNat]
          norm_num only [Nat.cast_ofNat] at hl
          linarith only [hl, h139]
        · by_cases h4 : p ≤ 163
          · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h4)
            simp only [target030Seed199Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
              ite_eq_left h4, Nat.cast_ofNat]
            norm_num only [Nat.cast_ofNat] at hl
            linarith only [hl, h163]
          · by_cases h5 : p ≤ 181
            · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h5)
              simp only [target030Seed199Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
                ite_eq_right h4, ite_eq_left h5, Nat.cast_ofNat]
              norm_num only [Nat.cast_ofNat] at hl
              linarith only [hl, h181]
            · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr hprime.2)
              simp only [target030Seed199Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
                ite_eq_right h4, ite_eq_right h5, Nat.cast_ofNat]
              norm_num only [Nat.cast_ofNat] at hl
              linarith only [hl, h199]
  · have hp113 := (target030Seed113_prime_supply p hold).2
    simpa only [target030Seed199Weight, ite_eq_left hp113] using
      target030Seed113_weight_bounds p hold

end PseudoPrime.PrimeTestBounds.MillerRabin
