/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors

/-! # First low-scale weighted prime supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first explicit supply consists of primes at most 19. The finite
primality and cutoff checks use kernel reduction and feed the weighted
semiprime candidate. -/
theorem prime_seed19_prime_supply : ∀ p ∈ primeSeed19Primes, p.Prime ∧ p ≤ 19 := by decide +kernel

/-- The integer weights of the first supply dominate ten times each prime's
logarithm. Rational logarithm enclosures certify the seven cutoff values; the
weight shared by 17 and 19 uses logarithmic monotonicity. -/
theorem prime_seed19_weight_bounds :
    ∀ p ∈ primeSeed19Primes, Real.log p ≤ (primeSeed19Weight p : ℝ) / 10 := by
  have h2 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2 1 16 (6 / 10) (7 / 10) = true from by
          decide +kernel)).2
  have h3 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3 2 16 (10 / 10) (11 / 10) = true from by
          decide +kernel)).2
  have h5 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 5 3 16 (16 / 10) (17 / 10) = true from by
          decide +kernel)).2
  have h7 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 7 3 16 (19 / 10) (20 / 10) = true from by
          decide +kernel)).2
  have h11 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 11 4 16 (23 / 10) (24 / 10) = true from by
          decide +kernel)).2
  have h13 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 13 4 16 (25 / 10) (26 / 10) = true from by
          decide +kernel)).2
  have h19 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 19 5 16 (29 / 10) (30 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h2 h3 h5 h7 h11 h13 h19
  have h17 : Real.log (17 : ℝ) ≤ 3 :=
    (Real.log_le_log (by norm_num only) (by norm_num only : (17 : ℝ) ≤ 19)).trans h19
  intro p hp
  simp only [primeSeed19Primes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num only [primeSeed19Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false]
  · exact h2
  · exact h3
  · exact h5
  · exact h7
  · exact h11
  · exact h13
  · exact h17
  · exact h19

end PseudoPrime.PrimeTestBounds.MillerRabin
