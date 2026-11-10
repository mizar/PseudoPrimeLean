/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Count

/-! # Prime labels through 991 for semiprime intervals -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Selected prime labels through 991 used in the weighted count. -/
def semiSeed991 : List ℕ :=
  primeSeed1849Extra.drop 116 ++ primeSeed373Primes

/-- Logarithmic weights for the selected prime labels. -/
def semiWeight991 (p : ℕ) : ℕ :=
  if p ≤ 373 then primeSeed373Weight p else 70

/-- The ordered weights of the selected prime labels. -/
def semiWeights991 : List ℕ :=
  List.replicate 93 70 ++ primeSeed373Weights

/-- The selected labels are distinct and have the stated positive weights. -/
theorem semiSeed991_labels :
    semiSeed991.Nodup ∧
      semiSeed991.map semiWeight991 = semiWeights991 ∧ ∀ p ∈ semiSeed991, 0 < semiWeight991 p := by
  have hsub : semiSeed991.Sublist primeSeed1849Primes :=
    (List.drop_sublist 116 primeSeed1849Extra).append (List.Sublist.refl _)
  refine ⟨hsub.nodup primeSeed1849_labels.1, ?_, ?_⟩
  · decide +kernel
  · intro p hp
    have hp0 := primeSeed1849_labels.2.2 p (hsub.subset hp)
    by_cases h : p ≤ 373
    · simpa only [semiWeight991, primeSeed1849Weight, ite_eq_left h] using hp0
    · simp only [semiWeight991, ite_eq_right h]
      norm_num only

/-- Every selected label is prime and at most 991. -/
theorem semiSeed991_primes : ∀ p ∈ semiSeed991, p.Prime ∧ p ≤ 991 := by
  intro p hp
  have hsub : semiSeed991.Sublist primeSeed1849Primes :=
    (List.drop_sublist 116 primeSeed1849Extra).append (List.Sublist.refl _)
  have hp' := primeSeed1849_prime_supply p (hsub.subset hp)
  refine ⟨hp'.1, ?_⟩
  have hdrop : ∀ p ∈ primeSeed1849Extra.drop 116, p ≤ 991 := by decide +kernel
  rcases List.mem_append.mp hp with he | he
  · exact hdrop p he
  · exact ((primeSeed373_prime_supply p he).2).trans (by decide)

/-- Each selected label has logarithm at most its weight divided by ten. -/
theorem semiSeed991_weights : ∀ p ∈ semiSeed991, Real.log p ≤ (semiWeight991 p : ℝ) / 10 := by
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 991 10 32 0 7 = true by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  intro p hp
  by_cases h : p ≤ 373
  · have hsub : semiSeed991.Sublist primeSeed1849Primes :=
      (List.drop_sublist 116 primeSeed1849Extra).append (List.Sublist.refl _)
    have hw := primeSeed1849_weight_bounds p (hsub.subset hp)
    simpa only [semiWeight991, primeSeed1849Weight, ite_eq_left h] using hw
  · have hprime := semiSeed991_primes p hp
    have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr hprime.2)
    norm_num only [Nat.cast_ofNat] at hl
    simp only [semiWeight991, ite_eq_right h, Nat.cast_ofNat]
    linarith only [hl, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
