/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Count

/-! # Prime labels through 863 for semiprime intervals -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Selected prime labels through 863 used in the weighted count. -/
def semiSeed863 : List ℕ :=
  primeSeed1849Extra.drop 133 ++ primeSeed373Primes

/-- Logarithmic weights for the selected prime labels. -/
def semiWeight863 (p : ℕ) : ℕ :=
  if p ≤ 373 then primeSeed373Weight p else 68

/-- The ordered weights of the selected prime labels. -/
def semiWeights863 : List ℕ :=
  List.replicate 76 68 ++ primeSeed373Weights

/-- The selected labels are distinct and have the stated positive weights. -/
theorem semiSeed863_labels :
    semiSeed863.Nodup ∧
      semiSeed863.map semiWeight863 = semiWeights863 ∧ ∀ p ∈ semiSeed863, 0 < semiWeight863 p := by
  have hsub : semiSeed863.Sublist primeSeed1849Primes :=
    (List.drop_sublist 133 primeSeed1849Extra).append (List.Sublist.refl _)
  refine ⟨hsub.nodup primeSeed1849_labels.1, ?_, ?_⟩
  · decide +kernel
  · intro p hp
    have hp0 := primeSeed1849_labels.2.2 p (hsub.subset hp)
    by_cases h : p ≤ 373
    · simpa only [semiWeight863, primeSeed1849Weight, ite_eq_left h] using hp0
    · simp only [semiWeight863, ite_eq_right h]
      norm_num only

/-- Every selected label is prime and at most 863. -/
theorem semiSeed863_primes : ∀ p ∈ semiSeed863, p.Prime ∧ p ≤ 863 := by
  intro p hp
  have hsub : semiSeed863.Sublist primeSeed1849Primes :=
    (List.drop_sublist 133 primeSeed1849Extra).append (List.Sublist.refl _)
  have hp' := primeSeed1849_prime_supply p (hsub.subset hp)
  refine ⟨hp'.1, ?_⟩
  have hdrop : ∀ p ∈ primeSeed1849Extra.drop 133, p ≤ 863 := by decide +kernel
  rcases List.mem_append.mp hp with he | he
  · exact hdrop p he
  · exact ((primeSeed373_prime_supply p he).2).trans (by decide)

/-- Each selected label has logarithm at most its weight divided by ten. -/
theorem semiSeed863_weights : ∀ p ∈ semiSeed863, Real.log p ≤ (semiWeight863 p : ℝ) / 10 := by
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 863 10 32 0 (34 / 5) = true by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  intro p hp
  by_cases h : p ≤ 373
  · have hsub : semiSeed863.Sublist primeSeed1849Primes :=
      (List.drop_sublist 133 primeSeed1849Extra).append (List.Sublist.refl _)
    have hw := primeSeed1849_weight_bounds p (hsub.subset hp)
    simpa only [semiWeight863, primeSeed1849Weight, ite_eq_left h] using hw
  · have hprime := semiSeed863_primes p hp
    have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr hprime.2)
    norm_num only [Nat.cast_ofNat] at hl
    simp only [semiWeight863, ite_eq_right h, Nat.cast_ofNat]
    linarith only [hl, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
