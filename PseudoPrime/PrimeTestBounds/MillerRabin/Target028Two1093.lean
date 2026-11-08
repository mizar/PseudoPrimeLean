/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GroupGrid
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerPrimeBlocks
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeCount

/-! # Two-weight prime supplies for the remaining semiprime range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The primes above 373 and at most 1093 receive common weight 70. -/
def target028TwoLow1093 : List ℕ :=
  centerPrimeBlock0.filter (fun p ↦ decide (373 < p ∧ p ≤ 1093))

/-- The primes above 1093 and at most `B` form the second group. -/
def target028TwoHigh1093 (B : ℕ) : List ℕ :=
  centerPrimeBlock0.filter (fun p ↦ decide (1093 < p ∧ p ≤ B))

/-- The two groups followed by the established supply through 373. -/
def target028TwoPrimes1093 (B : ℕ) : List ℕ :=
  target028TwoHigh1093 B ++ target028TwoLow1093 ++ target030Seed373Primes

/-- The old weights are retained through 373; the low and high groups use
weights 70 and `w`, respectively. -/
def target028TwoWeight1093 (w p : ℕ) : ℕ :=
  if p ≤ 373 then target030Seed373Weight p else if p ≤ 1093 then 70 else w

/-- Ordered weights for the two groups and the certified base supply. -/
def target028TwoWeights1093 (B w : ℕ) : List ℕ :=
  List.replicate (target028TwoHigh1093 B).length w ++
    List.replicate target028TwoLow1093.length 70 ++
    target030Seed373Weights

/-- Every label in the certified first prime block is prime. -/
theorem target028_center_prime1093 (p : ℕ) (hp : p ∈ centerPrimeBlock0) : p.Prime := by
  rw [centerPrimeBlock0_eq] at hp
  simp only [List.mem_filter, decide_eq_true_eq] at hp
  exact hp.2

/-- Every selected label is prime and at most `B`, provided the cutoff is
at least 1093. Primality follows from the two previously certified lists. -/
theorem target028_two_prime_supply1093 (B : ℕ) (hB : 1093 ≤ B) :
    ∀ p ∈ target028TwoPrimes1093 B, p.Prime ∧ p ≤ B := by
  intro p hp
  simp only [target028TwoPrimes1093, List.mem_append] at hp
  rcases hp with (hhigh | hlow) | hbase
  · simp only [target028TwoHigh1093, List.mem_filter, decide_eq_true_eq] at hhigh
    exact ⟨target028_center_prime1093 p hhigh.1, hhigh.2.2⟩
  · simp only [target028TwoLow1093, List.mem_filter, decide_eq_true_eq] at hlow
    exact ⟨target028_center_prime1093 p hlow.1, hlow.2.2.trans hB⟩
  · have h := target030Seed373_prime_supply p hbase
    exact ⟨h.1, h.2.trans (le_trans (by decide) hB)⟩

/-- If `w/10` bounds `log B`, both new groups and the original labels have
valid scaled logarithmic weights. The low-group bound is checked at 1093. -/
theorem target028_two_weight_bounds1093 (B w : ℕ) (hB : 1093 ≤ B)
    (hlog : Real.log B ≤ (w : ℝ) / 10) :
    ∀ p ∈ target028TwoPrimes1093 B, Real.log p ≤ (target028TwoWeight1093 w p : ℝ) / 10 := by
  have hlowlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1093 11 32 0 7 = true from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat] at hlowlog
  intro p hp
  simp only [target028TwoPrimes1093, List.mem_append] at hp
  rcases hp with (hhigh | hlow) | hbase
  · have hsup :=
      target028_two_prime_supply1093 B hB p
        (by
          simp only [target028TwoPrimes1093, List.mem_append]
          exact Or.inl (Or.inl hhigh))
    have hbound : ∀ p ∈ target028TwoHigh1093 B, 1093 < p := by
      intro p hp
      simp only [target028TwoHigh1093, List.mem_filter, decide_eq_true_eq] at hp
      exact hp.2.1
    have hp1093 : ¬p ≤ 1093 := Nat.not_le_of_gt (hbound p hhigh)
    have hp373 : ¬p ≤ 373 := Nat.not_le_of_gt (lt_trans (by decide) (hbound p hhigh))
    have hl := Real.log_le_log (Nat.cast_pos.mpr hsup.1.pos) (Nat.cast_le.mpr hsup.2)
    simpa only [target028TwoWeight1093, ite_eq_right hp373, ite_eq_right hp1093] using hl.trans hlog
  · simp only [target028TwoLow1093, List.mem_filter, decide_eq_true_eq] at hlow
    have hp373 : ¬p ≤ 373 := Nat.not_le_of_gt hlow.2.1
    have hp1093 : p ≤ 1093 := hlow.2.2
    have hl :=
      Real.log_le_log (Nat.cast_pos.mpr (target028_center_prime1093 p hlow.1).pos)
        (Nat.cast_le.mpr hp1093)
    have hc : Real.log (p : ℝ) ≤ (70 : ℝ) / 10 := by
      norm_num only at ⊢
      exact hl.trans hlowlog
    simpa only [target028TwoWeight1093, ite_eq_right hp373, ite_eq_left hp1093,
      Nat.cast_ofNat] using hc
  · have hp373 := (target030Seed373_prime_supply p hbase).2
    simpa only [target028TwoWeight1093, ite_eq_left hp373] using
      target030Seed373_weight_bounds p hbase

end PseudoPrime.PrimeTestBounds.MillerRabin
