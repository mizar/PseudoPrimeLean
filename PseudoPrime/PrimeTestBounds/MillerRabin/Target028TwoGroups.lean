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

/-- The primes above 373 and at most 1009 receive common weight 70. -/
def target028TwoLow : List ℕ :=
  centerPrimeBlock0.filter (fun p ↦ decide (373 < p ∧ p ≤ 1009))

/-- The primes above 1009 and at most `B` form the second group. -/
def target028TwoHigh (B : ℕ) : List ℕ :=
  centerPrimeBlock0.filter (fun p ↦ decide (1009 < p ∧ p ≤ B))

/-- The two groups followed by the established supply through 373. -/
def target028TwoPrimes (B : ℕ) : List ℕ :=
  target028TwoHigh B ++ target028TwoLow ++ target030Seed373Primes

/-- The old weights are retained through 373; the low and high groups use
weights 70 and `w`, respectively. -/
def target028TwoWeight (w p : ℕ) : ℕ :=
  if p ≤ 373 then target030Seed373Weight p else if p ≤ 1009 then 70 else w

/-- Ordered weights for the two groups and the certified base supply. -/
def target028TwoWeights (B w : ℕ) : List ℕ :=
  List.replicate (target028TwoHigh B).length w ++ List.replicate target028TwoLow.length 70 ++
    target030Seed373Weights

/-- Every label in the certified first prime block is prime. -/
theorem target028_center_prime (p : ℕ) (hp : p ∈ centerPrimeBlock0) : p.Prime := by
  rw [centerPrimeBlock0_eq] at hp
  simp only [List.mem_filter, decide_eq_true_eq] at hp
  exact hp.2

/-- Every selected label is prime and at most `B`, provided the cutoff is
at least 1009. Primality follows from the two previously certified lists. -/
theorem target028_two_prime_supply (B : ℕ) (hB : 1009 ≤ B) :
    ∀ p ∈ target028TwoPrimes B, p.Prime ∧ p ≤ B := by
  intro p hp
  simp only [target028TwoPrimes, List.mem_append] at hp
  rcases hp with (hhigh | hlow) | hbase
  · simp only [target028TwoHigh, List.mem_filter, decide_eq_true_eq] at hhigh
    exact ⟨target028_center_prime p hhigh.1, hhigh.2.2⟩
  · simp only [target028TwoLow, List.mem_filter, decide_eq_true_eq] at hlow
    exact ⟨target028_center_prime p hlow.1, hlow.2.2.trans hB⟩
  · have h := target030Seed373_prime_supply p hbase
    exact ⟨h.1, h.2.trans (le_trans (by decide) hB)⟩

/-- If `w/10` bounds `log B`, both new groups and the original labels have
valid scaled logarithmic weights. The low-group bound is checked at 1009. -/
theorem target028_two_weight_bounds (B w : ℕ) (hB : 1009 ≤ B) (hlog : Real.log B ≤ (w : ℝ) / 10) :
    ∀ p ∈ target028TwoPrimes B, Real.log p ≤ (target028TwoWeight w p : ℝ) / 10 := by
  have hlowlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1009 10 32 0 7 = true from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat] at hlowlog
  intro p hp
  simp only [target028TwoPrimes, List.mem_append] at hp
  rcases hp with (hhigh | hlow) | hbase
  · have hsup :=
      target028_two_prime_supply B hB p
        (by
          simp only [target028TwoPrimes, List.mem_append]
          exact Or.inl (Or.inl hhigh))
    have hbound : ∀ p ∈ target028TwoHigh B, 1009 < p := by
      intro p hp
      simp only [target028TwoHigh, List.mem_filter, decide_eq_true_eq] at hp
      exact hp.2.1
    have hp1009 : ¬p ≤ 1009 := Nat.not_le_of_gt (hbound p hhigh)
    have hp373 : ¬p ≤ 373 := Nat.not_le_of_gt (lt_trans (by decide) (hbound p hhigh))
    have hl := Real.log_le_log (Nat.cast_pos.mpr hsup.1.pos) (Nat.cast_le.mpr hsup.2)
    simpa only [target028TwoWeight, ite_eq_right hp373, ite_eq_right hp1009] using hl.trans hlog
  · simp only [target028TwoLow, List.mem_filter, decide_eq_true_eq] at hlow
    have hp373 : ¬p ≤ 373 := Nat.not_le_of_gt hlow.2.1
    have hp1009 : p ≤ 1009 := hlow.2.2
    have hl :=
      Real.log_le_log (Nat.cast_pos.mpr (target028_center_prime p hlow.1).pos)
        (Nat.cast_le.mpr hp1009)
    have hc : Real.log (p : ℝ) ≤ (70 : ℝ) / 10 := by
      norm_num only at ⊢
      exact hl.trans hlowlog
    simpa only [target028TwoWeight, ite_eq_right hp373, ite_eq_left hp1009, Nat.cast_ofNat] using hc
  · have hp373 := (target030Seed373_prime_supply p hbase).2
    simpa only [target028TwoWeight, ite_eq_left hp373] using target030Seed373_weight_bounds p hbase

-- The finite label check traverses the certified prime block through 5000.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
-- Duplicate-freeness and mapped weights are checked over the two filtered lists.
/-- At cutoff 2618 the two groups contain 95 and 211 labels and match the
positive weights required by the semiprime witness theorem. -/
theorem target028_two_labels_2618 :
    target028TwoLow.length = 95 ∧
      (target028TwoHigh 2618).length = 211 ∧
      (target028TwoPrimes 2618).Nodup ∧
      (target028TwoPrimes 2618).map (target028TwoWeight 79) = target028TwoWeights 2618 79 ∧
      ∀ p ∈ target028TwoPrimes 2618, 0 < target028TwoWeight 79 p := by
  decide +kernel

-- Simplifying the two replicated weight lists requires deeper recursion.
set_option maxRecDepth 65536 in
/-- A numerical lower bound for the two-group weighted count supplies a
semiprime witness when the cutoff and local envelope fit. -/
theorem exists_prime_reject_semiprime_two2618 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (H C : ℕ)
    (hcount :
      C ≤
        weightedPrimeCount id
          (List.replicate 211 79 ++ (List.replicate 95 70 ++ target030Seed373Weights)) H)
    {D X : ℝ} (hD : D ≤ Real.log (C : ℝ)) (hB : (2618 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((H : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2618 12 32 0 (79 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hcount' : C ≤ weightedPrimeCount id (target028TwoWeights 2618 79) H := by
    simpa only [target028TwoWeights, target028_two_labels_2618.1, target028_two_labels_2618.2.1,
      List.append_assoc] using hcount
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH (target028TwoPrimes 2618)
      (target028TwoWeights 2618 79) 2618 H (target028TwoWeight 79) 10 (by norm_num only)
      target028_two_labels_2618.2.2.1
      (fun r hr ↦ (target028_two_prime_supply 2618 (by decide) r hr).1)
      (fun r hr ↦ (target028_two_prime_supply 2618 (by decide) r hr).2)
      target028_two_labels_2618.2.2.2.2 (target028_two_weight_bounds 2618 79 (by decide) hlog)
      target028_two_labels_2618.2.2.2.1 C hcount' hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
