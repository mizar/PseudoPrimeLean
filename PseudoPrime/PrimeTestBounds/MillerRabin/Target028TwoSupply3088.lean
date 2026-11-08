/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Two1093

/-! # Two-group prime supply and semiprime witness -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- The finite filtered prime lists require deeper reduction.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
-- The two label lists are checked against the existing certified prime block.
/-- At cutoff 3088, the low and high groups contain 109 and 258 labels,
respectively; the ordered weights match and are positive. -/
theorem target028_two_labels_3088 :
    target028TwoLow1093.length = 109 ∧
      (target028TwoHigh1093 3088).length = 258 ∧
      (target028TwoPrimes1093 3088).Nodup ∧
      (target028TwoPrimes1093 3088).map (target028TwoWeight1093 81) =
        target028TwoWeights1093 3088 81 ∧
      ∀ p ∈ target028TwoPrimes1093 3088, 0 < target028TwoWeight1093 81 p := by
  decide +kernel

-- The replicated weight lists require deeper reduction.
set_option maxRecDepth 65536 in
/-- A certified two-group count yields a semiprime witness at cutoff 3088
when its logarithmic count and local envelope fit the requested bound. -/
theorem exists_prime_reject_semiprime_two3088 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (H C : ℕ)
    (hcount :
      C ≤
        weightedPrimeCount id
          (List.replicate 258 81 ++ (List.replicate 109 70 ++ target030Seed373Weights)) H)
    {D X : ℝ} (hD : D ≤ Real.log (C : ℝ)) (hB : (3088 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((H : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3088 12 32 0 (81 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hlog' : Real.log (3088 : ℝ) ≤ (81 : ℝ) / 10 := by
    norm_num only
    exact hlog
  have hcount' : C ≤ weightedPrimeCount id (target028TwoWeights1093 3088 81) H := by
    simpa only [target028TwoWeights1093, target028_two_labels_3088.1, target028_two_labels_3088.2.1,
      List.append_assoc] using hcount
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH
      (target028TwoPrimes1093 3088) (target028TwoWeights1093 3088 81) 3088 H
      (target028TwoWeight1093 81) 10 (by norm_num only) target028_two_labels_3088.2.2.1
      (fun r hr ↦ (target028_two_prime_supply1093 3088 (by decide) r hr).1)
      (fun r hr ↦ (target028_two_prime_supply1093 3088 (by decide) r hr).2)
      target028_two_labels_3088.2.2.2.2 (target028_two_weight_bounds1093 3088 81 (by decide) hlog')
      target028_two_labels_3088.2.2.2.1 C hcount' hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
