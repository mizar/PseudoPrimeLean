/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Count
import PseudoPrime.PrimeTestBounds.MillerRabin.SignedWeightedCell
import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors
import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeSmallFactor
import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeSeed991
import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeGrid383

/-! # Semiprime witnesses on logarithmic scales 67.6 to 68 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A radius-33.8 local anchor gives a rejecting prime at most 1142.44 when the larger
factor has logarithm at most 39. The proper local Fermat kernel transfers the anchor. -/
private theorem semiprime_local_anchor1142 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hqlog : Real.log q ≤ (39 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ 28561 / 25 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero q := ⟨Nat.ne_zero_of_lt hq.pos⟩
  let : Fact q.Prime := ⟨hq⟩
  have hqn : q ∣ n := hprod ▸ dvd_mul_left q p
  have hbad : ¬q - 1 ∣ n - 1 := by
    rw [hprod]
    exact NumberTheory.not_sub_one_dvd_prime_mul_sub_one_of_lt hp hq hpq
  let H := (powMonoidHom (n - 1) : (ZMod q)ˣ →* (ZMod q)ˣ).ker
  have hproper : H ≠ ⊤ := NumberTheory.local_prime_powerKernel_ne_top_of_not_dvd hbad
  have hpass :
    ∀ a : ℕ,
      PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
        ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q) := by
    intro a ha
    exact PrimeTest.strongMR_local_divisorKernel hn ho hqn ha
  have hc :=
    localCorrectionCheck_sound
      (show localCorrectionCheck (169 / 5) (521 / 100) 6 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (26 / 5 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (169 / 5) := by
    linarith only [hc]
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hproper hpass hGRH (b := 169 / 5) (d := 26 / 5)
      (by norm_num only) hd hqlog
  have hmax : max (169 / 5 : ℝ) (39 - 26 / 5) ≤ 169 / 5 := by apply max_le <;> norm_num only
  have hr1142 : (r : ℝ) ≤ 28561 / 25 := by
    nlinarith only [hb, hmax, le_max_left (169 / 5 : ℝ) (39 - 26 / 5)]
  exact ⟨r, hr, hr1142, hf⟩

/-- The weighted prime family has at least 2214293690627 products at budget 383. -/
private theorem card991_383 :
    2214293690627 ≤ (weightedPrimeFamily semiSeed991.toFinset semiWeight991 383).card := by
  have hc : 2214293690627 ≤ weightedPrimeCount id semiWeights991 383 := semiGrid383_count
  exact
    hc.trans_eq
      (weightedPrimeCount_weights_eq_card semiWeight991 383 semiSeed991 semiWeights991
        semiSeed991_labels.1 semiSeed991_labels.2.2 semiSeed991_labels.2.1)

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 67.6 and 68 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and the radius-33.8 local anchor cover both cases. -/
theorem quarter_semiprime_676_680 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (338 / 5 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 68) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := semiSeed991.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦ (semiSeed991_primes r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 1142 := fun r hr ↦
    ((semiSeed991_primes r (List.mem_toFinset.mp hr)).2).trans (by decide)
  have hw : ∀ r ∈ S, Real.log r ≤ (semiWeight991 r : ℝ) / 10 := fun r hr ↦
    semiSeed991_weights r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ semiWeight991 r := fun r hr ↦
    semiSeed991_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 4428587381254 43 32 (2911 / 100) 31 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (2911 / 100 : ℝ) ≤ Real.log ((2 * (weightedPrimeFamily S semiWeight991 383).card : ℕ) : ℝ) := by
    change
      (2911 / 100 : ℝ) ≤
        Real.log ((2 * (weightedPrimeFamily semiSeed991.toFinset semiWeight991 383).card : ℕ) : ℝ)
    have hcount :
      (4428587381254 : ℝ) ≤
        ((2 * (weightedPrimeFamily semiSeed991.toFinset semiWeight991 383).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 card991_383
    exact hlog.trans (Real.log_le_log (by norm_num only) hcount)
  have hA : Real.log 2 + (383 : ℝ) / 10 ≤ 39 := by linarith only [Real.log_two_lt_d9]
  have hB : (28561 / 25 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S semiWeight991 383 1142 10
      (by norm_num only) hwpos hprime hbound hw hA hD (by linarith only [hB])
  intro hqsmall
  have hmax : max (39 : ℝ) (Real.log n - 2911 / 100) ≤ 39 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor1142 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, hrB.trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
