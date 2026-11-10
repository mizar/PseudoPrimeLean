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

/-! # Semiprime witnesses on logarithmic scales 52.1 to 53.9 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A radius-26.05 local anchor gives a rejecting prime at most 678.6025 when the larger
factor has logarithm at most 30.95. The proper local Fermat kernel transfers the anchor. -/
private theorem semiprime_local_anchor678 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hqlog : Real.log q ≤ (619 / 20 : ℝ)) :
    ∃ r : ℕ,
      r.Prime ∧ (r : ℝ) ≤ 271441 / 400 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
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
      (show localCorrectionCheck (521 / 20) (491 / 100) 5 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (49 / 10 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (521 / 20) := by
    linarith only [hc]
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hproper hpass hGRH (b := 521 / 20) (d := 49 / 10)
      (by norm_num only) hd hqlog
  have hmax : max (521 / 20 : ℝ) (619 / 20 - 49 / 10) ≤ 521 / 20 := by
    apply max_le <;> norm_num only
  have hr678 : (r : ℝ) ≤ 271441 / 400 := by
    nlinarith only [hb, hmax, le_max_left (521 / 20 : ℝ) (619 / 20 - 49 / 10)]
  exact ⟨r, hr, hr678, hf⟩

/-- The weighted prime family has at least 4835997728 products at budget 302. -/
private theorem card373_302 :
    4835997728 ≤ (weightedPrimeFamily primeSeed373Primes.toFinset primeSeed373Weight 302).card := by
  have h := primeSeed373_count_lower 302 (by decide)
  rw [show primeSeed373Row14.getD 302 0 = 4835997728 by decide +kernel] at h
  exact
    h.trans_eq
      (weightedPrimeCount_weights_eq_card primeSeed373Weight 302 primeSeed373Primes
        primeSeed373Weights primeSeed373_labels.1 primeSeed373_labels.2.2 primeSeed373_labels.2.1)

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 52.1 and 53.9 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and the radius-26.05 local anchor cover both cases. -/
theorem quarter_semiprime_521_539 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (521 / 10 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 539 / 10) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := primeSeed373Primes.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (primeSeed373_prime_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 678 := fun r hr ↦
    ((primeSeed373_prime_supply r (List.mem_toFinset.mp hr)).2).trans (by decide)
  have hw : ∀ r ∈ S, Real.log r ≤ (primeSeed373Weight r : ℝ) / 10 := fun r hr ↦
    primeSeed373_weight_bounds r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ primeSeed373Weight r := fun r hr ↦
    primeSeed373_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 9671995456 34 32 (2299 / 100) 24 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (2299 / 100 : ℝ) ≤
      Real.log ((2 * (weightedPrimeFamily S primeSeed373Weight 302).card : ℕ) : ℝ) := by
    change
      (2299 / 100 : ℝ) ≤
        Real.log
          ((2 * (weightedPrimeFamily primeSeed373Primes.toFinset primeSeed373Weight 302).card : ℕ) :
            ℝ)
    have hcount :
      (9671995456 : ℝ) ≤
        ((2 * (weightedPrimeFamily primeSeed373Primes.toFinset primeSeed373Weight 302).card : ℕ) :
          ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 card373_302
    exact hlog.trans (Real.log_le_log (by norm_num only) hcount)
  have hA : Real.log 2 + (302 : ℝ) / 10 ≤ 619 / 20 := by linarith only [Real.log_two_lt_d9]
  have hB : (271441 / 400 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S primeSeed373Weight 302 678 10
      (by norm_num only) hwpos hprime hbound hw hA hD (by linarith only [hB])
  intro hqsmall
  have hmax : max (619 / 20 : ℝ) (Real.log n - 2299 / 100) ≤ 619 / 20 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor678 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, hrB.trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
