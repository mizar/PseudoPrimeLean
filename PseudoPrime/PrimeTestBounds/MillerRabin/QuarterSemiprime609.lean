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
import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeSeed863

/-! # Semiprime witnesses on logarithmic scales 60 to 60.9 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A radius-30 local anchor gives a rejecting prime at most 900 when the larger
factor has logarithm at most 35.1. The proper local Fermat kernel transfers the anchor. -/
private theorem semiprime_local_anchor900 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hqlog : Real.log q ≤ (351 / 10 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ 900 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
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
      (show localCorrectionCheck (30) (511 / 100) 5 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (51 / 10 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (30) := by
    linarith only [hc]
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hproper hpass hGRH (b := 30) (d := 51 / 10)
      (by norm_num only) hd hqlog
  have hmax : max (30 : ℝ) (351 / 10 - 51 / 10) ≤ 30 := by apply max_le <;> norm_num only
  have hr900 : (r : ℝ) ≤ 900 := by
    nlinarith only [hb, hmax, le_max_left (30 : ℝ) (351 / 10 - 51 / 10)]
  exact ⟨r, hr, hr900, hf⟩

/-- The weighted prime family has at least 87590594861 products at budget 344. -/
private theorem card863_344 :
    87590594861 ≤ (weightedPrimeFamily semiSeed863.toFinset semiWeight863 344).card := by
  have hb := primeSeed373_count_lower 276 (by decide)
  rw [show primeSeed373Row14.getD 276 0 = 1137540193 by decide +kernel] at hb
  have hg := weightedPrimeCount_group_lower 68 276 76 1 primeSeed373Weights (by decide)
  have hc : 87590594861 ≤ weightedPrimeCount id semiWeights863 344 := by
    have hm := (Nat.mul_le_mul_left (Nat.choose (76 + 1) 1) hb).trans hg
    norm_num only [Nat.choose_one_right] at hm
    exact hm
  exact
    hc.trans_eq
      (weightedPrimeCount_weights_eq_card semiWeight863 344 semiSeed863 semiWeights863
        semiSeed863_labels.1 semiSeed863_labels.2.2 semiSeed863_labels.2.1)

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 60 and 60.9 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and the radius-30 local anchor cover both cases. -/
theorem quarter_semiprime_600_609 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (60 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 609 / 10) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := semiSeed863.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦ (semiSeed863_primes r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 900 := fun r hr ↦
    ((semiSeed863_primes r (List.mem_toFinset.mp hr)).2).trans (by decide)
  have hw : ∀ r ∈ S, Real.log r ≤ (semiWeight863 r : ℝ) / 10 := fun r hr ↦
    semiSeed863_weights r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ semiWeight863 r := fun r hr ↦
    semiSeed863_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 175181189722 38 32 (647 / 25) 27 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (647 / 25 : ℝ) ≤ Real.log ((2 * (weightedPrimeFamily S semiWeight863 344).card : ℕ) : ℝ) := by
    change
      (647 / 25 : ℝ) ≤
        Real.log ((2 * (weightedPrimeFamily semiSeed863.toFinset semiWeight863 344).card : ℕ) : ℝ)
    have hcount :
      (175181189722 : ℝ) ≤
        ((2 * (weightedPrimeFamily semiSeed863.toFinset semiWeight863 344).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 card863_344
    exact hlog.trans (Real.log_le_log (by norm_num only) hcount)
  have hA : Real.log 2 + (344 : ℝ) / 10 ≤ 351 / 10 := by linarith only [Real.log_two_lt_d9]
  have hB : (900 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S semiWeight863 344 900 10
      (by norm_num only) hwpos hprime hbound hw hA hD (by linarith only [hB])
  intro hqsmall
  have hmax : max (351 / 10 : ℝ) (Real.log n - 647 / 25) ≤ 351 / 10 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor900 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, hrB.trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
