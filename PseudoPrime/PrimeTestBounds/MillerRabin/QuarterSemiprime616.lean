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

/-! # Semiprime witnesses on logarithmic scales 60.9 to 61.6 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A radius-30.45 local anchor gives a rejecting prime at most 927.2025 when the larger
factor has logarithm at most 35.55. The proper local Fermat kernel transfers the anchor. -/
private theorem semiprime_local_anchor927 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hqlog : Real.log q ≤ (711 / 20 : ℝ)) :
    ∃ r : ℕ,
      r.Prime ∧ (r : ℝ) ≤ 370881 / 400 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
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
      (show localCorrectionCheck (609 / 20) (511 / 100) 5 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (51 / 10 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (609 / 20) := by
    linarith only [hc]
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hproper hpass hGRH (b := 609 / 20) (d := 51 / 10)
      (by norm_num only) hd hqlog
  have hmax : max (609 / 20 : ℝ) (711 / 20 - 51 / 10) ≤ 609 / 20 := by
    apply max_le <;> norm_num only
  have hr927 : (r : ℝ) ≤ 370881 / 400 := by
    nlinarith only [hb, hmax, le_max_left (609 / 20 : ℝ) (711 / 20 - 51 / 10)]
  exact ⟨r, hr, hr927, hf⟩

/-- The weighted prime family has at least 109782442770 products at budget 348. -/
private theorem card863_348 :
    109782442770 ≤ (weightedPrimeFamily semiSeed863.toFinset semiWeight863 348).card := by
  have hb := primeSeed373_count_lower 280 (by decide)
  rw [show primeSeed373Row14.getD 280 0 = 1425746010 by decide +kernel] at hb
  have hg := weightedPrimeCount_group_lower 68 280 76 1 primeSeed373Weights (by decide)
  have hc : 109782442770 ≤ weightedPrimeCount id semiWeights863 348 := by
    have hm := (Nat.mul_le_mul_left (Nat.choose (76 + 1) 1) hb).trans hg
    norm_num only [Nat.choose_one_right] at hm
    exact hm
  exact
    hc.trans_eq
      (weightedPrimeCount_weights_eq_card semiWeight863 348 semiSeed863 semiWeights863
        semiSeed863_labels.1 semiSeed863_labels.2.2 semiSeed863_labels.2.1)

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 60.9 and 61.6 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and the radius-30.45 local anchor cover both cases. -/
theorem quarter_semiprime_609_616 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (609 / 10 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 308 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := semiSeed863.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦ (semiSeed863_primes r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 927 := fun r hr ↦
    ((semiSeed863_primes r (List.mem_toFinset.mp hr)).2).trans (by decide)
  have hw : ∀ r ∈ S, Real.log r ≤ (semiWeight863 r : ℝ) / 10 := fun r hr ↦
    semiSeed863_weights r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ semiWeight863 r := fun r hr ↦
    semiSeed863_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 219564885540 38 32 (2611 / 100) 27 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (2611 / 100 : ℝ) ≤ Real.log ((2 * (weightedPrimeFamily S semiWeight863 348).card : ℕ) : ℝ) := by
    change
      (2611 / 100 : ℝ) ≤
        Real.log ((2 * (weightedPrimeFamily semiSeed863.toFinset semiWeight863 348).card : ℕ) : ℝ)
    have hcount :
      (219564885540 : ℝ) ≤
        ((2 * (weightedPrimeFamily semiSeed863.toFinset semiWeight863 348).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 card863_348
    exact hlog.trans (Real.log_le_log (by norm_num only) hcount)
  have hA : Real.log 2 + (348 : ℝ) / 10 ≤ 711 / 20 := by linarith only [Real.log_two_lt_d9]
  have hB : (370881 / 400 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S semiWeight863 348 927 10
      (by norm_num only) hwpos hprime hbound hw hA hD (by linarith only [hB])
  intro hqsmall
  have hmax : max (711 / 20 : ℝ) (Real.log n - 2611 / 100) ≤ 711 / 20 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor927 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, hrB.trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
