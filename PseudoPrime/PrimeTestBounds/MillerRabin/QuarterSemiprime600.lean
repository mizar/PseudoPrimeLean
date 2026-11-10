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

/-! # Semiprime witnesses on logarithmic scales 59.1 to 60 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A radius-29.55 local anchor gives a rejecting prime at most 873.2025 when the larger
factor has logarithm at most 34.55. The proper local Fermat kernel transfers the anchor. -/
private theorem semiprime_local_anchor873 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hqlog : Real.log q ≤ (691 / 20 : ℝ)) :
    ∃ r : ℕ,
      r.Prime ∧ (r : ℝ) ≤ 349281 / 400 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
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
      (show localCorrectionCheck (591 / 20) (501 / 100) 5 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (5 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (591 / 20) := by
    linarith only [hc]
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hproper hpass hGRH (b := 591 / 20) (d := 5)
      (by norm_num only) hd hqlog
  have hmax : max (591 / 20 : ℝ) (691 / 20 - 5) ≤ 591 / 20 := by apply max_le <;> norm_num only
  have hr873 : (r : ℝ) ≤ 349281 / 400 := by
    nlinarith only [hb, hmax, le_max_left (591 / 20 : ℝ) (691 / 20 - 5)]
  exact ⟨r, hr, hr873, hf⟩

/-- The weighted prime family has at least 62279017801 products at budget 338. -/
private theorem card863_338 :
    62279017801 ≤ (weightedPrimeFamily semiSeed863.toFinset semiWeight863 338).card := by
  have hb := primeSeed373_count_lower 270 (by decide)
  rw [show primeSeed373Row14.getD 270 0 = 808818413 by decide +kernel] at hb
  have hg := weightedPrimeCount_group_lower 68 270 76 1 primeSeed373Weights (by decide)
  have hc : 62279017801 ≤ weightedPrimeCount id semiWeights863 338 := by
    have hm := (Nat.mul_le_mul_left (Nat.choose (76 + 1) 1) hb).trans hg
    norm_num only [Nat.choose_one_right] at hm
    exact hm
  exact
    hc.trans_eq
      (weightedPrimeCount_weights_eq_card semiWeight863 338 semiSeed863 semiWeights863
        semiSeed863_labels.1 semiSeed863_labels.2.2 semiSeed863_labels.2.1)

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 59.1 and 60 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and the radius-29.55 local anchor cover both cases. -/
theorem quarter_semiprime_591_600 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (591 / 10 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 60) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := semiSeed863.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦ (semiSeed863_primes r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 873 := fun r hr ↦
    ((semiSeed863_primes r (List.mem_toFinset.mp hr)).2).trans (by decide)
  have hw : ∀ r ∈ S, Real.log r ≤ (semiWeight863 r : ℝ) / 10 := fun r hr ↦
    semiSeed863_weights r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ semiWeight863 r := fun r hr ↦
    semiSeed863_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 124558035602 37 32 (1277 / 50) 27 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (1277 / 50 : ℝ) ≤ Real.log ((2 * (weightedPrimeFamily S semiWeight863 338).card : ℕ) : ℝ) := by
    change
      (1277 / 50 : ℝ) ≤
        Real.log ((2 * (weightedPrimeFamily semiSeed863.toFinset semiWeight863 338).card : ℕ) : ℝ)
    have hcount :
      (124558035602 : ℝ) ≤
        ((2 * (weightedPrimeFamily semiSeed863.toFinset semiWeight863 338).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 card863_338
    exact hlog.trans (Real.log_le_log (by norm_num only) hcount)
  have hA : Real.log 2 + (338 : ℝ) / 10 ≤ 691 / 20 := by linarith only [Real.log_two_lt_d9]
  have hB : (349281 / 400 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S semiWeight863 338 873 10
      (by norm_num only) hwpos hprime hbound hw hA hD (by linarith only [hB])
  intro hqsmall
  have hmax : max (691 / 20 : ℝ) (Real.log n - 1277 / 50) ≤ 691 / 20 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor873 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, hrB.trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
