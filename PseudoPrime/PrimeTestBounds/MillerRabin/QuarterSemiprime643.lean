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
import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeGrid359

/-! # Semiprime witnesses on logarithmic scales 63 to 64.3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A radius-31.5 local anchor gives a rejecting prime at most 992.25 when the larger
factor has logarithm at most 36.6. The proper local Fermat kernel transfers the anchor. -/
private theorem semiprime_local_anchor992 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hqlog : Real.log q ≤ (183 / 5 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ 3969 / 4 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
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
      (show localCorrectionCheck (63 / 2) (511 / 100) 5 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (51 / 10 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (63 / 2) := by
    linarith only [hc]
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hproper hpass hGRH (b := 63 / 2) (d := 51 / 10)
      (by norm_num only) hd hqlog
  have hmax : max (63 / 2 : ℝ) (183 / 5 - 51 / 10) ≤ 63 / 2 := by apply max_le <;> norm_num only
  have hr992 : (r : ℝ) ≤ 3969 / 4 := by
    nlinarith only [hb, hmax, le_max_left (63 / 2 : ℝ) (183 / 5 - 51 / 10)]
  exact ⟨r, hr, hr992, hf⟩

/-- The weighted prime family has at least 552906942156 products at budget 359. -/
private theorem card991_359 :
    552906942156 ≤ (weightedPrimeFamily semiSeed991.toFinset semiWeight991 359).card := by
  have hc : 552906942156 ≤ weightedPrimeCount id semiWeights991 359 := semiGrid359_count
  exact
    hc.trans_eq
      (weightedPrimeCount_weights_eq_card semiWeight991 359 semiSeed991 semiWeights991
        semiSeed991_labels.1 semiSeed991_labels.2.2 semiSeed991_labels.2.1)

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 63 and 64.3 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and the radius-31.5 local anchor cover both cases. -/
theorem quarter_semiprime_630_643 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (63 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 643 / 10) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := semiSeed991.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦ (semiSeed991_primes r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 992 := fun r hr ↦
    ((semiSeed991_primes r (List.mem_toFinset.mp hr)).2).trans (by decide)
  have hw : ∀ r ∈ S, Real.log r ≤ (semiWeight991 r : ℝ) / 10 := fun r hr ↦
    semiSeed991_weights r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ semiWeight991 r := fun r hr ↦
    semiSeed991_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1105813884312 41 32 (2773 / 100) 29 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (2773 / 100 : ℝ) ≤ Real.log ((2 * (weightedPrimeFamily S semiWeight991 359).card : ℕ) : ℝ) := by
    change
      (2773 / 100 : ℝ) ≤
        Real.log ((2 * (weightedPrimeFamily semiSeed991.toFinset semiWeight991 359).card : ℕ) : ℝ)
    have hcount :
      (1105813884312 : ℝ) ≤
        ((2 * (weightedPrimeFamily semiSeed991.toFinset semiWeight991 359).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 card991_359
    exact hlog.trans (Real.log_le_log (by norm_num only) hcount)
  have hA : Real.log 2 + (359 : ℝ) / 10 ≤ 183 / 5 := by linarith only [Real.log_two_lt_d9]
  have hB : (3969 / 4 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S semiWeight991 359 992 10
      (by norm_num only) hwpos hprime hbound hw hA hD (by linarith only [hB])
  intro hqsmall
  have hmax : max (183 / 5 : ℝ) (Real.log n - 2773 / 100) ≤ 183 / 5 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor992 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, hrB.trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
