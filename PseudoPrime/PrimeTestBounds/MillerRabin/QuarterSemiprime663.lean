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
import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeGrid372

/-! # Semiprime witnesses on logarithmic scales 65.4 to 66.3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A radius-32.7 local anchor gives a rejecting prime at most 1069.29 when the larger
factor has logarithm at most 37.9. The proper local Fermat kernel transfers the anchor. -/
private theorem semiprime_local_anchor1069 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hqlog : Real.log q ≤ (379 / 10 : ℝ)) :
    ∃ r : ℕ,
      r.Prime ∧ (r : ℝ) ≤ 106929 / 100 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
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
      (show localCorrectionCheck (327 / 10) (521 / 100) 6 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (26 / 5 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (327 / 10) := by
    linarith only [hc]
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hproper hpass hGRH (b := 327 / 10) (d := 26 / 5)
      (by norm_num only) hd hqlog
  have hmax : max (327 / 10 : ℝ) (379 / 10 - 26 / 5) ≤ 327 / 10 := by apply max_le <;> norm_num only
  have hr1069 : (r : ℝ) ≤ 106929 / 100 := by
    nlinarith only [hb, hmax, le_max_left (327 / 10 : ℝ) (379 / 10 - 26 / 5)]
  exact ⟨r, hr, hr1069, hf⟩

/-- The weighted prime family has at least 1175771945027 products at budget 372. -/
private theorem card991_372 :
    1175771945027 ≤ (weightedPrimeFamily semiSeed991.toFinset semiWeight991 372).card := by
  have hc : 1175771945027 ≤ weightedPrimeCount id semiWeights991 372 := semiGrid372_count
  exact
    hc.trans_eq
      (weightedPrimeCount_weights_eq_card semiWeight991 372 semiSeed991 semiWeights991
        semiSeed991_labels.1 semiSeed991_labels.2.2 semiSeed991_labels.2.1)

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 65.4 and 66.3 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and the radius-32.7 local anchor cover both cases. -/
theorem quarter_semiprime_654_663 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (327 / 5 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 663 / 10) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := semiSeed991.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦ (semiSeed991_primes r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 1069 := fun r hr ↦
    ((semiSeed991_primes r (List.mem_toFinset.mp hr)).2).trans (by decide)
  have hw : ∀ r ∈ S, Real.log r ≤ (semiWeight991 r : ℝ) / 10 := fun r hr ↦
    semiSeed991_weights r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ semiWeight991 r := fun r hr ↦
    semiSeed991_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2351543890054 42 32 (712 / 25) 30 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (712 / 25 : ℝ) ≤ Real.log ((2 * (weightedPrimeFamily S semiWeight991 372).card : ℕ) : ℝ) := by
    change
      (712 / 25 : ℝ) ≤
        Real.log ((2 * (weightedPrimeFamily semiSeed991.toFinset semiWeight991 372).card : ℕ) : ℝ)
    have hcount :
      (2351543890054 : ℝ) ≤
        ((2 * (weightedPrimeFamily semiSeed991.toFinset semiWeight991 372).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 card991_372
    exact hlog.trans (Real.log_le_log (by norm_num only) hcount)
  have hA : Real.log 2 + (372 : ℝ) / 10 ≤ 379 / 10 := by linarith only [Real.log_two_lt_d9]
  have hB : (106929 / 100 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S semiWeight991 372 1069 10
      (by norm_num only) hwpos hprime hbound hw hA hD (by linarith only [hB])
  intro hqsmall
  have hmax : max (379 / 10 : ℝ) (Real.log n - 712 / 25) ≤ 379 / 10 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor1069 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, hrB.trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
