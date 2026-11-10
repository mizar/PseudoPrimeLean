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

/-! # Semiprime witnesses on logarithmic scales 58.6 to 59.1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A radius-29.3 local anchor gives a rejecting prime at most 858.49 when the larger
factor has logarithm at most 34.3. The proper local Fermat kernel transfers the anchor. -/
private theorem semiprime_local_anchor858 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hqlog : Real.log q ≤ (343 / 10 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ 85849 / 100 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
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
      (show localCorrectionCheck (293 / 10) (501 / 100) 5 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (5 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (293 / 10) := by
    linarith only [hc]
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hproper hpass hGRH (b := 293 / 10) (d := 5)
      (by norm_num only) hd hqlog
  have hmax : max (293 / 10 : ℝ) (343 / 10 - 5) ≤ 293 / 10 := by apply max_le <;> norm_num only
  have hr858 : (r : ℝ) ≤ 85849 / 100 := by
    nlinarith only [hb, hmax, le_max_left (293 / 10 : ℝ) (343 / 10 - 5)]
  exact ⟨r, hr, hr858, hf⟩

/-- The weighted prime family has at least 29941345795 products at budget 336. -/
private theorem card373_336 :
    29941345795 ≤
      (weightedPrimeFamily primeSeed373Primes.toFinset primeSeed373Weight 336).card := by
  have h := primeSeed373_count_lower 336 (by decide)
  rw [show primeSeed373Row14.getD 336 0 = 29941345795 by decide +kernel] at h
  exact
    h.trans_eq
      (weightedPrimeCount_weights_eq_card primeSeed373Weight 336 primeSeed373Primes
        primeSeed373Weights primeSeed373_labels.1 primeSeed373_labels.2.2 primeSeed373_labels.2.1)

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 58.6 and 59.1 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and the radius-29.3 local anchor cover both cases. -/
theorem quarter_semiprime_586_591 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (293 / 5 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 591 / 10) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := primeSeed373Primes.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (primeSeed373_prime_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 858 := fun r hr ↦
    ((primeSeed373_prime_supply r (List.mem_toFinset.mp hr)).2).trans (by decide)
  have hw : ∀ r ∈ S, Real.log r ≤ (primeSeed373Weight r : ℝ) / 10 := fun r hr ↦
    primeSeed373_weight_bounds r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ primeSeed373Weight r := fun r hr ↦
    primeSeed373_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 59882691590 36 32 (2481 / 100) 26 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (2481 / 100 : ℝ) ≤
      Real.log ((2 * (weightedPrimeFamily S primeSeed373Weight 336).card : ℕ) : ℝ) := by
    change
      (2481 / 100 : ℝ) ≤
        Real.log
          ((2 * (weightedPrimeFamily primeSeed373Primes.toFinset primeSeed373Weight 336).card : ℕ) :
            ℝ)
    have hcount :
      (59882691590 : ℝ) ≤
        ((2 * (weightedPrimeFamily primeSeed373Primes.toFinset primeSeed373Weight 336).card : ℕ) :
          ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 card373_336
    exact hlog.trans (Real.log_le_log (by norm_num only) hcount)
  have hA : Real.log 2 + (336 : ℝ) / 10 ≤ 343 / 10 := by linarith only [Real.log_two_lt_d9]
  have hB : (85849 / 100 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S primeSeed373Weight 336 858 10
      (by norm_num only) hwpos hprime hbound hw hA hD (by linarith only [hB])
  intro hqsmall
  have hmax : max (343 / 10 : ℝ) (Real.log n - 2481 / 100) ≤ 343 / 10 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor858 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, hrB.trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
