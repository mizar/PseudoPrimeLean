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

/-! # Semiprime witnesses on logarithmic scales 40.2 to 43.9 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A radius-20.1 local anchor gives a rejecting prime at most 404.01 when the larger
factor has logarithm at most 24.6. The proper local Fermat kernel transfers the anchor. -/
private theorem semiprime_local_anchor404 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hqlog : Real.log q ≤ (123 / 5 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ 40401 / 100 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
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
      (show localCorrectionCheck (201 / 10) (451 / 100) 5 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (9 / 2 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (201 / 10) := by
    linarith only [hc]
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hproper hpass hGRH (b := 201 / 10) (d := 9 / 2)
      (by norm_num only) hd hqlog
  have hmax : max (201 / 10 : ℝ) (123 / 5 - 9 / 2) ≤ 201 / 10 := by apply max_le <;> norm_num only
  have hr404 : (r : ℝ) ≤ 40401 / 100 := by
    nlinarith only [hb, hmax, le_max_left (201 / 10 : ℝ) (123 / 5 - 9 / 2)]
  exact ⟨r, hr, hr404, hf⟩

/-- The weighted prime family has at least 132492865 products at budget 239. -/
private theorem card373_239 :
    132492865 ≤ (weightedPrimeFamily primeSeed373Primes.toFinset primeSeed373Weight 239).card := by
  have h := primeSeed373_count_lower 239 (by decide)
  rw [show primeSeed373Row14.getD 239 0 = 132492865 by decide +kernel] at h
  exact
    h.trans_eq
      (weightedPrimeCount_weights_eq_card primeSeed373Weight 239 primeSeed373Primes
        primeSeed373Weights primeSeed373_labels.1 primeSeed373_labels.2.2 primeSeed373_labels.2.1)

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 40.2 and 43.9 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and the radius-20.1 local anchor cover both cases. -/
theorem quarter_semiprime_402_439 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (201 / 5 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 439 / 10) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := primeSeed373Primes.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (primeSeed373_prime_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 404 := fun r hr ↦
    ((primeSeed373_prime_supply r (List.mem_toFinset.mp hr)).2).trans (by decide)
  have hw : ∀ r ∈ S, Real.log r ≤ (primeSeed373Weight r : ℝ) / 10 := fun r hr ↦
    primeSeed373_weight_bounds r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ primeSeed373Weight r := fun r hr ↦
    primeSeed373_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 264985730 28 32 (1939 / 100) 20 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (1939 / 100 : ℝ) ≤
      Real.log ((2 * (weightedPrimeFamily S primeSeed373Weight 239).card : ℕ) : ℝ) := by
    change
      (1939 / 100 : ℝ) ≤
        Real.log
          ((2 * (weightedPrimeFamily primeSeed373Primes.toFinset primeSeed373Weight 239).card : ℕ) :
            ℝ)
    have hcount :
      (264985730 : ℝ) ≤
        ((2 * (weightedPrimeFamily primeSeed373Primes.toFinset primeSeed373Weight 239).card : ℕ) :
          ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 2 card373_239
    exact hlog.trans (Real.log_le_log (by norm_num only) hcount)
  have hA : Real.log 2 + (239 : ℝ) / 10 ≤ 123 / 5 := by linarith only [Real.log_two_lt_d9]
  have hB : (40401 / 100 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S primeSeed373Weight 239 404 10
      (by norm_num only) hwpos hprime hbound hw hA hD (by linarith only [hB])
  intro hqsmall
  have hmax : max (123 / 5 : ℝ) (Real.log n - 1939 / 100) ≤ 123 / 5 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor404 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, hrB.trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
