/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Count282
import PseudoPrime.PrimeTestBounds.MillerRabin.SignedWeightedCell
import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors
import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeSmallFactor

/-! # Semiprime witnesses on logarithmic scales 38.6 to 40.2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A radius-19.3 local anchor gives a rejecting prime at most 372.49 when the larger
factor has logarithm at most 23.8. The proper local Fermat kernel transfers the anchor. -/
private theorem semiprime_local_anchor372 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hqlog : Real.log q ≤ (119 / 5 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ 37249 / 100 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
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
      (show localCorrectionCheck (193 / 10) (451 / 100) 5 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (9 / 2 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (193 / 10) := by
    linarith only [hc]
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hproper hpass hGRH (b := 193 / 10) (d := 9 / 2)
      (by norm_num only) hd hqlog
  have hmax : max (193 / 10 : ℝ) (119 / 5 - 9 / 2) ≤ 193 / 10 := by apply max_le <;> norm_num only
  have hr372 : (r : ℝ) ≤ 37249 / 100 := by
    nlinarith only [hb, hmax, le_max_left (193 / 10 : ℝ) (119 / 5 - 9 / 2)]
  exact ⟨r, hr, hr372, hf⟩

/-- The weighted prime family has 6775332 products at budget 231. -/
private theorem card89_231 :
    (weightedPrimeFamily primeSeed89Primes.toFinset primeSeed89Weight 231).card = 6775332 := by
  have h :=
    (weightedPrimeCount_weights_eq_card primeSeed89Weight 231 primeSeed89Primes primeSeed89Weights
          primeSeed89_labels.1 primeSeed89_labels.2.2 primeSeed89_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 282 primeSeed89Weights primeSeed89Row282 primeSeed89Tail282
          primeSeed89_checked282 231 (by decide)).symm)
  rw [show primeSeed89Row282.getD 231 0 = 6775332 by decide +kernel] at h
  exact h

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 38.6 and 40.2 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and the radius-19.3 local anchor cover both cases. -/
theorem quarter_semiprime_386_402 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (193 / 5 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 201 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := primeSeed89Primes.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (primeSeed89_prime_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 372 := fun r hr ↦
    ((primeSeed89_prime_supply r (List.mem_toFinset.mp hr)).2).trans (by decide)
  have hw : ∀ r ∈ S, Real.log r ≤ (primeSeed89Weight r : ℝ) / 10 := fun r hr ↦
    primeSeed89_weight_bounds r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ primeSeed89Weight r := fun r hr ↦
    primeSeed89_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 13550664 25 32 (1642 / 100) 18 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (1642 / 100 : ℝ) ≤
      Real.log ((2 * (weightedPrimeFamily S primeSeed89Weight 231).card : ℕ) : ℝ) := by
    change
      (1642 / 100 : ℝ) ≤
        Real.log
          ((2 * (weightedPrimeFamily primeSeed89Primes.toFinset primeSeed89Weight 231).card : ℕ) :
            ℝ)
    rw [card89_231]
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    exact hlog
  have hA : Real.log 2 + (231 : ℝ) / 10 ≤ 119 / 5 := by linarith only [Real.log_two_lt_d9]
  have hB : (37249 / 100 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S primeSeed89Weight 231 372 10
      (by norm_num only) hwpos hprime hbound hw hA hD (by linarith only [hB])
  intro hqsmall
  have hmax : max (119 / 5 : ℝ) (Real.log n - 1642 / 100) ≤ 119 / 5 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor372 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, hrB.trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
