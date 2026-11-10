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

/-! # Semiprime witnesses on logarithmic scales 34 to 36.6 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A radius-17 local anchor gives a rejecting prime at most 289 when the larger
factor has logarithm at most 21.35. The proper local Fermat kernel transfers the anchor. -/
private theorem semiprime_local_anchor289 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hqlog : Real.log q ≤ (427 / 20 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ 289 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
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
    localCorrectionCheck_sound (show localCorrectionCheck 17 (436 / 100) 5 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (87 / 20 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection 17 := by
    linarith only [hc]
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hproper hpass hGRH (b := 17) (d := 87 / 20)
      (by norm_num only) hd hqlog
  have hmax : max (17 : ℝ) (427 / 20 - 87 / 20) ≤ 17 := by apply max_le <;> norm_num only
  have hr289 : (r : ℝ) ≤ 289 := by
    nlinarith only [hb, hmax, le_max_left (17 : ℝ) (427 / 20 - 87 / 20)]
  exact ⟨r, hr, hr289, hf⟩

/-- The weighted prime family has 2121938 products at budget 206. -/
private theorem card89_206 :
    (weightedPrimeFamily primeSeed89Primes.toFinset primeSeed89Weight 206).card = 2121938 := by
  have h :=
    (weightedPrimeCount_weights_eq_card primeSeed89Weight 206 primeSeed89Primes primeSeed89Weights
          primeSeed89_labels.1 primeSeed89_labels.2.2 primeSeed89_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 282 primeSeed89Weights primeSeed89Row282 primeSeed89Tail282
          primeSeed89_checked282 206 (by decide)).symm)
  rw [show primeSeed89Row282.getD 206 0 = 2121938 by decide +kernel] at h
  exact h

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 34 and 36.6 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and the radius-17 local anchor cover both cases. -/
theorem quarter_semiprime_34_366 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (34 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 183 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := primeSeed89Primes.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (primeSeed89_prime_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 289 := fun r hr ↦
    ((primeSeed89_prime_supply r (List.mem_toFinset.mp hr)).2).trans (by decide)
  have hw : ∀ r ∈ S, Real.log r ≤ (primeSeed89Weight r : ℝ) / 10 := fun r hr ↦
    primeSeed89_weight_bounds r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ primeSeed89Weight r := fun r hr ↦
    primeSeed89_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 4243876 23 32 (61 / 4) 16 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (61 / 4 : ℝ) ≤ Real.log ((2 * (weightedPrimeFamily S primeSeed89Weight 206).card : ℕ) : ℝ) := by
    change
      (61 / 4 : ℝ) ≤
        Real.log
          ((2 * (weightedPrimeFamily primeSeed89Primes.toFinset primeSeed89Weight 206).card : ℕ) :
            ℝ)
    rw [card89_206]
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    exact hlog
  have hA : Real.log 2 + (206 : ℝ) / 10 ≤ 427 / 20 := by linarith only [Real.log_two_lt_d9]
  have hB : (289 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S primeSeed89Weight 206 289 10
      (by norm_num only) hwpos hprime hbound hw hA hD hB
  intro hqsmall
  have hmax : max (427 / 20 : ℝ) (Real.log n - 61 / 4) ≤ 427 / 20 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor289 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, hrB.trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
