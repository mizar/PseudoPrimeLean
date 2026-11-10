/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Count197
import PseudoPrime.PrimeTestBounds.MillerRabin.SignedWeightedCell
import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors
import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeSmallFactor

/-! # Semiprime witnesses on logarithmic scales 28.2 to 31.5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A radius-fourteen local anchor gives a rejecting prime at most 196 when the larger
factor has logarithm at most 17.99. The proper local Fermat kernel transfers the anchor. -/
private theorem semiprime_local_anchor196 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hqlog : Real.log q ≤ (1799 / 100 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ 196 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
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
  have hc := localCorrectionCheck_sound (show localCorrectionCheck 14 4 4 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat] at hc
  have hd : (399 / 100 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection 14 := by
    linarith only [hc]
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hproper hpass hGRH (b := 14) (d := 399 / 100)
      (by norm_num only) hd hqlog
  have hmax : max (14 : ℝ) (1799 / 100 - 399 / 100) ≤ 14 := by apply max_le <;> norm_num only
  have hr196 : (r : ℝ) ≤ 196 := by
    nlinarith only [hb, hmax, le_max_left (14 : ℝ) (1799 / 100 - 399 / 100)]
  exact ⟨r, hr, hr196, hf⟩

/-- The weighted prime family has 387518 products at budget 172. -/
private theorem card89_172 :
    (weightedPrimeFamily primeSeed89Primes.toFinset primeSeed89Weight 172).card = 387518 := by
  have h :=
    (weightedPrimeCount_weights_eq_card primeSeed89Weight 172 primeSeed89Primes primeSeed89Weights
          primeSeed89_labels.1 primeSeed89_labels.2.2 primeSeed89_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 197 primeSeed89Weights primeSeed89Row197 primeSeed89Tail197
          primeSeed89_checked197 172 (by decide)).symm)
  rw [show primeSeed89Row197.getD 172 0 = 387518 by decide +kernel] at h
  exact h

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 28.2 and 31.5 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and the radius-fourteen local anchor cover both cases. -/
theorem quarter_semiprime_282_315 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (141 / 5 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 63 / 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := primeSeed89Primes.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (primeSeed89_prime_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 196 := fun r hr ↦
    ((primeSeed89_prime_supply r (List.mem_toFinset.mp hr)).2).trans (by decide)
  have hw : ∀ r ∈ S, Real.log r ≤ (primeSeed89Weight r : ℝ) / 10 := fun r hr ↦
    primeSeed89_weight_bounds r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ primeSeed89Weight r := fun r hr ↦
    primeSeed89_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 775036 20 32 (1355 / 100) 14 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (1355 / 100 : ℝ) ≤
      Real.log ((2 * (weightedPrimeFamily S primeSeed89Weight 172).card : ℕ) : ℝ) := by
    change
      (1355 / 100 : ℝ) ≤
        Real.log
          ((2 * (weightedPrimeFamily primeSeed89Primes.toFinset primeSeed89Weight 172).card : ℕ) :
            ℝ)
    rw [card89_172]
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    exact hlog
  have hA : Real.log 2 + (172 : ℝ) / 10 ≤ 1799 / 100 := by linarith only [Real.log_two_lt_d9]
  have hB : (196 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S primeSeed89Weight 172 196 10
      (by norm_num only) hwpos hprime hbound hw hA hD hB
  intro hqsmall
  have hmax : max (1799 / 100 : ℝ) (Real.log n - 1355 / 100) ≤ 1799 / 100 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor196 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, hrB.trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
