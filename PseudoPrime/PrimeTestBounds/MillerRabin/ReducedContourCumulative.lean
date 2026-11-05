/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourHistory

/-! # Cumulative histories for the reduced-contour coefficient series -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- History after adding coefficient `1057 / 2500` at logarithmic scale `80000`. -/
noncomputable def reducedHistory1 : ℝ → ℝ :=
  reducedHistoryStep pairedCumulativeCap 80000 (1057 / 2500)
/-- History after adding coefficient `39 / 100` at scale `2 * 10 ^ 8`. -/
noncomputable def reducedHistory2 : ℝ → ℝ := reducedHistoryStep reducedHistory1 200000000 (39 / 100)
/-- History after adding coefficient `161 / 500` at scale `5 * 10 ^ 8`. -/
noncomputable def reducedHistory3 : ℝ → ℝ :=
  reducedHistoryStep reducedHistory2 500000000 (161 / 500)
/-- History after adding coefficient `3 / 10` at scale `10 ^ 9`. -/
noncomputable def reducedHistory4 : ℝ → ℝ := reducedHistoryStep reducedHistory3 1000000000 (3 / 10)
/-- History after adding coefficient `71 / 250` at scale `5 * 10 ^ 9`. -/
noncomputable def reducedHistory5 : ℝ → ℝ :=
  reducedHistoryStep reducedHistory4 5000000000 (71 / 250)
/-- The successive quadratic history bounds remain nonnegative. -/
theorem reducedHistory_nonneg : ∀ L, 0 ≤ reducedHistory5 L := by
  have hp : ∀ L, 0 ≤ pairedCumulativeCap L := by
    intro L
    exact (by norm_num only : (0 : ℝ) ≤ (4 / 9) * (70000 : ℝ) ^ 2).trans (le_max_left _ _)
  exact reducedStep_nonneg
    (reducedStep_nonneg (reducedStep_nonneg (reducedStep_nonneg
      (reducedStep_nonneg hp (by norm_num only)) (by norm_num only))
        (by norm_num only)) (by norm_num only)) (by norm_num only)
/-- Under GRH, the quadratic history bounds every least witness below the common scale.
Each fixed candidate retains the preceding history at its entrance. -/
theorem leastPrime_le_reducedHistory (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ reducedHistory5 L := by
  have h1 : ∀ {n : ℕ}, 1 < n → Odd n → ¬n.Prime → ∀ L, Real.log n ≤ L →
      (compositeLeastPrime n : ℝ) ≤ reducedHistory1 L := by
    intro n hn ho hc L hlog
    exact reducedStep_bound (by norm_num only) (by norm_num only) hGRH
      (fun hn ho hc L hlog ↦ leastPrime_le_pairedScale hGRH hn ho hc L hlog)
      (fun hn ho hc hL ↦ prime_witness_04228 hn ho hc hGRH hL) hn ho hc L hlog
  have h2 : ∀ {n : ℕ}, 1 < n → Odd n → ¬n.Prime → ∀ L, Real.log n ≤ L →
      (compositeLeastPrime n : ℝ) ≤ reducedHistory2 L := by
    intro n hn ho hc L hlog
    exact reducedStep_bound (by norm_num only) (by norm_num only) hGRH h1
      (fun hn ho hc hL ↦ prime_witness_reduced039 hn ho hc hGRH hL) hn ho hc L hlog
  have h3 : ∀ {n : ℕ}, 1 < n → Odd n → ¬n.Prime → ∀ L, Real.log n ≤ L →
      (compositeLeastPrime n : ℝ) ≤ reducedHistory3 L := by
    intro n hn ho hc L hlog
    exact reducedStep_bound (by norm_num only) (by norm_num only) hGRH h2
      (fun hn ho hc hL ↦ prime_witness_reduced0322 hn ho hc hGRH hL) hn ho hc L hlog
  have h4 : ∀ {n : ℕ}, 1 < n → Odd n → ¬n.Prime → ∀ L, Real.log n ≤ L →
      (compositeLeastPrime n : ℝ) ≤ reducedHistory4 L := by
    intro n hn ho hc L hlog
    exact reducedStep_bound (by norm_num only) (by norm_num only) hGRH h3
      (fun hn ho hc hL ↦ prime_witness_reduced030 hn ho hc hGRH hL) hn ho hc L hlog
  exact reducedStep_bound (by norm_num only) (by norm_num only) hGRH h4
    (fun hn ho hc hL ↦ prime_witness_reduced0284 hn ho hc hGRH hL) hn ho hc L hlog
/-- Add the early Gaussian bound to the fixed history while retaining its entrance history. -/
noncomputable def reducedGaussianHistory (L : ℝ) : ℝ :=
  min (reducedHistory5 L)
    (max (reducedHistory5 30000000000) ((21 / 10 : ℝ) * (adaptiveGaussianA L * L) ^ 2))
/-- The Gaussian history bound is nonnegative at every real scale. -/
theorem reducedGaussianHistory_nonneg : ∀ L, 0 ≤ reducedGaussianHistory L := by
  intro L
  exact le_min (reducedHistory_nonneg L)
    ((mul_nonneg (by norm_num only : (0 : ℝ) ≤ 21 / 10) (sq_nonneg _)).trans (le_max_right _ _))
/-- Under GRH, the early Gaussian history bounds all least witnesses below the common scale.
Monotonicity of the scaled Gaussian slope covers all eligible earlier inputs. -/
theorem leastPrime_le_reducedGaussianScale
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ reducedGaussianHistory L := by
  refine le_min (leastPrime_le_reducedHistory hGRH hn ho hc L hlog) ?_
  by_cases hhigh : (30000000000 : ℝ) ≤ Real.log n
  · obtain ⟨p, hp, hb, hr⟩ := prime_witness_earlyGaussian hn ho hc hGRH hhigh
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    have ha : 0 ≤ adaptiveGaussianA (Real.log n) := by
      have hh := earlyGaussian_slope_lower (Real.log n) hhigh
      linarith only [hh]
    have hs := pow_le_pow_left₀ (mul_nonneg ha (by linarith only [hhigh]))
      (earlyGaussian_scaled_mono hhigh hlog) 2
    have hh := mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 21 / 10)
    rw [mul_pow] at hh
    have hh' : (21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2 * Real.log n ^ 2 ≤
        (21 / 10 : ℝ) * (adaptiveGaussianA L * L) ^ 2 := by
      simpa only [mul_assoc] using hh
    exact ((Nat.cast_le.mpr hm).trans hb).trans (hh'.trans (le_max_right _ _))
  · exact
      (leastPrime_le_reducedHistory hGRH hn ho hc 30000000000 (le_of_not_ge hhigh)).trans
        (le_max_left _ _)

end PseudoPrime.PrimeTestBounds.MillerRabin
