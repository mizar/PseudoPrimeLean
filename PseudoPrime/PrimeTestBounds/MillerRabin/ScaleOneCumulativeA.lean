/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ScaleOneEnvelopeA
public import PseudoPrime.PrimeTestBounds.MillerRabin.SmoothDualCumulative

/-! # Stage A scale-one cumulative upper bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The adaptive Gaussian radius times the scale is nondecreasing from 25000. -/
theorem scaleOne_scaled_monoA {L M : ℝ} (hL : 25000 ≤ L) (hLM : L ≤ M) :
    adaptiveGaussianA L * L ≤ adaptiveGaussianA M * M := by
  have hl : 0 < L := by linarith only [hL]
  have hm : 0 < M := by linarith only [hL, hLM]
  have hs : Real.sqrt L ≤ Real.sqrt M := Real.sqrt_le_sqrt hLM
  have he (x : ℝ) (hx : 0 < x) :
    adaptiveGaussianA x * x =
      (2 * (20115621 / 50000000) * x + (61 / 100) * (28794111 / 12500000) * Real.sqrt x + 39) /
        (10971611 / 5000000) := by
    have hp : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    dsimp only [adaptiveGaussianA]
    have hxr : x / Real.sqrt x = Real.sqrt x := by
      apply (div_eq_iff hp.ne').2
      simpa only [pow_two] using (Real.sq_sqrt hx.le).symm
    have hterm :
      (((61 / 100 : ℝ) * (28794111 / 12500000)) / Real.sqrt x) * x =
        ((61 / 100 : ℝ) * (28794111 / 12500000)) * Real.sqrt x := by
      rw [div_mul_eq_mul_div, mul_div_assoc, hxr]
    rw [div_mul_eq_mul_div, add_mul, add_mul, hterm, div_mul_cancel₀ _ hx.ne']
  rw [he L hl, he M hm]
  apply (div_le_div_iff_of_pos_right (by norm_num only)).2
  nlinarith only [hLM, hs]

/-- Preserve the pre-entrance four-ninths history in the Gaussian cap. -/
noncomputable def scaleOneCapA (L : ℝ) : ℝ :=
  max ((4 / 9 : ℝ) * (25000 : ℝ) ^ 2) ((21 / 10 : ℝ) * (adaptiveGaussianA L * L) ^ 2)

/-- Under GRH, the history-safe cap bounds every least witness below the common scale. -/
theorem scaleOne_leastScaleA (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ}
    (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ scaleOneCapA L := by
  by_cases hhigh : (25000 : ℝ) ≤ Real.log n
  · obtain ⟨p, hp, hb, hr⟩ := prime_witness_scaleOne hn ho hc hGRH hhigh
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    have ha : 0 ≤ adaptiveGaussianA (Real.log n) := by
      have hh := (scaleOne_gaussian_slope (Real.log n) hhigh).1
      linarith only [hh]
    have hs :=
      pow_le_pow_left₀ (mul_nonneg ha (by linarith only [hhigh])) (scaleOne_scaled_monoA hhigh hlog)
        2
    have hh := mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 21 / 10)
    rw [mul_pow] at hh
    have hh' :
      (21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2 * Real.log n ^ 2 ≤
        (21 / 10 : ℝ) * (adaptiveGaussianA L * L) ^ 2 := by
      simpa only [mul_assoc] using hh
    exact ((Nat.cast_le.mpr hm).trans hb).trans (hh'.trans (le_max_right _ _))
  · have hp := leastPrime_le_fourNinthsScale hGRH hn ho hc 25000 (le_of_not_ge hhigh)
    exact (hp.trans (min_le_right _ _)).trans (le_max_left _ _)

/-- Intersect the previous cumulative envelope with the new history-safe cap. -/
noncomputable def scaleOneCumulativeA (N : ℕ) : ℝ :=
  min (smoothCumulative N) (scaleOneCapA (Real.log N))

/-- Under GRH, the stage A cumulative envelope bounds every natural-number endpoint. -/
theorem cumulativeLeastPrime_le_scaleOneA
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ scaleOneCumulativeA N := by
  apply le_min (cumulativeLeastPrime_le_smooth hGRH N)
  have hnonneg : ∀ L, 0 ≤ scaleOneCapA L := by
    intro L
    exact (by norm_num only : (0 : ℝ) ≤ (4 / 9) * (25000 : ℝ) ^ 2) |>.trans (le_max_left _ _)
  have h :=
    cumulativeLeastPrime_le_base scaleOneCapA hnonneg
      (fun hn ho hc L hlog ↦ scaleOne_leastScaleA hGRH hn ho hc L hlog) [] hGRH N
  simpa only [baseHistory] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
