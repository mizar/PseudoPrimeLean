/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanShortBridge
public import PseudoPrime.PrimeTestBounds.MillerRabin.EarlyGaussianShape

/-! # Nonincreasing normalized series for the reduced-contour bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The normalized coefficient series selects the applicable reduced-contour constant
or the early adaptive Gaussian coefficient. It is separate from the full public minimum. -/
noncomputable def reducedSeriesCoeff (L : ℝ) : ℝ :=
  if 30000000000 ≤ L then (21 / 10) * adaptiveGaussianA L ^ 2
  else if 5000000000 ≤ L then 71 / 250
  else if 1000000000 ≤ L then 3 / 10
  else if 500000000 ≤ L then 161 / 500
  else if 200000000 ≤ L then 39 / 100
  else 1057 / 2500
/-- Under GRH, every odd composite above logarithmic scale `80000` has a rejecting
prime under the normalized series bound. Each branch applies its own actual witness. -/
theorem reducedSeries_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (80000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ reducedSeriesCoeff (Real.log n) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hG : (30000000000 : ℝ) ≤ Real.log n
  · rw [reducedSeriesCoeff, ite_eq_left hG]
    exact prime_witness_earlyGaussian hn ho hc hGRH hG
  · by_cases h5 : (5000000000 : ℝ) ≤ Real.log n
    · rw [reducedSeriesCoeff, ite_eq_right hG, ite_eq_left h5]
      exact prime_witness_reduced0284 hn ho hc hGRH h5
    · by_cases h1 : (1000000000 : ℝ) ≤ Real.log n
      · rw [reducedSeriesCoeff, ite_eq_right hG, ite_eq_right h5, ite_eq_left h1]
        exact prime_witness_reduced030 hn ho hc hGRH h1
      · by_cases hh : (500000000 : ℝ) ≤ Real.log n
        · rw [reducedSeriesCoeff, ite_eq_right hG, ite_eq_right h5, ite_eq_right h1, ite_eq_left hh]
          exact prime_witness_reduced0322 hn ho hc hGRH hh
        · by_cases he : (200000000 : ℝ) ≤ Real.log n
          · rw [reducedSeriesCoeff, ite_eq_right hG, ite_eq_right h5, ite_eq_right h1,
              ite_eq_right hh, ite_eq_left he]
            exact prime_witness_reduced039 hn ho hc hGRH he
          · rw [reducedSeriesCoeff, ite_eq_right hG, ite_eq_right h5, ite_eq_right h1,
              ite_eq_right hh, ite_eq_right he]
            exact prime_witness_04228 hn ho hc hGRH hL
/-- The normalized coefficient series is antitone on the real line. The constants
decrease at each entrance and the Gaussian coefficient is antitone after its entrance. -/
theorem reducedSeries_antitone {L M : ℝ} (hLM : L ≤ M) :
    reducedSeriesCoeff M ≤ reducedSeriesCoeff L := by
  have hg : (30000000000 : ℝ) ≤ M →
      (21 / 10 : ℝ) * adaptiveGaussianA M ^ 2 ≤ 28237 / 100000 := by
    intro hm
    exact (earlyGaussian_coeff_upper M hm).le
  have ha : (30000000000 : ℝ) ≤ L →
      (21 / 10 : ℝ) * adaptiveGaussianA M ^ 2 ≤ (21 / 10 : ℝ) * adaptiveGaussianA L ^ 2 := by
    intro hl
    exact earlyGaussian_coeff_anti hl hLM
  have h30 : (30000000000 : ℝ) ≤ L → 30000000000 ≤ M := fun h ↦ h.trans hLM
  have h5 : (5000000000 : ℝ) ≤ L → 5000000000 ≤ M := fun h ↦ h.trans hLM
  have h1 : (1000000000 : ℝ) ≤ L → 1000000000 ≤ M := fun h ↦ h.trans hLM
  have h05 : (500000000 : ℝ) ≤ L → 500000000 ≤ M := fun h ↦ h.trans hLM
  have h02 : (200000000 : ℝ) ≤ L → 200000000 ≤ M := fun h ↦ h.trans hLM
  unfold reducedSeriesCoeff
  split_ifs <;> first
    | exact ha (by assumption)
    | (have hh := hg (by assumption); linarith only [hh])
    | exact False.elim ((by assumption : ¬(30000000000 : ℝ) ≤ M) (h30 (by assumption)))
    | exact False.elim ((by assumption : ¬(5000000000 : ℝ) ≤ M) (h5 (by assumption)))
    | exact False.elim ((by assumption : ¬(1000000000 : ℝ) ≤ M) (h1 (by assumption)))
    | exact False.elim ((by assumption : ¬(500000000 : ℝ) ≤ M) (h05 (by assumption)))
    | exact False.elim ((by assumption : ¬(200000000 : ℝ) ≤ M) (h02 (by assumption)))
    | norm_num only


end PseudoPrime.PrimeTestBounds.MillerRabin
