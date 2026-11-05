/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.DualScaleWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.DualGaussianShape
/-! # Nonincreasing dual-scale witness series -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- The normalized coefficient combines five dual-scale profiles with the existing
low-scale and early Gaussian witnesses. It is separate from the full public minimum. -/
noncomputable def dualSeriesCoeff (L : ℝ) : ℝ :=
  if 200000000 ≤ L then (21 / 10) * adaptiveGaussianA L ^ 2
  else if 100000000 ≤ L then 29 / 100
  else if 60000000 ≤ L then 31 / 100
  else if 30000000 ≤ L then 33 / 100
  else if 15000000 ≤ L then 9 / 25
  else if 5000000 ≤ L then 2 / 5
  else 1057 / 2500
/-- Under GRH, the coefficient series bounds an actual rejecting prime for every odd
composite at or above its entrance. Each branch uses its certified witness. -/
theorem dualSeries_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (80000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ dualSeriesCoeff (Real.log n) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hG : (200000000 : ℝ) ≤ Real.log n
  · rw [dualSeriesCoeff, ite_eq_left hG]
    exact prime_witness_dualGaussian hn ho hc hGRH hG
  · by_cases h5 : (100000000 : ℝ) ≤ Real.log n
    · rw [dualSeriesCoeff, ite_eq_right hG, ite_eq_left h5]
      exact prime_witness_dual029 hn ho hc hGRH h5
    · by_cases h4 : (60000000 : ℝ) ≤ Real.log n
      · rw [dualSeriesCoeff, ite_eq_right hG, ite_eq_right h5, ite_eq_left h4]
        exact prime_witness_dual031 hn ho hc hGRH h4
      · by_cases h3 : (30000000 : ℝ) ≤ Real.log n
        · rw [dualSeriesCoeff, ite_eq_right hG, ite_eq_right h5, ite_eq_right h4, ite_eq_left h3]
          exact prime_witness_dual033 hn ho hc hGRH h3
        · by_cases h2 : (15000000 : ℝ) ≤ Real.log n
          · rw [dualSeriesCoeff, ite_eq_right hG, ite_eq_right h5, ite_eq_right h4,
              ite_eq_right h3, ite_eq_left h2]
            exact prime_witness_dual036 hn ho hc hGRH h2
          · by_cases h1 : (5000000 : ℝ) ≤ Real.log n
            · rw [dualSeriesCoeff, ite_eq_right hG, ite_eq_right h5, ite_eq_right h4,
                ite_eq_right h3, ite_eq_right h2, ite_eq_left h1]
              exact prime_witness_dual040 hn ho hc hGRH h1
            · rw [dualSeriesCoeff, ite_eq_right hG, ite_eq_right h5, ite_eq_right h4,
                ite_eq_right h3, ite_eq_right h2, ite_eq_right h1]
              exact prime_witness_04228 hn ho hc hGRH hL

/-- The coefficient series is nonincreasing: every fixed entrance decreases the
coefficient and the final Gaussian coefficient is nonincreasing after its entrance. -/
theorem dualSeries_antitone {L M : ℝ} (hLM : L ≤ M) : dualSeriesCoeff M ≤ dualSeriesCoeff L := by
  have hg : (200000000 : ℝ) ≤ M →
      (21 / 10 : ℝ) * adaptiveGaussianA M ^ 2 ≤ 29 / 100 := by
    intro hm
    have ha := dualGaussian_slope_lower M hm
    have hb := dualGaussian_slope_upper M hm
    have hs := pow_le_pow_left₀ (show 0 ≤ adaptiveGaussianA M by linarith only [ha]) hb 2
    nlinarith only [hs]
  have ha : (200000000 : ℝ) ≤ L →
      (21 / 10 : ℝ) * adaptiveGaussianA M ^ 2 ≤ (21 / 10 : ℝ) * adaptiveGaussianA L ^ 2 := by
    intro hl
    exact dualGaussian_coeff_anti hl hLM
  have h30 : (200000000 : ℝ) ≤ L → 200000000 ≤ M := fun h ↦ h.trans hLM
  have h100 : (100000000 : ℝ) ≤ L → 100000000 ≤ M := fun h ↦ h.trans hLM
  have h60 : (60000000 : ℝ) ≤ L → 60000000 ≤ M := fun h ↦ h.trans hLM
  have h30m : (30000000 : ℝ) ≤ L → 30000000 ≤ M := fun h ↦ h.trans hLM
  have h15 : (15000000 : ℝ) ≤ L → 15000000 ≤ M := fun h ↦ h.trans hLM
  have h5 : (5000000 : ℝ) ≤ L → 5000000 ≤ M := fun h ↦ h.trans hLM
  unfold dualSeriesCoeff
  split_ifs <;> first
    | exact ha (by assumption)
    | (have hh := hg (by assumption); linarith only [hh])
    | exact False.elim ((by assumption : ¬(200000000 : ℝ) ≤ M) (h30 (by assumption)))
    | exact False.elim ((by assumption : ¬(100000000 : ℝ) ≤ M) (h100 (by assumption)))
    | exact False.elim ((by assumption : ¬(60000000 : ℝ) ≤ M) (h60 (by assumption)))
    | exact False.elim ((by assumption : ¬(30000000 : ℝ) ≤ M) (h30m (by assumption)))
    | exact False.elim ((by assumption : ¬(15000000 : ℝ) ≤ M) (h15 (by assumption)))
    | exact False.elim ((by assumption : ¬(5000000 : ℝ) ≤ M) (h5 (by assumption)))
    | norm_num only
end PseudoPrime.PrimeTestBounds.MillerRabin
