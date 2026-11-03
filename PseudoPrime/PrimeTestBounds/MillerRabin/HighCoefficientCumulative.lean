/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighCoefficientBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCumulative

/-! # Common-scale cumulative high-coefficient witness envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Intersect the existing common-scale base with a history-safe cap: inputs
before logarithmic scale 70000 use four ninths of the entrance squared, while
later inputs use seven sixteenths of the common scale squared. -/
noncomputable def highCoeffHistoryBase (L : ℝ) : ℝ :=
  min (fourNinthsHistoryBase L) (max ((4 / 9 : ℝ) * (70000 : ℝ) ^ 2) ((7 / 16 : ℝ) * L ^ 2))

/-- The new common-scale base is nonnegative for every real scale. -/
theorem highCoeffHistoryBase_nonneg (L : ℝ) : 0 ≤ highCoeffHistoryBase L := by
  exact
    le_min (fourNinthsHistoryBase_nonneg L)
      ((mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4 / 9) (sq_nonneg (70000 : ℝ))).trans
        (le_max_left _ _))

/-- Under GRH the new base bounds the least prime MR witness of every odd
composite whose logarithm is at most `L`. Split inputs at the high-range
entrance and compare each logarithm with its common bound. -/
theorem leastPrime_le_highCoeffScale (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ highCoeffHistoryBase L := by
  apply le_min (leastPrime_le_fourNinthsScale hGRH hn ho hc L hlog)
  have h0 := Real.log_natCast_nonneg n
  by_cases hhigh : (70000 : ℝ) ≤ Real.log n
  · obtain ⟨p, hp, hb, hr⟩ := highCoeff_prime_witness hn ho hc hGRH hhigh
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    have hs := (sq_le_sq₀ h0 (h0.trans hlog)).mpr hlog
    exact
      ((Nat.cast_le.mpr hm).trans hb).trans
        ((mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 7 / 16)).trans
          (le_max_right _ _))
  · obtain ⟨p, hp, hb, hr⟩ := exists_prime_witness_four_ninths hn ho hc hGRH
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    have hs := (sq_le_sq₀ h0 (by norm_num only : (0 : ℝ) ≤ 70000)).mpr (le_of_not_ge hhigh)
    exact
      ((Nat.cast_le.mpr hm).trans hb).trans
        ((mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 4 / 9)).trans
          (le_max_left _ _))

/-- Propagate the new common-scale base through the existing certified
profile history, preserving coverage of all earlier inputs. -/
noncomputable def highCoeffCumulative (N : ℕ) : ℝ :=
  baseHistory TriangularProfile.T TriangularProfile.C highCoeffHistoryBase historyProfiles
    (Real.log N)

/-- Under GRH, the cumulative maximum of least prime MR witnesses through
`N` is bounded by the history-preserving high-coefficient envelope. -/
theorem cumulativeLeastPrime_le_highCoeff
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ highCoeffCumulative N := by
  exact
    cumulativeLeastPrime_le_base highCoeffHistoryBase highCoeffHistoryBase_nonneg
      (fun hn ho hc L hlog ↦ leastPrime_le_highCoeffScale hGRH hn ho hc L hlog) historyProfiles hGRH
      N

/-- The new cumulative envelope never exceeds the preceding four-ninths
history envelope. Monotonicity of the history construction transfers the
pointwise minimum at the common-scale base. -/
theorem highCoeffCumulative_le_previous (N : ℕ) :
    highCoeffCumulative N ≤ fourNinthsCumulativeEnvelope N := by
  apply baseHistory_mono TriangularProfile.T TriangularProfile.C
  intro L
  exact min_le_left _ _

/-- The new cumulative envelope is at most the maximum of the four-ninths
entrance cap and the seven-sixteenths common-scale bound. -/
theorem highCoeffCumulative_le_max (N : ℕ) :
    highCoeffCumulative N ≤
      max ((4 / 9 : ℝ) * (70000 : ℝ) ^ 2) ((7 / 16 : ℝ) * (Real.log N) ^ 2) := by
  exact
    (baseHistory_le_base TriangularProfile.T TriangularProfile.C highCoeffHistoryBase
          historyProfiles (Real.log N)).trans
      (min_le_right _ _)

/-- From logarithmic scale 71000, the seven-sixteenths term absorbs the
four-ninths entrance cap, so the entire history envelope is below it. -/
theorem highCoeffCumulative_le_quad {N : ℕ} (hL : (71000 : ℝ) ≤ Real.log N) :
    highCoeffCumulative N ≤ (7 / 16 : ℝ) * (Real.log N) ^ 2 := by
  apply (highCoeffCumulative_le_max N).trans
  apply max_le ?_ le_rfl
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 71000) hL 2
  nlinarith only [hs]

/-- Under GRH and `log N ≥ 71000`, the cumulative maximum of least prime
MR witnesses is at most `(7 / 16) * log N ^ 2`. The common-scale entrance
cap covers earlier inputs without assuming pointwise monotonicity. -/
theorem cumulativeLeastPrime_le_highCoeff_quad
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {N : ℕ}
    (hL : (71000 : ℝ) ≤ Real.log N) :
    (cumulativeLeastPrime N : ℝ) ≤ (7 / 16 : ℝ) * (Real.log N) ^ 2 := by
  exact (cumulativeLeastPrime_le_highCoeff hGRH N).trans (highCoeffCumulative_le_quad hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
