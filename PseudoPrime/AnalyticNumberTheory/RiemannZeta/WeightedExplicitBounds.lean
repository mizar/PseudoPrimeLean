/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroSeriesLimit
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FiniteZeroSums
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ContourKernelConjugation
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.WeightedSumIntegral
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogResidueAtZeroClosedForm
public import PseudoPrime.Analysis.ExplicitFormulaHelpers

/-! # Explicit weighted zeta bounds and trivial-zero corrections -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- RH bounds the reciprocal residue-ledger error after its exact finite trivial-zero sum
is removed. This retains both signs of the error needed in Lemma 2.4. -/
theorem abs_reciprocalResidueLedger_error_le (hRH : RiemannHypothesis) {x τ : ℝ} (hx : 1 < x)
    (hτ : 1 < τ) (m : ℕ) :
    |(riemannZetaReciprocalContourResidueLedger x (unifiedRectangleLower m)
              (unifiedTauRectangleUpper τ m)).re -
          (Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x) -
          (∑
              ρ ∈
                (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                      (unifiedTauRectangleUpper τ m)).filter
                  (fun ρ ↦ ρ.re < 0),
              riemannZetaReciprocalZeroContribution x ρ).re| ≤
      2 * RiemannXi.riemannZeroMass / Real.sqrt x := by
  classical
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  let S := riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper τ m)
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ ↦ ρ.re < 0)
      (riemannZetaReciprocalZeroContribution x)
  have hb :=
    norm_sum_riemannZetaReciprocalZeroContribution_le hRH hxpos (S.filter (fun ρ ↦ ¬ρ.re < 0))
      (fun ρ hρ ↦ (mem_riemannZetaZerosInAnyRectangle_iff.mp (Finset.mem_filter.mp hρ).1).2)
      (fun ρ hρ ↦ not_lt.mp (Finset.mem_filter.mp hρ).2)
  have hre0 : (Complex.log (2 * (Real.pi : ℂ)) * (x : ℂ)⁻¹).re = Real.log (2 * Real.pi) / x := by
    rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul, ←
      Complex.ofReal_log (mul_nonneg (by norm_num only) Real.pi_pos.le), ← Complex.ofReal_inv, ←
      Complex.ofReal_mul, Complex.ofReal_re]
    exact div_eq_mul_inv _ _ |>.symm
  have hre1 :
    (Complex.log (x : ℂ) - 1 - (Real.eulerMascheroniConstant : ℂ)).re =
      Real.log x - 1 - Real.eulerMascheroniConstant := by
    rw [← Complex.ofReal_log hxpos.le]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  rw [riemannZetaReciprocalContourResidueLedger_unifiedTau_eq hτ,
    riemannZetaReciprocalResidueAtZero_eq, riemannZetaReciprocalResidueAtOne_eq hxpos,
    Complex.add_re, Complex.add_re, hre0, hre1]
  change
    |Real.log (2 * Real.pi) / x + (Real.log x - 1 - Real.eulerMascheroniConstant) +
            (∑ ρ ∈ S, riemannZetaReciprocalZeroContribution x ρ).re -
          (Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x) -
          (∑ ρ ∈ S.filter (fun ρ ↦ ρ.re < 0), riemannZetaReciprocalZeroContribution x ρ).re| ≤
      _
  rw [← hsplit, Complex.add_re]
  have he :
    Real.log (2 * Real.pi) / x + (Real.log x - 1 - Real.eulerMascheroniConstant) +
          ((∑ ρ ∈ S.filter (fun ρ ↦ ρ.re < 0), riemannZetaReciprocalZeroContribution x ρ).re +
            (∑ ρ ∈ S.filter (fun ρ ↦ ¬ρ.re < 0), riemannZetaReciprocalZeroContribution x ρ).re) -
        (Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x) -
        (∑ ρ ∈ S.filter (fun ρ ↦ ρ.re < 0), riemannZetaReciprocalZeroContribution x ρ).re =
      (∑ ρ ∈ S.filter (fun ρ ↦ ¬ρ.re < 0), riemannZetaReciprocalZeroContribution x ρ).re := by
    ring
  rw [he]
  exact (Complex.abs_re_le_norm _).trans hb

/-- RH bounds the error in the full reciprocal zeta explicit formula by
`2 * RiemannXi.riemannZeroMass / sqrt x`. Both the contour ledger and the exact trivial-zero
partial sums are passed to their limits, so no sign of the error is discarded. -/
theorem abs_reciprocalWeightedMangoldtSum_error_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    |Arithmetic.reciprocalWeightedMangoldtSum x -
            (Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x) +
          riemannReciprocalTrivialZeroSeries x| ≤
      2 * RiemannXi.riemannZeroMass / Real.sqrt x := by
  have h2 : (1 : ℝ) < 2 := by norm_num only
  have hR :=
    Analysis.tendsto_residueLedger_of_normalized
      (tendsto_riemannZetaReciprocalContourResidueLedger_atTop hx h2 le_rfl)
  rw [← reciprocalWeightedMangoldtSum_eq_integral (lt_trans zero_lt_one hx) h2] at hR
  have hRe := (Complex.continuous_re.tendsto _).comp hR
  simp only [Complex.ofReal_re] at hRe
  have ht := tendsto_sum_reciprocalTrivialZeros_unifiedRectangle hx h2
  have hlim :=
    ((hRe.sub_const
            (Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x)).sub
        ht).abs
  have hb :=
    le_of_tendsto hlim
      (Filter.Eventually.of_forall (fun m ↦ abs_reciprocalResidueLedger_error_le hRH hx h2 m))
  simpa only [sub_neg_eq_add] using hb

/-- The reciprocal trivial-zero series agrees with the denominator convention
in the paper statement; this is only the inverse-power identity. -/
theorem riemannReciprocalTrivialZeroSeries_eq_paper (x : ℝ) :
    riemannReciprocalTrivialZeroSeries x =
      ∑' k : ℕ, 1 / (x ^ (2 * (k + 1) + 1) * (2 * ((k : ℝ) + 1)) * (2 * ((k : ℝ) + 1) + 1)) := by
  unfold riemannReciprocalTrivialZeroSeries
  apply tsum_congr
  intro k
  simp only [inv_pow, div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- RH bounds the logarithmic residue-ledger error after the exact trivial-zero sum
is removed. The derivative of the xi logarithmic derivative accounts for the constant error. -/
theorem abs_logResidueLedger_error_le (hRH : RiemannHypothesis) {x τ : ℝ} (hx : 1 < x) (hτ : 1 < τ)
    (m : ℕ) :
    |(riemannZetaLogContourResidueLedger x (unifiedRectangleLower m)
              (unifiedTauRectangleUpper τ m)).re -
          (x - Real.log (2 * Real.pi) * Real.log x - 1 + Real.pi ^ 2 / 24) -
          (∑
              ρ ∈
                (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                      (unifiedTauRectangleUpper τ m)).filter
                  (fun ρ ↦ ρ.re < 0),
              riemannZetaLogZeroContribution x ρ).re| ≤
      2 * RiemannXi.riemannZeroMass * (Real.sqrt x + 1) := by
  classical
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  let S := riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper τ m)
  let Sn := S.filter (fun ρ ↦ ¬ρ.re < 0)
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ ↦ ρ.re < 0) (riemannZetaLogZeroContribution x)
  have hb :=
    norm_sum_riemannZetaLogZeroContribution_le hRH hxpos Sn
      (fun ρ hρ ↦ (mem_riemannZetaZerosInAnyRectangle_iff.mp (Finset.mem_filter.mp hρ).1).2)
      (fun ρ hρ ↦ not_lt.mp (Finset.mem_filter.mp hρ).2)
  have hD := RiemannXi.norm_deriv_logDeriv_riemannXi_zero_le_two_mul_riemannZeroMass hRH
  have hbridge := congrArg Complex.re RiemannXi.deriv_logDeriv_riemannXi_zero_eq
  have hbridge' :
    (deriv (logDeriv RiemannXi.riemannXi) 0).re =
      -1 + Real.pi ^ 2 / 24 + RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re := by
    simpa only [Complex.add_re, Complex.neg_re, Complex.one_re, ← Complex.ofReal_pow,
      ← Complex.ofReal_ofNat 24, ← Complex.ofReal_div, Complex.ofReal_re] using hbridge
  have hre0 :
    (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero -
          Complex.log (2 * Real.pi) * Complex.log x).re =
      -RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
        Real.log (2 * Real.pi) * Real.log x := by
    rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul, ←
      Complex.ofReal_log (mul_nonneg (by norm_num only) Real.pi_pos.le), ←
      Complex.ofReal_log hxpos.le, ← Complex.ofReal_mul, Complex.sub_re, Complex.neg_re,
      Complex.ofReal_re]
  rw [riemannZetaLogContourResidueLedger_unifiedTau_eq hτ, riemannZetaLogResidueAtZero_eq hxpos,
    riemannZetaLogResidueAtOne_eq, Complex.add_re, Complex.add_re, hre0, Complex.ofReal_re]
  change
    |-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re - Real.log (2 * Real.pi) * Real.log x +
            x +
            (∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ).re -
          (x - Real.log (2 * Real.pi) * Real.log x - 1 + Real.pi ^ 2 / 24) -
          (∑ ρ ∈ S.filter (fun ρ ↦ ρ.re < 0), riemannZetaLogZeroContribution x ρ).re| ≤
      _
  rw [← hsplit, Complex.add_re]
  have he :
    -RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re - Real.log (2 * Real.pi) * Real.log x +
          x +
          ((∑ ρ ∈ S.filter (fun ρ ↦ ρ.re < 0), riemannZetaLogZeroContribution x ρ).re +
            (∑ ρ ∈ Sn, riemannZetaLogZeroContribution x ρ).re) -
        (x - Real.log (2 * Real.pi) * Real.log x - 1 + Real.pi ^ 2 / 24) -
        (∑ ρ ∈ S.filter (fun ρ ↦ ρ.re < 0), riemannZetaLogZeroContribution x ρ).re =
      ((∑ ρ ∈ Sn, riemannZetaLogZeroContribution x ρ) -
          deriv (logDeriv RiemannXi.riemannXi) 0).re := by
    rw [Complex.sub_re, hbridge']
    ring
  rw [he]
  exact
    (Complex.abs_re_le_norm _).trans
      ((norm_sub_le _ _).trans ((add_le_add hb hD).trans_eq (by ring)))

/-- RH bounds the logarithmic explicit-formula error after the full trivial-zero series
has been retained. The finite zero norm estimate passes to the weighted sum limit. -/
theorem abs_logWeightedMangoldtSum_error_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    |Arithmetic.logWeightedMangoldtSum x -
            (x - Real.log (2 * Real.pi) * Real.log x - 1 + Real.pi ^ 2 / 24) +
          riemannZetaLogTrivialZeroSeries x| ≤
      2 * RiemannXi.riemannZeroMass * (Real.sqrt x + 1) := by
  have h2 : (1 : ℝ) < 2 := by norm_num only
  have hR :=
    Analysis.tendsto_residueLedger_of_normalized
      (tendsto_riemannZetaLogContourResidueLedger_atTop hx h2 le_rfl)
  rw [← logWeightedMangoldtSum_eq_integral (lt_trans zero_lt_one hx) h2] at hR
  have hRe := (Complex.continuous_re.tendsto _).comp hR
  simp only [Complex.ofReal_re] at hRe
  have ht := tendsto_sum_logTrivialZeros_unifiedRectangle hx h2
  have hlim :=
    ((hRe.sub_const (x - Real.log (2 * Real.pi) * Real.log x - 1 + Real.pi ^ 2 / 24)).sub ht).abs
  have hb :=
    le_of_tendsto hlim
      (Filter.Eventually.of_forall (fun m ↦ abs_logResidueLedger_error_le hRH hx h2 m))
  simpa only [sub_neg_eq_add] using hb

/-- For `x > 1`, the paper's logarithmic correction series is the Basel constant
minus the logarithmic trivial-zero tail. Both component series are summable. -/
theorem logTrivialZeroSeries_paper_eq {x : ℝ} (hx : 1 < x) :
    (∑' k : ℕ, (1 - 1 / x ^ (2 * (k + 1))) / (4 * ((k : ℝ) + 1) ^ 2)) =
      Real.pi ^ 2 / 24 - riemannZetaLogTrivialZeroSeries x := by
  have hb0 : Summable (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
    have h := hasSum_zeta_two.summable.comp_injective Nat.succ_injective
    change Summable (fun k : ℕ ↦ (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hb := hb0.mul_left (1 / 4 : ℝ)
  have hs := summable_logTrivialZeroTerm hx
  have he :
    (∑' k : ℕ, (1 - 1 / x ^ (2 * (k + 1))) / (4 * ((k : ℝ) + 1) ^ 2)) =
      ∑' k : ℕ,
        ((1 / 4 : ℝ) * (1 / ((k : ℝ) + 1) ^ 2) -
          x⁻¹ ^ (2 * (k + 1)) / (4 * ((k : ℝ) + 1) ^ 2)) := by
    apply tsum_congr
    intro k
    simp only [inv_pow, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [he, hb.tsum_sub hs, tsum_mul_left, Analysis.tsum_shifted_basel_eq]
  unfold riemannZetaLogTrivialZeroSeries
  ring

/-- Under RH and x > 1, the unsigned reciprocal Mangoldt sum is bounded by
log x-1-gamma+log(2 pi)/x+2 RiemannXi.riemannZeroMass/sqrt x.
Discard the nonnegative trivial-zero tail
from the exact error estimate. This removes the finite reciprocal sum from L-value bounds. -/
theorem reciprocalWeightedMangoldtSum_le_explicit (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    Arithmetic.reciprocalWeightedMangoldtSum x ≤
      Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x +
        2 * RiemannXi.riemannZeroMass / Real.sqrt x := by
  have h := (abs_le.mp (abs_reciprocalWeightedMangoldtSum_error_le hRH hx)).2
  have ht : 0 ≤ riemannReciprocalTrivialZeroSeries x := by
    apply tsum_nonneg
    intro k
    exact
      div_nonneg (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans hx).le) _)
        (mul_nonneg (by positivity) (by positivity))
  linarith only [h, ht]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
