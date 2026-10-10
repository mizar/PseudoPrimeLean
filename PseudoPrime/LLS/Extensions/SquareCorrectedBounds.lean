/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.PrimePowerComparison
public import PseudoPrime.LLS.LogLValueComparison
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtLogSquareSeries

/-! Square correction and zeta-at-two factors in general L-value lower bounds. -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For a cutoff above one, the truncated Mangoldt majorant is the logarithmic weighted
sum plus the reciprocal weighted sum divided by the logarithm of the cutoff. Sum the
pointwise weight splitting identity. This identifies the arithmetic term in the value bounds. -/
theorem truncatedMangoldtMajorant_eq_log_sums {x : ℝ} (hx : 1 < x) :
    AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x =
      PaperStatements.logLValueSum x +
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x / Real.log x := by
  unfold AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant PaperStatements.logLValueSum
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact PaperStatements.comparison_weight_split hx (Finset.mem_Ioc.mp hn).1

/-- For a cutoff above one, the alternating prime-power sum is the negative truncated
majorant plus `log (pi^2 / 6)` minus the square correction loss. Reindex even exponents
as squares and use the logarithmic zeta series. This retains the lower-value Euler constant. -/
theorem alternatingPrimePowerSum_eq_majorant_squareLoss {x : ℝ} (hx : 1 < x) :
    PaperStatements.alternatingPrimePowerSum x =
      -AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x + Real.log (Real.pi ^ 2 / 6) -
        AnalyticNumberTheory.Arithmetic.squareMangoldtCorrectionLoss x := by
  rw [PaperStatements.alternatingPrimePowerSum_eq_log_sums hx,
    AnalyticNumberTheory.Arithmetic.two_mul_squareMangoldtCorrection_eq,
    truncatedMangoldtMajorant_eq_log_sums hx]
  ring

/-- For admissible RH data and cutoff at least one hundred, the negative logarithm of the
L-value norm is bounded using the truncated majorant minus `log (pi^2 / 6)`, with square
loss at most `3 / (2 sqrt x)`. Insert the exact alternating decomposition and the existing
tail bound in the general root comparison. This supplies the corrected logarithmic lower bound. -/
theorem neg_log_norm_L_one_le_square_corrected (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 100 ≤ x) :
    -Real.log ‖f.L 1‖ ≤
      (f.degree : ℝ) *
          (AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x -
              Real.log (Real.pi ^ 2 / 6) +
            3 / (2 * Real.sqrt x)) +
        |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) +
        f.truncatedConductorErrorBound x := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 100) hx
  have h := neg_log_norm_L_one_le_alternating f hf hRH hx
  rw [alternatingPrimePowerSum_eq_majorant_squareLoss hx1] at h
  have hs :=
    mul_le_mul_of_nonneg_left (AnalyticNumberTheory.Arithmetic.squareMangoldtCorrectionLoss_le x hx)
      (Nat.cast_nonneg f.degree)
  linarith only [h, hs]

/-- For admissible RH data and cutoff at least one hundred, the reciprocal L-value norm
has an upper bound with explicit factor `(6 / pi^2)^degree`. Exponentiate the corrected
negative-logarithm bound and extract the zeta-at-two constant. The remaining arithmetic
majorant and truncation error are kept explicit for the final conductor asymptotics. -/
theorem reciprocal_norm_L_one_le_square_corrected (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 100 ≤ x) :
    1 / ‖f.L 1‖ ≤
      (6 / Real.pi ^ 2) ^ f.degree *
        Real.exp
          ((f.degree : ℝ) *
              (AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x +
                3 / (2 * Real.sqrt x)) +
            |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) +
            f.truncatedConductorErrorBound x) := by
  have h := neg_log_norm_L_one_le_square_corrected f hf hRH hx
  have hlog :
    Real.log (1 / ‖f.L 1‖) ≤
      (f.degree : ℝ) *
          (AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x -
              Real.log (Real.pi ^ 2 / 6) +
            3 / (2 * Real.sqrt x)) +
        |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) +
        f.truncatedConductorErrorBound x := by
    rw [one_div, Real.log_inv]
    exact h
  have he := (Real.le_exp_log (1 / ‖f.L 1‖)).trans (Real.exp_le_exp.mpr hlog)
  have hp : 0 < Real.pi ^ 2 / 6 := div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num only)
  have hex :
    Real.exp (-(f.degree : ℝ) * Real.log (Real.pi ^ 2 / 6)) = (6 / Real.pi ^ 2) ^ f.degree := by
    rw [neg_mul, ← mul_neg, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hp, inv_div]
  have harg :
    (f.degree : ℝ) *
          (AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x -
              Real.log (Real.pi ^ 2 / 6) +
            3 / (2 * Real.sqrt x)) +
        |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) +
        f.truncatedConductorErrorBound x =
      -(f.degree : ℝ) * Real.log (Real.pi ^ 2 / 6) +
        ((f.degree : ℝ) *
            (AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x + 3 / (2 * Real.sqrt x)) +
          |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) +
          f.truncatedConductorErrorBound x) := by
    ring
  rw [harg, Real.exp_add, hex] at he
  exact he

end PseudoPrime.LLS.Extensions.GeneralLFunction
