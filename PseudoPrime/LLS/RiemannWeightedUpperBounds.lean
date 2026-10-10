/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannExplicitFormula
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CompositePrimePowers
public import PseudoPrime.Analysis.NumericalLogBounds

/-! # Upper bounds for logarithmically weighted Mangoldt sums

The Riemann explicit formula and a rational zero-mass certificate bound the
arithmetic sum at root cutoffs used in the coset comparison.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH and `x > 1`, retain the logarithmic and constant corrections in the
upper bound for the logarithmically weighted Mangoldt sum.
Discard only the nonnegative trivial-zero tail and bound the zero mass by `1/40`.
The negative corrections sharpen the odd prime-power estimates at small cutoffs. -/
theorem logWeightedMangoldtSum_le_explicit (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x ≤
      x + Real.sqrt x / 20 - Real.log (2 * Real.pi) * Real.log x - 19 / 20 + Real.pi ^ 2 / 24 := by
  have he := (abs_le.mp (abs_logWeightedMangoldtSum_error_le hRH hx)).2
  have ht : 0 ≤ AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries x := by
    apply tsum_nonneg
    intro k
    exact
      div_nonneg (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans hx).le) _)
        (mul_nonneg (by norm_num only) (sq_nonneg _))
  have hm :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth
      (add_nonneg (Real.sqrt_nonneg x) zero_le_one)
  nlinarith only [he, ht, hm]

/-- Under RH and `x > 1`, the corrected Mangoldt upper bound has rational savings
`1837/1000 * log x + 269/500`. Bound `log(2 pi)` below and `pi²` above
in the explicit correction estimate. This gives certificate arithmetic rational coefficients. -/
theorem logWeightedMangoldtSum_le_rational_corrected (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 1 < x) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x ≤
      x + Real.sqrt x / 20 - (1837 / 1000 : ℝ) * Real.log x - 269 / 500 := by
  have hs := logWeightedMangoldtSum_le_explicit hRH hx
  have hl := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_gt.le (Real.log_pos hx).le
  have hc : (269 / 500 : ℝ) ≤ 19 / 20 - Real.pi ^ 2 / 24 := by
    nlinarith only [Real.pi_lt_d4, Real.pi_pos, sq_nonneg (Real.pi - 3.1415927)]
  nlinarith only [hs, hl, hc]

/-- Under RH and `x > 1`, the corrected Mangoldt upper bound saves
`183/100 * log x + 1/2`. Weaken the sharper rational savings using positive `log x`.
These simpler coefficients are the first small-modulus analytic certificate criterion. -/
theorem logWeightedMangoldtSum_le_simple_corrected (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x ≤
      x + Real.sqrt x / 20 - (183 / 100 : ℝ) * Real.log x - 1 / 2 := by
  have hs := logWeightedMangoldtSum_le_rational_corrected hRH hx
  nlinarith only [hs, Real.log_pos hx]

/-- Under RH, for a real cutoff greater than one, the logarithmically weighted
Mangoldt sum is at most `x + sqrt x / 20`.
Discard the nonnegative trivial-zero series and logarithmic correction, and bound
the zero contribution with mass `1/40`. The remaining constant term is negative.
This bounds the prime-power slices in the coset argument. -/
theorem logWeightedMangoldtSum_le_add_sqrt_twentieth (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 1 < x) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x ≤ x + Real.sqrt x / 20 := by
  have he := (abs_le.mp (abs_logWeightedMangoldtSum_error_le hRH hx)).2
  have ht : 0 ≤ AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries x := by
    apply tsum_nonneg
    intro k
    exact
      div_nonneg (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans hx).le) _)
        (mul_nonneg (by norm_num only) (sq_nonneg _))
  have hm :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth
      (add_nonneg (Real.sqrt_nonneg x) zero_le_one)
  have hl :=
    mul_nonneg (Real.log_nonneg (by nlinarith only [Real.pi_gt_three] : 1 ≤ 2 * Real.pi))
      (Real.log_pos hx).le
  nlinarith only [he, ht, hm, hl, Real.pi_lt_four, Real.pi_pos, sq_nonneg (Real.pi - 4)]

/-- Under RH and `x > 1`, the composite prime-power contribution is bounded by
root-cutoff sums retaining the negative logarithmic and constant corrections.
Apply the corrected Mangoldt bound at each positive root cutoff.
This preserves the savings needed for residue comparisons at smaller moduli. -/
theorem compositePrimePowerLogWeightedSum_le_corrected_root_sums (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 1 < x) :
    AnalyticNumberTheory.Arithmetic.compositePrimePowerLogWeightedSum x ≤
      ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊,
        (k : ℝ) *
          (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20 -
              Real.log (2 * Real.pi) * Real.log (x ^ ((1 : ℝ) / k)) -
              19 / 20 +
            Real.pi ^ 2 / 24) := by
  apply (AnalyticNumberTheory.Arithmetic.compositePrimePowerLogWeightedSum_le_root_sums hx).trans
  apply Finset.sum_le_sum
  intro k hk
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast lt_of_lt_of_le (by norm_num only : 0 < 2) (Finset.mem_Icc.mp hk).1
  exact
    mul_le_mul_of_nonneg_left
      (logWeightedMangoldtSum_le_explicit hRH (Real.one_lt_rpow hx (div_pos zero_lt_one hkpos)))
      hkpos.le

/-- Under RH, for `x > 1`, the composite logarithmic contribution is bounded by a
finite sum of explicit root-cutoff expressions. The prime-power decomposition
and the weighted Mangoldt upper bound give each exponent's contribution.
This reduces the remaining coset upper bound to inequalities in real powers. -/
theorem compositePrimePowerLogWeightedSum_le_explicit_root_sums (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 1 < x) :
    AnalyticNumberTheory.Arithmetic.compositePrimePowerLogWeightedSum x ≤
      ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊,
        (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20) := by
  apply (AnalyticNumberTheory.Arithmetic.compositePrimePowerLogWeightedSum_le_root_sums hx).trans
  apply Finset.sum_le_sum
  intro k hk
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast lt_of_lt_of_le (by norm_num only : 0 < 2) (Finset.mem_Icc.mp hk).1
  exact
    mul_le_mul_of_nonneg_left
      (logWeightedMangoldtSum_le_add_sqrt_twentieth hRH
        (Real.one_lt_rpow hx (div_pos zero_lt_one hkpos)))
      hkpos.le

end PseudoPrime.LLS
