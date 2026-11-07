/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.WeightedExplicitBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences

/-! # Trivial-zero tail comparison for Chebyshev bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For ordered real arguments above one, the logarithmic trivial-zero tail
is antitone. Compare each nonnegative inverse-power term and use convergence
at both arguments. This retains the tail sign in the Chebyshev secant bound. -/
theorem log_trivial_tail_antitone {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries b ≤
      AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries a := by
  unfold AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries
  apply
    Summable.tsum_le_tsum _
      (AnalyticNumberTheory.RiemannZeta.summable_logTrivialZeroTerm (ha.trans_le hab))
      (AnalyticNumberTheory.RiemannZeta.summable_logTrivialZeroTerm ha)
  intro k
  apply div_le_div_of_nonneg_right _ (mul_nonneg (by norm_num only) (sq_nonneg _))
  apply pow_le_pow_left₀
  · exact inv_nonneg.mpr (zero_lt_one.trans (ha.trans_le hab)).le
  · exact (inv_le_inv₀ (zero_lt_one.trans (ha.trans_le hab)) (zero_lt_one.trans ha)).2 hab

/-- Under RH, two ordered cutoffs above one yield a one-sided Chebyshev
secant bound retaining the explicit-formula constant and the sign of the
trivial-zero tail. The shared constant cancels before estimating the two zero
contributions. This is the analytic input for the sharper relative bound. -/
theorem psi_log_secant_lower (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    b - a - Real.log (2 * Real.pi) * Real.log (b / a) -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt a + Real.sqrt b + 2) ≤
      Chebyshev.psi b * Real.log (b / a) := by
  have hA :=
    (abs_le.mp (AnalyticNumberTheory.RiemannZeta.abs_logWeightedMangoldtSum_error_le hRH ha)).2
  have hB :=
    (abs_le.mp
        (AnalyticNumberTheory.RiemannZeta.abs_logWeightedMangoldtSum_error_le hRH (ha.trans hab))).1
  have ht := log_trivial_tail_antitone ha hab.le
  have hs :=
    (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum_difference_bounds (zero_lt_one.trans ha)
        hab.le).2
  rw [Real.log_div (zero_lt_one.trans (ha.trans hab)).ne' (zero_lt_one.trans ha).ne'] at hs ⊢
  nlinarith only [hA, hB, ht, hs]

/-- Under RH, dividing the positive logarithmic secant yields a direct lower
bound for `psi` at the upper endpoint. This preserves the explicit zero mass
and is ready for rational control of a relative-width cutoff. -/
theorem psi_lower_log_secant (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    (b - a) / Real.log (b / a) - Real.log (2 * Real.pi) -
        (2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt a + Real.sqrt b + 2)) /
          Real.log (b / a) ≤
      Chebyshev.psi b := by
  have hl : 0 < Real.log (b / a) := Real.log_pos ((one_lt_div (zero_lt_one.trans ha)).2 hab)
  have h := psi_log_secant_lower hRH ha hab
  have he :
    ((b - a) / Real.log (b / a) - Real.log (2 * Real.pi) -
          (2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt a + Real.sqrt b + 2)) /
            Real.log (b / a)) *
        Real.log (b / a) =
      b - a - Real.log (2 * Real.pi) * Real.log (b / a) -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt a + Real.sqrt b + 2) := by
    rw [sub_mul, sub_mul, div_mul_cancel₀ _ hl.ne', div_mul_cancel₀ _ hl.ne']
  exact (mul_le_mul_iff_left₀ hl).mp (he ▸ h)

end PseudoPrime.PrimeTestBounds.MillerRabin
