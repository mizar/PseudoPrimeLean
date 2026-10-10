/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.ReciprocalFormulaDerivation
public import PseudoPrime.LLS.Extensions.ArithmeticCoefficients
public import Mathlib.NumberTheory.Chebyshev

/-!
# Zero mass and the unweighted reciprocal arithmetic sum

The exact reciprocal formula bounds the smoothed sum. Chebyshev's bound controls
its difference from the unweighted sum. Boundedness of the latter gives the remainder
required by the fixed-function statement `lls_sumzeros`.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For admissible RH data and `x > 1`, the smoothed reciprocal sum equals the ordinary
endpoint derivative times `-(1 - 1/x)`, minus the centered zero contribution and the gamma
residue sum. Equate the arithmetic and zero evaluations of the completed Mellin integral
and use the completion product rule at one. This bounds the arithmetic sum for fixed data. -/
theorem reciprocalWeightedSum_eq_zero_sub_gamma (f : GeneralLFunction)
    (hf : f.IsAdmissible) (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    f.reciprocalWeightedSum x =
      -logDeriv f.L 1 * (1 - (x : ℂ)⁻¹) -
        ((f.zeroMass : ℂ) / (x : ℂ) - f.reciprocalZeroSum x) - f.reciprocalGammaSum x := by
  have ha := normalized_integral_completedReciprocal_eq_arithmetic_sub f hf hRH zero_lt_one hx
  have hz := normalized_integral_completedReciprocalMellin_eq f hf hRH zero_lt_one hx
  have he := ha.symm.trans hz
  rw [logDeriv_completed_eq_completionFactor_add f hf (by norm_num only [Complex.one_re])
    (completed_ne_zero_of_re_ne_half hRH (by norm_num only [Complex.one_re]))] at he
  exact ((sub_eq_iff_eq_add).mp he).trans (by
    ring
    )

/-- For `x > 0`, the unweighted reciprocal sum minus its smoothed version is `1/x` times
the finite Mangoldt coefficient sum. Subtract the weights termwise and cancel the positive
natural index. This reduces the smoothing error to a summatory Mangoldt bound. -/
theorem reciprocalSum_sub_weighted_eq (f : GeneralLFunction) {x : ℝ} (hx : 0 < x) :
    f.reciprocalSum x - f.reciprocalWeightedSum x =
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f.mangoldtCoefficient n * (ArithmeticFunction.vonMangoldt n : ℂ)) /
        (x : ℂ) := by
  unfold reciprocalSum reciprocalWeightedSum
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1).ne'
  have hnC : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn0
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_natCast]
  field_simp (disch := simp only [hnC, hxC, ne_eq, not_false_eq_true])
  ring

/-- For admissible data and `x > 0`, the smoothing error has norm at most
`degree * (log 4 + 4)`. Ramanujan bounds control the coefficient sum and Chebyshev's
linear bound controls the sum of `Λ(n)`. This makes smoothing removal uniformly bounded. -/
theorem norm_reciprocalSum_sub_weighted_le (f : GeneralLFunction) (hf : f.IsAdmissible)
    {x : ℝ} (hx : 0 < x) :
    ‖f.reciprocalSum x - f.reciprocalWeightedSum x‖ ≤ f.degree * (Real.log 4 + 4) := by
  rw [reciprocalSum_sub_weighted_eq f hx, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx]
  have hb := norm_finiteWeightedSum_le f hf (Finset.Ioc 0 ⌊x⌋₊) ArithmeticFunction.vonMangoldt
  simp only [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] at hb
  have hc := Chebyshev.psi_le_const_mul_self hx.le
  change (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n) ≤ (Real.log 4 + 4) * x at hc
  apply (div_le_iff₀ hx).mpr
  exact hb.trans ((mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg f.degree)).trans_eq (by
    ring
    ))

/-- The totalized completed-zero mass is nonnegative for any data. Each analytic multiplicity
and inverse-square norm is nonnegative; take their total sum. This supplies the sign
conditions in fixed-function reciprocal bounds. -/
private theorem zeroMass_nonneg (f : GeneralLFunction) : 0 ≤ f.zeroMass := by
  exact tsum_nonneg (fun ρ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- For `x > 1`, the complex number `1 - 1/x` has norm at most one. Rewrite it as a real
coercion in the interval `[0,1]`. This bounds the ordinary endpoint multiplier. -/
private theorem norm_one_sub_inv_le_one {x : ℝ} (hx : 1 < x) : ‖1 - (x : ℂ)⁻¹‖ ≤ 1 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hi : x⁻¹ ≤ 1 := by
    simpa only [one_div, div_one] using (div_le_div_of_nonneg_left zero_le_one zero_lt_one hx.le)
  have he : 1 - (x : ℂ)⁻¹ = ((1 - x⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hi)]
  exact sub_le_self 1 (inv_nonneg.mpr hx0.le)

/-- For admissible RH data and `x > 1`, the reciprocal zero sum's norm is at most the zero
mass. Zero mass is summable and `sqrt x ≥ 1`, so its established `mass/sqrt x` bound applies.
This gives a fixed bound for the completed-zero contribution. -/
private theorem norm_reciprocalZeroSum_le_mass (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) : ‖f.reciprocalZeroSum x‖ ≤ f.zeroMass := by
  have hs : 1 ≤ Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx.le
  exact
    (norm_reciprocalZeroSum_le f hRH (summable_zeroMassTerm_of_admissible f hf hRH)
          (zero_lt_one.trans hx)).trans
      ((div_le_div_of_nonneg_left (zeroMass_nonneg f) zero_lt_one hs).trans_eq (div_one _))

/-- For admissible data and `x > 1`, the gamma residue sum is bounded by its fixed gamma
constant. The logarithmic inequality `log x ≤ x - 1` makes `(log x + 1)/x ≤ 1`.
This gives a cutoff-independent bound for the archimedean contribution. -/
private theorem norm_reciprocalGammaSum_le_bound (f : GeneralLFunction) (hf : f.IsAdmissible)
    {x : ℝ} (hx : 1 < x) : ‖f.reciprocalGammaSum x‖ ≤ f.reciprocalGammaBound := by
  have hr : (Real.log x + 1) / x ≤ 1 := by
    apply (div_le_one (zero_lt_one.trans hx)).mpr
    linarith only [Real.log_le_sub_one_of_pos (zero_lt_one.trans hx)]
  exact
    (norm_reciprocalGammaSum_le f hf hx).trans
      (mul_le_of_le_one_right (reciprocalGammaBound_nonneg f) hr)

/-- For fixed admissible RH data and `x > 1`, bound the smoothed reciprocal sum by the
ordinary endpoint norm, twice the zero mass and the fixed gamma constant. Use the exact
zero/gamma formula and the triangle inequality. This controls the arithmetic term after
removing its dependence on the cutoff. -/
theorem norm_reciprocalWeightedSum_le (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖f.reciprocalWeightedSum x‖ ≤ ‖logDeriv f.L 1‖ + 2 * f.zeroMass + f.reciprocalGammaBound := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hA : ‖-logDeriv f.L 1 * (1 - (x : ℂ)⁻¹)‖ ≤ ‖logDeriv f.L 1‖ := by
    rw [norm_mul, norm_neg]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_one_sub_inv_le_one hx)
  have hM : ‖(f.zeroMass : ℂ) / (x : ℂ)‖ ≤ f.zeroMass := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (zeroMass_nonneg f),
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    exact (div_le_div_of_nonneg_left (zeroMass_nonneg f) zero_lt_one hx.le).trans_eq (div_one _)
  have hZ := norm_reciprocalZeroSum_le_mass f hf hRH hx
  have hG := norm_reciprocalGammaSum_le_bound f hf hx
  have hB := norm_sub_le ((f.zeroMass : ℂ) / (x : ℂ)) (f.reciprocalZeroSum x)
  have hC :=
    norm_sub_le (-logDeriv f.L 1 * (1 - (x : ℂ)⁻¹))
      ((f.zeroMass : ℂ) / (x : ℂ) - f.reciprocalZeroSum x)
  have hD :=
    norm_sub_le
      (-logDeriv f.L 1 * (1 - (x : ℂ)⁻¹) - ((f.zeroMass : ℂ) / (x : ℂ) - f.reciprocalZeroSum x))
      (f.reciprocalGammaSum x)
  rw [reciprocalWeightedSum_eq_zero_sub_gamma f hf hRH hx]
  linarith only [hA, hM, hZ, hG, hB, hC, hD]

/-- For fixed admissible RH data and `x > 1`, the unweighted reciprocal sum is bounded by
the smoothed-sum constant plus `degree * (log 4 + 4)`. Add the uniformly bounded smoothing
error to the completed zero/gamma estimate. This supplies the fixed-function zero-mass error. -/
theorem norm_reciprocalSum_le (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖f.reciprocalSum x‖ ≤
      ‖logDeriv f.L 1‖ + 2 * f.zeroMass + f.reciprocalGammaBound + f.degree * (Real.log 4 + 4) := by
  have he :
    f.reciprocalSum x =
      f.reciprocalWeightedSum x + (f.reciprocalSum x - f.reciprocalWeightedSum x) := by
    ring
  calc
    _ = ‖f.reciprocalWeightedSum x + (f.reciprocalSum x - f.reciprocalWeightedSum x)‖ := by
      rw [← he]
    _ ≤ ‖f.reciprocalWeightedSum x‖ + ‖f.reciprocalSum x - f.reciprocalWeightedSum x‖ :=
      norm_add_le _ _
    _ ≤ _ :=
      add_le_add (norm_reciprocalWeightedSum_le f hf hRH hx)
        (norm_reciprocalSum_sub_weighted_le f hf (zero_lt_one.trans hx))

/-- The real error `zeroMass - log analyticConductor + 2 * Re(reciprocalSum x)`.
It gives the zero-mass identity exactly by rearrangement. For admissible RH data, its
cutoff-independent bound proves the asymptotic error required in `lls_sumzeros`. -/
noncomputable def zeroMassReciprocalRemainder (f : GeneralLFunction) (x : ℝ) : ℝ :=
  f.zeroMass - Real.log f.analyticConductor + 2 * (f.reciprocalSum x).re

/-- The fixed constant bounding the zero-mass remainder: `abs(mass - log conductor)` plus
twice the bound on the unweighted reciprocal sum. It may depend on the ordinary endpoint,
zero mass and gamma shifts. The fixed-function Big-O statement allows this dependence. -/
noncomputable def zeroMassReciprocalBound (f : GeneralLFunction) : ℝ :=
  |f.zeroMass - Real.log f.analyticConductor| +
    2 * (‖logDeriv f.L 1‖ + 2 * f.zeroMass + f.reciprocalGammaBound + f.degree * (Real.log 4 + 4))

/-- For fixed admissible RH data and `x > 1`, the zero-mass remainder norm is at most its
fixed constant. Bound the real reciprocal sum by its complex norm and use the finite-sum
estimate. This supplies boundedness before comparison with the asymptotic scale. -/
theorem norm_zeroMassReciprocalRemainder_le (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖f.zeroMassReciprocalRemainder x‖ ≤ f.zeroMassReciprocalBound := by
  have hb := norm_reciprocalSum_le f hf hRH hx
  have hr := Complex.abs_re_le_norm (f.reciprocalSum x)
  unfold zeroMassReciprocalRemainder zeroMassReciprocalBound
  have hn := norm_add_le (f.zeroMass - Real.log f.analyticConductor) (2 * (f.reciprocalSum x).re)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num only)] at hn
  rw [Real.norm_eq_abs]
  linarith only [hn, hr, hb]

/-- For each fixed admissible RH function, its zero-mass remainder is Big-O of
`degree + log analyticConductor / sqrt x` at infinity. The remainder is bounded; positive
degree makes the comparison scale eventually at least one half. This proves the complete
remainder condition in `lls_sumzeros`, without asserting a constant uniform over functions. -/
theorem isBigO_zeroMassReciprocalRemainder (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) :
    Asymptotics.IsBigO Filter.atTop f.zeroMassReciprocalRemainder
      (fun x : ℝ ↦ f.degree + Real.log f.analyticConductor / Real.sqrt x) := by
  have hB : 0 ≤ f.zeroMassReciprocalBound :=
    (norm_nonneg (f.zeroMassReciprocalRemainder 2)).trans
      (norm_zeroMassReciprocalRemainder_le f hf hRH (by norm_num only))
  have hd : (1 : ℝ) ≤ f.degree := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hf.1.ne')
  apply Asymptotics.IsBigO.of_bound (2 * f.zeroMassReciprocalBound)
  filter_upwards [Real.tendsto_sqrt_atTop.eventually
      (Filter.eventually_ge_atTop (2 * |Real.log f.analyticConductor| + 2)),
    Filter.eventually_gt_atTop (1 : ℝ)] with x hs hx
  have hpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr (zero_lt_one.trans hx)
  have hl : -(1 / 2 : ℝ) ≤ Real.log f.analyticConductor / Real.sqrt x := by
    apply (le_div_iff₀ hpos).mpr
    linarith only [hs, neg_abs_le (Real.log f.analyticConductor)]
  have hn : (1 / 2 : ℝ) ≤ f.degree + Real.log f.analyticConductor / Real.sqrt x := by
    linarith only [hd, hl]
  have hnorm :
    ‖(f.degree : ℝ) + Real.log f.analyticConductor / Real.sqrt x‖ =
      f.degree + Real.log f.analyticConductor / Real.sqrt x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith only [hn])]
  rw [hnorm]
  have hb := norm_zeroMassReciprocalRemainder_le f hf hRH hx
  nlinarith only [hb, hB, mul_nonneg hB (sub_nonneg.mpr hn)]

/-- For admissible RH data and `x > 1`, the zero-mass remainder splits into the gamma
endpoint minus the logarithmic conductor, an endpoint correction divided by `x`, the
reciprocal zero and gamma sums, and the smoothing error. Take real parts of the exact
reciprocal formula and use the ordinary endpoint identity. This isolates the additional
estimates needed for a remainder bound uniform over a family of L-functions. -/
theorem zeroMassReciprocalRemainder_eq_contributions (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    f.zeroMassReciprocalRemainder x =
      2 * f.gammaLogDerivativeAtOne - Real.log f.analyticConductor -
              (2 * f.gammaLogDerivativeAtOne + f.zeroMass) / x +
            2 * (f.reciprocalZeroSum x).re -
          2 * (f.reciprocalGammaSum x).re +
        2 * (f.reciprocalSum x - f.reciprocalWeightedSum x).re := by
  have he := congrArg Complex.re (reciprocalWeightedSum_eq_zero_sub_gamma f hf hRH hx)
  have hk : 1 - (x : ℂ)⁻¹ = ((1 - x⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv]
  rw [hk] at he
  simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at he
  have hd : ((f.zeroMass : ℂ) / (x : ℂ)).re = f.zeroMass / x := by
    rw [← Complex.ofReal_div, Complex.ofReal_re]
  rw [hd, re_logDeriv_ordinary_one_eq_half_zeroMass_sub_gamma f hf hRH] at he
  unfold zeroMassReciprocalRemainder
  rw [Complex.sub_re, he]
  ring

end PseudoPrime.LLS.Extensions.GeneralLFunction
