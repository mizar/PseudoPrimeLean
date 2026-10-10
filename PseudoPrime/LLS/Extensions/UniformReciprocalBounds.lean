/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.ZeroMassReciprocalFormula
public import PseudoPrime.LLS.Extensions.GammaConductorComparison

/-!
# Reciprocal remainder bounds with uniform gamma terms

Uniform gamma residue and digamma estimates bound the reciprocal errors by conductor and degree.
At a fixed cutoff, absorb the zero-mass terms to obtain a conductor bound for the mass itself.
This gives uniform control on fixed-degree families and the error scale in the zero-mass formula.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For admissible RH data and cutoff greater than one, the reciprocal remainder is
bounded by its endpoint correction divided by the cutoff plus a degree-dependent universal
gamma-residue bound. Insert the exact residue formula and take norms. This removes all
dependence on individual gamma shifts from the non-endpoint part of the error. -/
theorem norm_reciprocalRemainder_le_uniform_gamma (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖f.reciprocalRemainder x‖ ≤
      |f.gammaLogDerivativeAtOne + f.zeroMass| / x +
        (f.degree : ℝ) *
          ((Real.log x + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) / x) := by
  rw [reciprocalRemainder_eq_gammaResidues f hf hRH hx]
  have hg :=
    (Complex.abs_re_le_norm (f.reciprocalGammaSum x)).trans
      (norm_reciprocalGammaSum_le_uniform f hf hx)
  have he :
    ‖(f.gammaLogDerivativeAtOne + f.zeroMass) / x‖ =
      |f.gammaLogDerivativeAtOne + f.zeroMass| / x := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (zero_lt_one.trans hx)]
  have hb := norm_add_le ((f.gammaLogDerivativeAtOne + f.zeroMass) / x) (f.reciprocalGammaSum x).re
  simp only [he, Real.norm_eq_abs] at hb
  exact hb.trans (add_le_add (le_refl _) hg)

/-- For admissible RH data and cutoff greater than one, the zero-mass remainder is
bounded by the finite digamma-error sum, an endpoint correction,
the zero mass divided by the square root, a universal degree-dependent gamma term, and
Chebyshev's smoothing error. Apply the exact contribution decomposition and the proved
bounds to each term. This isolates the remaining endpoint estimates for uniform families. -/
theorem norm_zeroMassReciprocalRemainder_le_explicit (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖f.zeroMassReciprocalRemainder x‖ ≤
      |∑ j : Fin f.degree,
            ((logDeriv Complex.Gamma ((1 + f.shift j) / 2)).re - Real.log ‖(1 + f.shift j) / 2‖)| +
        |2 * f.gammaLogDerivativeAtOne + f.zeroMass| / x +
        2 * (f.zeroMass / Real.sqrt x) +
        2 *
          ((f.degree : ℝ) *
            ((Real.log x + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) / x)) +
        2 * ((f.degree : ℝ) * (Real.log 4 + 4)) := by
  rw [← twice_gammaLogDerivativeAtOne_sub_log_conductor f hf]
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hg :=
    (Complex.abs_re_le_norm (f.reciprocalGammaSum x)).trans
      (norm_reciprocalGammaSum_le_uniform f hf hx)
  have hz :=
    (Complex.abs_re_le_norm (f.reciprocalZeroSum x)).trans
      (norm_reciprocalZeroSum_le f hRH (summable_zeroMassTerm_of_admissible f hf hRH) hx0)
  have hs :=
    (Complex.abs_re_le_norm (f.reciprocalSum x - f.reciprocalWeightedSum x)).trans
      (norm_reciprocalSum_sub_weighted_le f hf hx0)
  have he :
    |(2 * f.gammaLogDerivativeAtOne + f.zeroMass) / x| =
      |2 * f.gammaLogDerivativeAtOne + f.zeroMass| / x := by
    rw [abs_div, abs_of_pos hx0]
  rw [zeroMassReciprocalRemainder_eq_contributions f hf hRH hx, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;>
    linarith only [(abs_le.mp hg).1, (abs_le.mp hg).2, (abs_le.mp hz).1, (abs_le.mp hz).2,
      (abs_le.mp hs).1, (abs_le.mp hs).2,
      le_abs_self (2 * f.gammaLogDerivativeAtOne - Real.log f.analyticConductor),
      neg_le_abs (2 * f.gammaLogDerivativeAtOne - Real.log f.analyticConductor),
      le_abs_self ((2 * f.gammaLogDerivativeAtOne + f.zeroMass) / x),
      neg_le_abs ((2 * f.gammaLogDerivativeAtOne + f.zeroMass) / x), he]

/-- For admissible data, the gamma endpoint plus zero mass is bounded by the absolute
logarithmic conductor, the degree times the universal digamma error, and the zero mass.
Insert the conductor comparison and use nonnegativity of zero mass and the triangle
inequality. This controls the endpoint divided by the cutoff in the reciprocal remainder. -/
theorem abs_twice_gammaLogDerivativeAtOne_add_zeroMass_le (f : GeneralLFunction)
    (hf : f.IsAdmissible) :
    |2 * f.gammaLogDerivativeAtOne + f.zeroMass| ≤
      |Real.log f.analyticConductor| +
        (f.degree : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound +
        f.zeroMass := by
  have hM : 0 ≤ f.zeroMass := tsum_nonneg (fun ρ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have he :
    2 * f.gammaLogDerivativeAtOne + f.zeroMass =
      (2 * f.gammaLogDerivativeAtOne - Real.log f.analyticConductor) +
        Real.log f.analyticConductor +
        f.zeroMass := by
    ring
  rw [he]
  have h :=
    (abs_add_le
          ((2 * f.gammaLogDerivativeAtOne - Real.log f.analyticConductor) +
            Real.log f.analyticConductor)
          f.zeroMass).trans
      (add_le_add (abs_add_le _ _) (le_refl |f.zeroMass|))
  rw [abs_of_nonneg hM] at h
  linarith only [h, abs_twice_gammaLogDerivativeAtOne_sub_log_conductor_le f hf]

/-- For admissible RH data and cutoff greater than one, bound the zero-mass remainder
using only the analytic conductor, degree, zero mass, and universal gamma constants.
Apply the uniform digamma estimate to both endpoint terms in the explicit remainder bound.
No individual gamma shifts remain; the bound supports uniform estimates on families. -/
theorem norm_zeroMassReciprocalRemainder_le_conductor (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖f.zeroMassReciprocalRemainder x‖ ≤
      (f.degree : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound +
        (|Real.log f.analyticConductor| +
            (f.degree : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound +
            f.zeroMass) /
          x +
        2 * (f.zeroMass / Real.sqrt x) +
        2 *
          ((f.degree : ℝ) *
            ((Real.log x + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) / x)) +
        2 * ((f.degree : ℝ) * (Real.log 4 + 4)) := by
  have h := norm_zeroMassReciprocalRemainder_le_explicit f hf hRH hx
  rw [← twice_gammaLogDerivativeAtOne_sub_log_conductor f hf] at h
  have ha := abs_twice_gammaLogDerivativeAtOne_sub_log_conductor_le f hf
  have hb :=
    div_le_div_of_nonneg_right (abs_twice_gammaLogDerivativeAtOne_add_zeroMass_le f hf)
      (zero_lt_one.trans hx).le
  exact h.trans (by linarith only [ha, hb])

/-- For admissible data and any cutoff, bound the reciprocal arithmetic sum by the degree
times the corresponding nonnegative Mangoldt sum. Apply the Ramanujan coefficient bound
termwise. This permits a fixed-cutoff bound independent of the gamma shifts and conductor. -/
theorem norm_reciprocalSum_le_degree_majorant (f : GeneralLFunction) (hf : f.IsAdmissible) (x : ℝ) :
    ‖f.reciprocalSum x‖ ≤
      (f.degree : ℝ) * AnalyticNumberTheory.Arithmetic.reciprocalMangoldtSum x := by
  have h :=
    norm_finiteWeightedSum_le f hf (Finset.Ioc 0 ⌊x⌋₊)
      (fun n ↦ ArithmeticFunction.vonMangoldt n / (n : ℝ))
  simpa only [reciprocalSum, AnalyticNumberTheory.Arithmetic.reciprocalMangoldtSum,
    abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))] using h

/-- The universal degree coefficient in the zero-mass conductor bound.
It combines the digamma error, the reciprocal Mangoldt sum at cutoff 16, gamma residues,
and smoothing error. At that cutoff the remaining zero-mass terms can be absorbed. -/
noncomputable def zeroMassDegreeBound : ℝ :=
  (17 / 7) * AnalyticNumberTheory.Gamma.digammaLogErrorBound +
    (32 / 7) * AnalyticNumberTheory.Arithmetic.reciprocalMangoldtSum 16 +
    (2 / 7) * (Real.log 16 + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) +
    (32 / 7) * (Real.log 4 + 4)

/-- For admissible RH data, the zero mass is at most 17/7 times the absolute logarithmic
analytic conductor plus the degree times a universal constant. Evaluate the remainder
identity at cutoff 16, bound its arithmetic sum, and absorb the mass terms with coefficient
9/16. This supplies a conductor bound uniform in all admissible gamma shifts. -/
theorem zeroMass_le_conductor_degree (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) :
    f.zeroMass ≤
      (17 / 7) * |Real.log f.analyticConductor| + (f.degree : ℝ) * zeroMassDegreeBound := by
  have hr :=
    norm_zeroMassReciprocalRemainder_le_conductor f hf hRH (show (1 : ℝ) < 16 by norm_num only)
  have hs := norm_reciprocalSum_le_degree_majorant f hf 16
  have he := Complex.abs_re_le_norm (f.reciprocalSum 16)
  have hroot : Real.sqrt (16 : ℝ) = 4 := by norm_num only [Real.sqrt_eq_iff_eq_sq, Nat.ofNat_pos]
  rw [hroot, Real.norm_eq_abs, zeroMassReciprocalRemainder] at hr
  have ha := le_abs_self (f.zeroMass - Real.log f.analyticConductor + 2 * (f.reciprocalSum 16).re)
  have hl := le_abs_self (Real.log f.analyticConductor)
  have hn := neg_le_abs (f.reciprocalSum 16).re
  unfold zeroMassDegreeBound
  linarith only [hr, hs, he, ha, hl, hn]

/-- On every fixed-degree admissible RH family, zero mass is O(log analyticConductor)
as the conductor tends to infinity. Apply the uniform mass bound above exp(1), where
log conductor is at least one, and absorb the degree constant. This gives the family-level
zero-mass control required in the general L-value scenario. -/
theorem isBigO_zeroMass_conductorFilter (d : ℕ) :
    Asymptotics.IsBigO (conductorFilter d) (fun f : FixedDegreeFamily d ↦ f.val.zeroMass)
      (fun f ↦ Real.log f.val.analyticConductor) := by
  apply Asymptotics.IsBigO.of_bound ((17 / 7 : ℝ) + (d : ℝ) * |zeroMassDegreeBound|)
  apply Filter.eventually_comap.mpr
  refine (Filter.eventually_ge_atTop (Real.exp 1)).mono ?_
  intro C hC f hfC
  have hlog : 1 ≤ Real.log f.val.analyticConductor := by
    have h := Real.log_le_log (Real.exp_pos 1) hC
    rw [Real.log_exp, ← hfC] at h
    exact h
  have hM : 0 ≤ f.val.zeroMass := tsum_nonneg (fun ρ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hM, abs_of_nonneg (zero_le_one.trans hlog)]
  have hb := zeroMass_le_conductor_degree f.val f.property.2.1 f.property.2.2
  rw [f.property.1, abs_of_nonneg (zero_le_one.trans hlog)] at hb
  have hc :=
    mul_le_mul_of_nonneg_left (le_abs_self zeroMassDegreeBound) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hs :=
    mul_le_mul_of_nonneg_left hlog (mul_nonneg (Nat.cast_nonneg d) (abs_nonneg zeroMassDegreeBound))
  nlinarith only [hb, hc, hs]

/-- For admissible RH data and cutoff greater than one, the zero-mass remainder has an
upper bound involving only the analytic conductor, degree, cutoff and universal constants.
Substitute the uniform conductor bound for every occurrence of zero mass.
This supplies a pointwise family-uniform estimate without gamma-endpoint or mass parameters. -/
theorem norm_zeroMassReciprocalRemainder_le_uniform (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    let U := (17 / 7 : ℝ) * |Real.log f.analyticConductor| + (f.degree : ℝ) * zeroMassDegreeBound
    ‖f.zeroMassReciprocalRemainder x‖ ≤
      (f.degree : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound +
        (|Real.log f.analyticConductor| +
            (f.degree : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound +
            U) /
          x +
        2 * (U / Real.sqrt x) +
        2 *
          ((f.degree : ℝ) *
            ((Real.log x + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) / x)) +
        2 * ((f.degree : ℝ) * (Real.log 4 + 4)) := by
  dsimp only
  have hb := zeroMass_le_conductor_degree f hf hRH
  have hx0 : 0 ≤ x := (zero_lt_one.trans hx).le
  have h1 :=
    div_le_div_of_nonneg_right
      (add_le_add
        (le_refl
          (|Real.log f.analyticConductor| +
            (f.degree : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound))
        hb)
      hx0
  have h2 := div_le_div_of_nonneg_right hb (Real.sqrt_nonneg x)
  exact
    (norm_zeroMassReciprocalRemainder_le_conductor f hf hRH hx).trans (by linarith only [h1, h2])

/-- For admissible RH data and cutoff greater than one, the zero-mass remainder is at most
a universal constant times the degree plus 58/7 times |log conductor|/sqrt(cutoff).
Insert the uniform mass bound, use sqrt(x) ≤ x and log(x)/x ≤ 1, and absorb the gamma terms.
This realizes the uniform error scale used in the general zero-mass estimate. -/
theorem norm_zeroMassReciprocalRemainder_le_degree_add_conductor (f : GeneralLFunction)
    (hf : f.IsAdmissible) (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖f.zeroMassReciprocalRemainder x‖ ≤
      (f.degree : ℝ) *
          (2 * AnalyticNumberTheory.Gamma.digammaLogErrorBound + 3 * |zeroMassDegreeBound| +
            2 * (1 + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) +
            2 * (Real.log 4 + 4)) +
        (58 / 7) * (|Real.log f.analyticConductor| / Real.sqrt x) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hs1 : 1 ≤ Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx.le
  have hsx : Real.sqrt x ≤ x := (Real.sqrt_le_iff).mpr ⟨hx0.le, by nlinarith only [hx.le]⟩
  have hA : 0 ≤ AnalyticNumberTheory.Gamma.digammaLogErrorBound :=
    tsum_nonneg (fun n ↦ div_nonneg (by norm_num only) (sq_nonneg _))
  have hB : 0 ≤ AnalyticNumberTheory.Gamma.reciprocalGammaTailBound :=
    tsum_nonneg (fun n ↦ div_nonneg (by norm_num only) (sq_nonneg _))
  have hM := zeroMass_le_conductor_degree f hf hRH
  have hK :=
    mul_le_mul_of_nonneg_left (le_abs_self zeroMassDegreeBound)
      (Nat.cast_nonneg f.degree : (0 : ℝ) ≤ f.degree)
  have hMb :
    f.zeroMass ≤
      (17 / 7) * |Real.log f.analyticConductor| + (f.degree : ℝ) * |zeroMassDegreeBound| := by
    linarith only [hM, hK]
  have hMx :
    f.zeroMass / x ≤
      (17 / 7) * (|Real.log f.analyticConductor| / Real.sqrt x) +
        (f.degree : ℝ) * |zeroMassDegreeBound| := by
    apply (div_le_div_of_nonneg_right hMb hx0.le).trans
    rw [add_div, mul_div_assoc]
    have h1 :=
      div_le_div_of_nonneg_left (abs_nonneg (Real.log f.analyticConductor))
        (zero_lt_one.trans_le hs1) hsx
    have h2 :=
      (div_le_div_of_nonneg_left
            (mul_nonneg (Nat.cast_nonneg f.degree) (abs_nonneg zeroMassDegreeBound)) zero_lt_one
            hx.le).trans_eq
        (div_one _)
    linarith only [h1, h2]
  have hMs :
    f.zeroMass / Real.sqrt x ≤
      (17 / 7) * (|Real.log f.analyticConductor| / Real.sqrt x) +
        (f.degree : ℝ) * |zeroMassDegreeBound| := by
    apply (div_le_div_of_nonneg_right hMb (Real.sqrt_nonneg x)).trans
    rw [add_div, mul_div_assoc]
    have h2 :=
      (div_le_div_of_nonneg_left
            (mul_nonneg (Nat.cast_nonneg f.degree) (abs_nonneg zeroMassDegreeBound)) zero_lt_one
            hs1).trans_eq
        (div_one _)
    linarith only [h2]
  have hC :=
    div_le_div_of_nonneg_left (abs_nonneg (Real.log f.analyticConductor)) (zero_lt_one.trans_le hs1)
      hsx
  have hAx :=
    (div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg f.degree) hA) zero_lt_one
          hx.le).trans_eq
      (div_one _)
  have hBx := (div_le_div_of_nonneg_left hB zero_lt_one hx.le).trans_eq (div_one _)
  have hlog : Real.log x / x ≤ 1 := by
    apply (div_le_one hx0).mpr
    linarith only [Real.log_le_sub_one_of_pos hx0]
  have hg :
    (f.degree : ℝ) * ((Real.log x + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) / x) ≤
      (f.degree : ℝ) * (1 + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) := by
    rw [add_div]
    exact mul_le_mul_of_nonneg_left (add_le_add hlog hBx) (Nat.cast_nonneg f.degree)
  have hr := norm_zeroMassReciprocalRemainder_le_conductor f hf hRH hx
  rw [add_div, add_div] at hr
  nlinarith only [hr, hMx, hMs, hC, hAx, hg]

/-- For admissible RH data and cutoff greater than one, bound the reciprocal remainder
by conductor, degree, zero mass and the uniform gamma residue constant.
Compare the gamma endpoint with half the logarithmic conductor and add the mass correction.
This supplies the smaller remainder in the combined truncated L-value formula. -/
theorem norm_reciprocalRemainder_le_conductor (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖f.reciprocalRemainder x‖ ≤
      (|Real.log f.analyticConductor| +
            (f.degree : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound +
            2 * f.zeroMass) /
          (2 * x) +
        (f.degree : ℝ) *
          ((Real.log x + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) / x) := by
  have hM : 0 ≤ f.zeroMass := tsum_nonneg (fun ρ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have he :
    f.gammaLogDerivativeAtOne + f.zeroMass =
      (2 * f.gammaLogDerivativeAtOne + f.zeroMass + f.zeroMass) / 2 := by
    ring
  have hg :
    |f.gammaLogDerivativeAtOne + f.zeroMass| ≤
      (|Real.log f.analyticConductor| +
          (f.degree : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound +
          2 * f.zeroMass) /
        2 := by
    rw [he, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num only)]
    have h := abs_add_le (2 * f.gammaLogDerivativeAtOne + f.zeroMass) f.zeroMass
    rw [abs_of_nonneg hM] at h
    linarith only [h, abs_twice_gammaLogDerivativeAtOne_add_zeroMass_le f hf]
  have h := div_le_div_of_nonneg_right hg (zero_lt_one.trans hx).le
  rw [div_div] at h
  exact (norm_reciprocalRemainder_le_uniform_gamma f hf hRH hx).trans (add_le_add h (le_refl _))

end PseudoPrime.LLS.Extensions.GeneralLFunction
