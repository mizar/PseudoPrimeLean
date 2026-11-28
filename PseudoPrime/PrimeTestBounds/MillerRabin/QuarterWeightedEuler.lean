/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedPhase
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftEuler

/-! # Section 107 Euler weight and its derivative -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private noncomputable def combine101 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  let Q := fun s : ℝ ↦
    (Real.exp (-(51 / 50) * s) * f (x + s) + Real.exp ((51 / 50) * s) * f (x - s)) / 2
  (((11 / 25 : ℝ) ^ 2 + (91 / 200 : ℝ) ^ 2) / 2) * Q 0 - (11 / 25 * (91 / 200 : ℝ)) * Q (1 / 5) -
      (11 / 25) * Q (14 / 5) +
    (91 / 200) * Q 3

private noncomputable def c0 : ℝ :=
  weightedEulerPoly (11 / 25) (91 / 200) 5

private noncomputable def c1 : ℝ :=
  combine101 (fun x ↦ 3 * (51 / 50) / 8 + (51 / 50 : ℝ) ^ 2 / 4 * x) 5

private noncomputable def c2 : ℝ :=
  combine101 (fun _ ↦ (51 / 50 : ℝ) ^ 2 / 8) 5

private theorem poly101_expand (x : ℝ) :
    weightedEulerPoly (11 / 25) (91 / 200) x = c0 + c1 * (x - 5) + c2 * (x - 5) ^ 2 := by
  unfold c0 c1 c2 combine101 weightedEulerPoly weightedShiftPoly
  dsimp only
  ring

private theorem poly101_coeff :
    c0 ∈ Set.Icc 0.96548090 0.96548098 ∧
      c1 ∈ Set.Icc 0.71803505 0.71803515 ∧ c2 ∈ Set.Icc 0.13262084 0.13262092 := by
  have ht := exp_t
  have hb := exp_b
  have hh := exp_h
  have ht' :=
    And.intro (one_div_le_one_div_of_le (Real.exp_pos _) ht.2)
      (one_div_le_one_div_of_le (by norm_num only) ht.1)
  have hb' :=
    And.intro (one_div_le_one_div_of_le (Real.exp_pos _) hb.2)
      (one_div_le_one_div_of_le (by norm_num only) hb.1)
  have hh' :=
    And.intro (one_div_le_one_div_of_le (Real.exp_pos _) hh.2)
      (one_div_le_one_div_of_le (by norm_num only) hh.1)
  unfold c0 c1 c2 combine101 weightedEulerPoly weightedShiftPoly
  simp only [neg_mul, Real.exp_neg, ← one_div, mul_zero, Real.exp_zero, one_mul]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    linarith only [ht.1, ht.2, ht'.1, ht'.2, hb.1, hb.2, hb'.1, hb'.2, hh.1, hh.2, hh'.1, hh'.2]

/-- With the section 107 coefficients, the Euler polynomial is strictly
positive at every logarithmic argument at least five. -/
theorem weighted_euler_pos {x : ℝ} (hx : 5 ≤ x) : 0 < weightedEulerPoly (11 / 25) (91 / 200) x := by
  obtain ⟨h0, h1, h2⟩ := poly101_coeff
  rw [poly101_expand]
  have h1' : 0 ≤ c1 := by linarith only [h1.1]
  have h2' : 0 ≤ c2 := by linarith only [h2.1]
  linarith only [h0.1, mul_nonneg h1' (sub_nonneg.mpr hx), mul_nonneg h2' (sq_nonneg (x - 5))]

private theorem poly101_deriv (x : ℝ) :
    HasDerivAt (weightedEulerPoly (11 / 25) (91 / 200)) (c1 + 2 * c2 * (x - 5)) x := by
  have h := ((hasDerivAt_id x).sub_const 5)
  have H := ((h.const_mul c1).const_add c0).add ((h.pow 2).const_mul c2)
  rw [show
      weightedEulerPoly (11 / 25) (91 / 200) = (fun y : ℝ ↦ c0 + c1 * (y - 5) + c2 * (y - 5) ^ 2)
      from funext poly101_expand]
  change HasDerivAt (fun y : ℝ ↦ c0 + c1 * (y - 5) + c2 * (y - 5) ^ 2) _ x at H
  convert H using 1
  norm_num only [id, Nat.cast_ofNat]
  ring

/-- The partial-summation weight (38/25)P-P' for the section 107 polynomial
is strictly positive at logarithmic arguments at least five. -/
theorem weighted_euler_diff_pos {x : ℝ} (hx : 5 ≤ x) :
    0 <
      (38 / 25) * weightedEulerPoly (11 / 25) (91 / 200) x -
        deriv (weightedEulerPoly (11 / 25) (91 / 200)) x := by
  obtain ⟨h0, h1, h2⟩ := poly101_coeff
  rw [poly101_expand, (poly101_deriv x).deriv]
  have h₀ : 0 < (38 / 25) * c0 - c1 := by linarith only [h0.1, h1.2]
  have h₁ : 0 ≤ (38 / 25) * c1 - 2 * c2 := by linarith only [h1.1, h2.2]
  have h₂ : 0 ≤ (38 / 25) * c2 := by linarith only [h2.1]
  convert
    add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg h₀ (mul_nonneg h₁ (sub_nonneg.mpr hx)))
      (mul_nonneg h₂ (sq_nonneg (x - 5))) using
    1
  ring

/-- The positive-variable Euler weight for the section 107 partial summation. -/
noncomputable def weightedEulerDensity (t : ℝ) : ℝ :=
  Real.exp (-(38 / 25 : ℝ) * Real.log t) * weightedEulerPoly (11 / 25) (91 / 200) (Real.log t)

/-- At positive t, the derivative of the Euler density is the negative
logarithmic differential weight times the positive scale factor. -/
theorem weighted_euler_density_deriv {t : ℝ} (ht : 0 < t) :
    deriv weightedEulerDensity t =
      -(Real.exp (-(38 / 25 : ℝ) * Real.log t) *
            ((38 / 25) * weightedEulerPoly (11 / 25) (91 / 200) (Real.log t) -
              deriv (weightedEulerPoly (11 / 25) (91 / 200)) (Real.log t))) *
        t⁻¹ := by
  let x := Real.log t
  have he := ((hasDerivAt_id x).const_mul (-(38 / 25 : ℝ))).exp
  have h := (he.mul (poly101_deriv x)).comp t (Real.hasDerivAt_log ht.ne')
  change HasDerivAt weightedEulerDensity _ t at h
  rw [h.deriv, (poly101_deriv x).deriv]
  dsimp only [id, x]
  ring

/-- For log t at least five, the section 107 Euler density has negative
derivative. This sign controls the centered Chebyshev error integral. -/
theorem weighted_euler_density_deriv_neg {t : ℝ} (ht : 0 < t) (hl : 5 ≤ Real.log t) :
    deriv weightedEulerDensity t < 0 := by
  rw [weighted_euler_density_deriv ht]
  have hp := mul_pos (Real.exp_pos (-(38 / 25 : ℝ) * Real.log t)) (weighted_euler_diff_pos hl)
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hp) (inv_pos.mpr ht)

private theorem weighted_density_analytic {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℝ weightedEulerDensity t := by
  unfold weightedEulerDensity weightedEulerPoly weightedShiftPoly
  fun_prop (disch := exact ht.ne')

/-- On a positive finite interval, centered Abel summation expresses the
section 107 Euler sum by its main integral, endpoint errors, and derivative integral. -/
theorem weighted_euler_abel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) *
            weightedEulerPoly (11 / 25) (91 / 200) (Real.log n)) -
        (∫ t : ℝ in a..b, weightedEulerDensity t) =
      (Chebyshev.psi b - b) * weightedEulerDensity b -
        (Chebyshev.psi a - a) * weightedEulerDensity a -
        ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv weightedEulerDensity t := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) := weighted_density_analytic (ha.trans_le ht.1)
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval ha.le hab
      (fun t ht ↦ (hd t ht).differentiableAt)
      (show ContinuousOn (deriv weightedEulerDensity) (Set.Icc a b) from fun t ht ↦
          (hd t ht).deriv.continuousAt.continuousWithinAt).integrableOn_Icc
  rw [← h]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1
  have hp : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  rw [weightedEulerDensity, Real.rpow_def_of_pos hp, neg_mul, mul_comm (38 / 25 : ℝ), Real.exp_neg]
  ring

/-- The upper centered Abel boundary for the section 107 weight goes to zero
because its quadratic logarithmic moments decay against the unconditional psi bound. -/
theorem weighted_euler_boundary_zero :
    Filter.Tendsto (fun x : ℝ ↦ (Chebyshev.psi x - x) * weightedEulerDensity x) Filter.atTop
      (nhds 0) := by
  let E := fun x : ℝ ↦ (Chebyshev.psi x - x) / 4
  have hE : ∀ᶠ x : ℝ in Filter.atTop, ‖E x‖ ≤ 2 * x := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 := zero_le_one.trans hx
    have hlog := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 4)
    have hu :=
      (Chebyshev.psi_le_const_mul_self hx0).trans
        (mul_le_mul_of_nonneg_right (by linarith only [hlog] : Real.log 4 + 4 ≤ 7) hx0)
    rw [Real.norm_eq_abs, abs_le]
    dsimp only [E]
    constructor <;> linarith only [hu, Chebyshev.psi_nonneg (x := x), hx0]
  have hm (k : ℕ) :=
    AnalyticNumberTheory.RiemannZeta.moment_boundary_tendsto (by norm_num only : (1 : ℝ) < 38 / 25)
      k E hE
  let C := c0 - 5 * c1 + 25 * c2
  let L := c1 - 10 * c2
  let Q := c2
  have hh :=
    ((((hm 0).const_mul (4 * C)).add ((hm 1).const_mul (4 * L))).add ((hm 2).const_mul (4 * Q)))
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight, E, weightedEulerDensity, C, L,
    Q]
  rw [poly101_expand]
  rw [Real.rpow_def_of_pos hx]
  rw [show Real.log x * -(38 / 25 : ℝ) = -(38 / 25 : ℝ) * Real.log x by ring]
  ring

/-- RH bounds the centered finite Abel error by its explicit square-root
envelope wherever the section 107 Euler density is decreasing. -/
theorem weighted_euler_error_RH (hRH : RiemannHypothesis) {a b : ℝ} (ha : 101 ≤ a)
    (hla : 5 ≤ Real.log a) (hab : a ≤ b) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv weightedEulerDensity t| ≤
      ∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv weightedEulerDensity t := by
  have hcont :
    ContinuousOn (fun t : ℝ ↦ Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv weightedEulerDensity t)
      (Set.Icc a b) := by
    intro t ht
    have hp : 0 < t := by linarith only [ha, ht.1]
    exact
      ((Real.continuous_sqrt.continuousAt.mul
              (((Real.continuousAt_log hp.ne').pow 2).div_const 24)).mul
          (weighted_density_analytic hp).deriv.continuousAt.neg).continuousWithinAt
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, ← Real.norm_eq_abs]
  apply
    MeasureTheory.norm_integral_le_of_norm_le
      (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have ht' := ha.trans ht.1.le
  have hp : 0 < t := by linarith only [ht']
  have hl := hla.trans (Real.log_le_log (by linarith only [ha]) ht.1.le)
  have hn := (weighted_euler_density_deriv_neg hp hl).le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos hn]
  exact mul_le_mul_of_nonneg_right (psi_log_sq_of_RH hRH ht') (neg_nonneg.mpr hn)

/-- The section 107 Euler weights are absolutely summable by the three
von Mangoldt logarithmic moments at exponent 38/25. -/
theorem weighted_euler_summable :
    Summable
      (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) *
          weightedEulerPoly (11 / 25) (91 / 200) (Real.log n)) := by
  have hm :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 38 / 25)
      (by norm_num only)
  have h :=
    (((hm 0).mul_left (c0 - 5 * c1 + 25 * c2)).add ((hm 1).mul_left (c1 - 10 * c2))).add
      ((hm 2).mul_left c2)
  apply h.congr
  intro n
  rw [poly101_expand]
  ring

/-- Under RH, a limit M for the main integral and an eventual upper bound D
for the explicit slope integral bound the full section 107 Euler tail. -/
theorem weighted_euler_tail_RH (hRH : RiemannHypothesis) {a M D : ℝ} (ha : 101 ≤ a)
    (hl : 5 ≤ Real.log a)
    (hm :
      Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, weightedEulerDensity t) Filter.atTop (nhds M))
    (hd :
      ∀ᶠ b : ℝ in Filter.atTop,
        (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv weightedEulerDensity t) ≤
          D) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) *
        weightedEulerPoly (11 / 25) (91 / 200) (Real.log n)
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤
      M + Real.sqrt a * (Real.log a ^ 2 / 24) * weightedEulerDensity a + D := by
  intro f
  have hf0 : f 0 = 0 := by
    dsimp only [f]; rw [ArithmeticFunction.map_zero, zero_div, zero_mul]
  have hs :=
    (AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix f hf0 weighted_euler_summable a).comp
      (show Filter.Tendsto (fun b : ℝ ↦ ⌊b⌋₊) Filter.atTop Filter.atTop from
        tendsto_nat_floor_atTop)
  have h :=
    (((hm.add weighted_euler_boundary_zero).sub_const
          ((Chebyshev.psi a - a) * weightedEulerDensity a)).sub
      hs)
  rw [add_zero] at h
  have he :=
    h.congr'
      (show
        ∀ᶠ b : ℝ in Filter.atTop,
          _ = ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv weightedEulerDensity t
        from by
        filter_upwards [Filter.eventually_ge_atTop a] with b hb
        have hab := weighted_euler_abel (by linarith only [ha]) hb
        dsimp only [Function.comp_apply, f]
        linarith only [hab])
  have hb :=
    ge_of_tendsto he
      (show
        ∀ᶠ b : ℝ in Filter.atTop,
          -D ≤ ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv weightedEulerDensity t
        from by
        filter_upwards [hd, Filter.eventually_ge_atTop a] with b hb hab
        exact (abs_le.mp ((weighted_euler_error_RH hRH ha hl hab).trans hb)).1)
  have hw : 0 ≤ weightedEulerDensity a := mul_nonneg (Real.exp_pos _).le (weighted_euler_pos hl).le
  have hp := mul_le_mul_of_nonneg_right (abs_le.mp (psi_log_sq_of_RH hRH ha)).1 hw
  linarith only [hb, hp]

end PseudoPrime.PrimeTestBounds.MillerRabin
