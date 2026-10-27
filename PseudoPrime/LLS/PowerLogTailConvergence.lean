/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogBoundarySummation
public import PseudoPrime.LLS.RiemannWeightedErrorBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtDirichletBounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Power-weighted Mangoldt tail convergence under RH -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The actual logarithmically weighted Mangoldt sum is nonnegative at a
positive cutoff. Each retained quotient is at least one and Mangoldt is
nonnegative. This supplies the sign for tail domination. -/
theorem logWeightedMangoldtSum_nonneg_of_pos {t : ℝ} (ht : 0 < t) :
    0 ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t := by
  apply Finset.sum_nonneg
  intro m hm
  exact
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.log_nonneg
        ((one_le_div₀ (Nat.cast_pos.mpr (Finset.mem_Ioc.mp hm).1)).mpr
          ((Nat.le_floor_iff ht.le).mp (Finset.mem_Ioc.mp hm).2)))

/-- The actual logarithmically weighted sum is continuous on positive
cutoffs. Around each point use a fixed larger finite clipped-log prefix.
This supplies measurability of the power-tail integrand. -/
theorem continuousOn_logWeightedMangoldtSum_Ioi :
    ContinuousOn AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (Set.Ioi (0 : ℝ)) := by
  intro t ht
  have hc :
    ContinuousOn AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (Set.Icc 0 (t + 1)) := by
    simpa only [one_mul] using
      AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled (x := (1 : ℝ))
        (by norm_num only) (t + 1)
  exact (hc.continuousAt (Icc_mem_nhds ht (lt_add_one t))).continuousWithinAt

/-- Under RH and a cutoff at least one, the logarithmically weighted sum
is at most four times the cutoff. The sharp error formula and elementary
square-root and logarithm bounds give a coarse integrable majorant. -/
theorem logWeightedMangoldtSum_le_four_mul (hRH : RiemannHypothesis) {t : ℝ} (ht : 1 ≤ t) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t ≤ 4 * t := by
  have he :=
    (abs_le.mp (logWeightedMangoldtSum_error_le_refined_global hRH (zero_lt_one.trans_le ht))).2
  rw [max_eq_right ht] at he
  have hs : Real.sqrt t ≤ t := Real.sqrt_le_iff.mpr ⟨zero_le_one.trans ht, by nlinarith only [ht]⟩
  linarith only [he, hs, Real.log_le_self (zero_le_one.trans ht), ht]

/-- Under RH, every resolvent exponent sigma greater than one gives an
integrable logarithmic power density beyond a cutoff at least one.
Dominate it by four sigma squared times t to the minus sigma, retaining
the full exponent range needed by the signed resolvent certificate. -/
theorem integrableOn_power_logWeightedMangoldtSum (hRH : RiemannHypothesis) {σ a : ℝ} (hσ : 1 < σ)
    (ha : 1 ≤ a) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * (σ ^ 2 * t ^ (-σ - 1)))
      (Set.Ioi a) := by
  have hc :
    ContinuousOn
      (fun t : ℝ ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * (σ ^ 2 * t ^ (-σ - 1)))
      (Set.Ioi a) :=
    (continuousOn_logWeightedMangoldtSum_Ioi.mono (Set.Ioi_subset_Ioi (zero_le_one.trans ha))).mul
      (continuousOn_const.mul
        (fun t ht ↦
          (Real.continuousAt_rpow_const t (-σ - 1)
              (Or.inl (zero_lt_one.trans_le (ha.trans ht.le)).ne')).continuousWithinAt))
  refine
    ((integrableOn_Ioi_rpow_of_lt (by linarith only [hσ] : -σ < -1)
              (zero_lt_one.trans_le ha)).const_mul
          (4 * σ ^ 2)).mono'
      (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  have ht1 := ha.trans ht.le
  have hm :=
    mul_le_mul_of_nonneg_right (logWeightedMangoldtSum_le_four_mul hRH ht1)
      (mul_nonneg (sq_nonneg σ) (Real.rpow_nonneg (zero_le_one.trans ht1) (-σ - 1)))
  rw [Real.norm_of_nonneg
      (mul_nonneg (logWeightedMangoldtSum_nonneg_of_pos (zero_lt_one.trans_le ht1))
        (mul_nonneg (sq_nonneg σ) (Real.rpow_nonneg (zero_le_one.trans ht1) (-σ - 1))))]
  have he : 4 * t * (σ ^ 2 * t ^ (-σ - 1)) = (4 * σ ^ 2) * t ^ (-σ) := by
    rw [Real.rpow_sub_one (zero_lt_one.trans_le ht1).ne' (-σ)]
    calc
      _ = (4 * σ ^ 2 * t ^ (-σ)) * (t / t) := by ring
      _ = _ := by rw [div_self (zero_lt_one.trans_le ht1).ne', mul_one]
  exact hm.trans_eq he

/-- The upper Chebyshev boundary is nonnegative for nonnegative sigma
and positive cutoff. Both arithmetic sums and the real power are nonnegative. -/
theorem power_mangoldt_boundary_nonneg {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) :
    0 ≤
      t ^ (-σ) *
        (Chebyshev.psi t + σ * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t) := by
  exact
    mul_nonneg (Real.rpow_nonneg ht.le (-σ))
      (add_nonneg (Chebyshev.psi_nonneg t)
        (mul_nonneg hσ (logWeightedMangoldtSum_nonneg_of_pos ht)))

/-- Under RH and nonnegative sigma, the upper boundary is bounded by a
fixed coefficient times t to the one minus sigma. The elementary Chebyshev
bound and the coarse logarithmic bound suffice for the limit. -/
theorem power_mangoldt_boundary_le_majorant (hRH : RiemannHypothesis) {σ t : ℝ} (hσ : 0 ≤ σ)
    (ht : 1 ≤ t) :
    t ^ (-σ) * (Chebyshev.psi t + σ * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t) ≤
      (Real.log 4 + 4 + 4 * σ) * t ^ (1 - σ) := by
  have hm :=
    mul_le_mul_of_nonneg_left
      (add_le_add (Chebyshev.psi_le_const_mul_self (zero_le_one.trans ht))
        (mul_le_mul_of_nonneg_left (logWeightedMangoldtSum_le_four_mul hRH ht) hσ))
      (Real.rpow_nonneg (zero_le_one.trans ht) (-σ))
  rw [show (1 - σ) = (-σ) + 1 by ring, Real.rpow_add_one (zero_lt_one.trans_le ht).ne' (-σ)]
  convert hm using 1
  ring

/-- Under RH and sigma greater than one, the upper boundary tends to
zero. Sandwich the nonnegative boundary between zero and the decaying
real power. This removes the endpoint before the infinite-tail identity. -/
theorem tendsto_power_mangoldt_boundary_zero (hRH : RiemannHypothesis) {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto
      (fun t : ℝ ↦
        t ^ (-σ) * (Chebyshev.psi t + σ * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t))
      Filter.atTop (nhds (0 : ℝ)) := by
  have hr : Filter.Tendsto (fun t : ℝ ↦ t ^ (1 - σ)) Filter.atTop (nhds (0 : ℝ)) := by
    rw [show (1 - σ) = -(σ - 1) by ring]
    exact tendsto_rpow_neg_atTop (sub_pos.mpr hσ)
  have hm := hr.const_mul (Real.log 4 + 4 + 4 * σ)
  simp only [mul_zero] at hm
  apply Filter.Tendsto.squeeze' (tendsto_const_nhds) hm
  · exact
      (Filter.eventually_ge_atTop (1 : ℝ)).mono
        (fun t ht ↦
          power_mangoldt_boundary_nonneg (zero_lt_one.trans hσ).le (zero_lt_one.trans_le ht))
  · exact
      (Filter.eventually_ge_atTop (1 : ℝ)).mono
        (fun t ht ↦ power_mangoldt_boundary_le_majorant hRH (zero_lt_one.trans hσ).le ht)

/-- Under RH, for sigma greater than one and lower cutoff at least one,
the full Mangoldt power series minus its retained prefix equals the
improper logarithmic integral minus the exact lower Chebyshev boundary.
Combine the arithmetic prefix limit, integrability, vanishing upper
boundary and the finite formula. This is the scalar Euler-tail identity. -/
theorem powerMangoldtTail_eq_improper_log_integral (hRH : RiemannHypothesis) {σ a : ℝ} (hσ : 1 < σ)
    (ha : 1 ≤ a) :
    (∑' m : ℕ, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ)) -
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ)) =
      (∫ t in Set.Ioi a,
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * (σ ^ 2 * t ^ (-σ - 1))) -
        a ^ (-σ) *
          (Chebyshev.psi a + σ * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a) := by
  have hp := AnalyticNumberTheory.Arithmetic.tendsto_powerMangoldtTailPrefix hσ a
  have hi :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi a
      (integrableOn_power_logWeightedMangoldtSum hRH hσ ha)
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  have hb :=
    (tendsto_power_mangoldt_boundary_zero hRH hσ).comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  have hr :=
    (hi.sub_const
          (a ^ (-σ) *
            (Chebyshev.psi a + σ * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a))).add
      hb
  simp only [add_zero] at hr
  have he :
    (fun n : ℕ ↦
        ∑ m ∈ Finset.Ioc ⌊a⌋₊ n, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ)) =ᶠ[Filter.atTop]
      (fun n : ℕ ↦
        (∫ t in a..(n : ℝ),
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * (σ ^ 2 * t ^ (-σ - 1))) -
            a ^ (-σ) *
              (Chebyshev.psi a + σ * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a) +
          (n : ℝ) ^ (-σ) *
            (Chebyshev.psi n + σ * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum n)) := by
    apply (tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop a)).mono
    intro n hn
    simpa only [Nat.floor_natCast] using
      AnalyticNumberTheory.Arithmetic.power_mangoldt_tail_eq_log_integral σ
        (zero_lt_one.trans_le ha) hn
  exact tendsto_nhds_unique (hp.congr' he) hr

/-- For an exponent greater than one, the linear variation density is
integrable beyond any positive cutoff. Cancel the extra reciprocal and
use the convergent real power. This evaluates the Euler-tail main term. -/
theorem power_linear_density_integrable {σ a : ℝ} (hσ : 1 < σ) (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ t * (σ ^ 2 * t ^ (-σ - 1))) (Set.Ioi a) := by
  have ht := (integrableOn_Ioi_rpow_of_lt (by linarith only [hσ] : -σ < -1) ha).const_mul (σ ^ 2)
  apply MeasureTheory.IntegrableOn.congr_fun ht _ measurableSet_Ioi
  intro t ht
  have ht0 := ha.trans ht
  dsimp only
  symm
  rw [Real.rpow_sub_one ht0.ne' (-σ)]
  calc
    _ = _ := by
      calc
        _ = σ ^ 2 * t ^ (-σ) * (t / t) := by ring
        _ = _ := by rw [div_self ht0.ne', mul_one]

/-- Beyond a positive cutoff, the integral of the linear power variation
density is sigma squared times a to the one minus sigma divided by
sigma minus one. Apply the exact improper real-power integral. -/
theorem power_linear_density_integral_eq {σ a : ℝ} (hσ : 1 < σ) (ha : 0 < a) :
    (∫ t in Set.Ioi a, t * (σ ^ 2 * t ^ (-σ - 1))) = σ ^ 2 * a ^ (1 - σ) / (σ - 1) := by
  have he :
    (fun t : ℝ ↦ t * (σ ^ 2 * t ^ (-σ - 1))) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi a)]
      (fun t : ℝ ↦ σ ^ 2 * t ^ (-σ)) := by
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have ht0 := ha.trans ht
    dsimp only
    rw [Real.rpow_sub_one ht0.ne' (-σ)]
    calc
      _ = σ ^ 2 * t ^ (-σ) * (t / t) := by ring
      _ = _ := by rw [div_self ht0.ne', mul_one]
  rw [MeasureTheory.integral_congr_ae he, MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith only [hσ] : -σ < -1) ha]
  rw [show -σ + 1 = 1 - σ by ring, show 1 - σ = -(σ - 1) by ring, div_neg, neg_div, neg_neg]
  ring

end PseudoPrime.LLS
