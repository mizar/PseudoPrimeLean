/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevMomentTail43
import PseudoPrime.Analysis.LogarithmicPowerAbsorption
import PseudoPrime.Analysis.LogPowerTailIntegral

/-! # Vanishing boundary terms for Chebyshev moment tails -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Eventually, the square-root logarithmic Chebyshev error envelope is at
most `x` in absolute value. A fixed logarithmic power is eventually smaller
than the square root, and the remaining logarithm has the required sign. -/
theorem chebyshev_error_eventually_le :
    ∀ᶠ x : ℝ in Filter.atTop,
      |Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi))| ≤ x := by
  have hp :=
    Analysis.eventually_mul_one_add_log_pow_lt_rpow (C := 1) (s := 1 / 2) (by norm_num only)
      (by norm_num only) 2
  filter_upwards [hp, Filter.eventually_ge_atTop (Real.exp 1)] with x hpow hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hl : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hx
    rw [Real.log_exp] at h
    exact h
  have hll0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hl
  have hll : Real.log (Real.log x) ≤ Real.log x := by
    have h := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hl)
    linarith only [h]
  have hp2 :=
    pow_le_pow_left₀ (show 0 ≤ Real.log x by linarith only [hl])
      (show Real.log x ≤ 1 + Real.log x by linarith only) 2
  simp only [one_mul, ← Real.sqrt_eq_rpow] at hpow
  have hlog2 : Real.log x ^ 2 ≤ Real.sqrt x := hp2.trans hpow.le
  have hprod : 0 ≤ Real.log x * (Real.log x - Real.log (Real.log x)) :=
    mul_nonneg (by linarith only [hl]) (sub_nonneg.mpr hll)
  have hprod2 : Real.log x * (Real.log x - Real.log (Real.log x)) ≤ Real.sqrt x := by
    have hh := mul_nonneg (show 0 ≤ Real.log x by linarith only [hl]) hll0
    nlinarith only [hlog2, hh]
  have hs := Real.sqrt_nonneg x
  have hsq := Real.sq_sqrt hx0.le
  have hden : 0 < 8 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hval :
    0 ≤ Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) :=
    mul_nonneg hs (div_nonneg hprod hden.le)
  rw [abs_of_nonneg hval]
  have hm := mul_le_mul_of_nonneg_left hprod2 hs
  have hh : Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x))) ≤ x := by
    nlinarith only [hm, hsq]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).2
  have hxnonneg := hx0.le
  nlinarith only [hh, hden, Real.pi_gt_three, hxnonneg]

/-- For `σ > 1`, a power-logarithm weight times any eventual linear-growth
envelope tends to zero. The logarithmic moment is absorbed by the positive
power saving `σ - 1`. -/
theorem moment_boundary_tendsto {σ : ℝ} (hσ : 1 < σ) (k : ℕ) (E : ℝ → ℝ)
    (hE : ∀ᶠ x : ℝ in Filter.atTop, ‖E x‖ ≤ 2 * x) :
    Filter.Tendsto (fun x : ℝ ↦ Arithmetic.mangoldtMomentWeight σ k x * E x) Filter.atTop
      (nhds 0) := by
  have hr : 0 < σ - 1 := by linarith only [hσ]
  have ht := (Analysis.log_pow_mul_neg_rpow_tendsto hr k).const_mul 2
  have ht' :
    Filter.Tendsto (fun x : ℝ ↦ 2 * (x ^ (-(σ - 1)) * Real.log x ^ k)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using ht
  apply squeeze_zero_norm' ?_ ht'
  filter_upwards [hE, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hw : 0 ≤ Arithmetic.mangoldtMomentWeight σ k x :=
    mul_nonneg (Real.rpow_nonneg hx0.le _) (pow_nonneg hl k)
  have hb := mul_le_mul_of_nonneg_left hx hw
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hw]
  have heq :
    Arithmetic.mangoldtMomentWeight σ k x * (2 * x) = 2 * (x ^ (-(σ - 1)) * Real.log x ^ k) := by
    dsimp only [Arithmetic.mangoldtMomentWeight]
    have hrpow : x ^ (-σ) * x = x ^ (-(σ - 1)) := by
      have h := Real.rpow_add hx0 (-σ) 1
      rw [Real.rpow_one] at h
      convert h.symm using 1
      congr 1
      ring
    rw [show x ^ (-σ) * Real.log x ^ k * (2 * x) = 2 * (x ^ (-σ) * x) * Real.log x ^ k by ring,
      hrpow]
    ring
  rw [heq] at hb
  exact hb

/-- Both Chebyshev envelopes eventually have absolute value at most `2x`.
Use the linear majorant for their common error term and the triangle bound. -/
theorem chebyshev_envelopes_eventually_le :
    ∀ᶠ x : ℝ in Filter.atTop,
      ‖chebyshevMajorant43 x‖ ≤ 2 * x ∧ ‖chebyshevMinorant43 x‖ ≤ 2 * x := by
  filter_upwards [chebyshev_error_eventually_le, Filter.eventually_ge_atTop (0 : ℝ)] with x h hx
  have hm :=
    abs_add_le x (Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)))
  have hn :=
    abs_sub x (Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)))
  rw [abs_of_nonneg hx] at hm hn
  simp only [Real.norm_eq_abs, chebyshevMajorant43, chebyshevMinorant43]
  constructor
  · linarith only [hm, h]
  · linarith only [hn, h]

/-- For `σ > 1`, the upper Chebyshev envelope multiplied by the moment
weight tends to zero at the natural upper endpoints. This removes its
boundary term when passing finite Abel estimates to an infinite tail. -/
theorem majorant_moment_boundary_zero {σ : ℝ} (hσ : 1 < σ) (k : ℕ) :
    Filter.Tendsto (fun n : ℕ ↦ Arithmetic.mangoldtMomentWeight σ k n * chebyshevMajorant43 n)
      Filter.atTop (nhds 0) := by
  have h := chebyshev_envelopes_eventually_le.mono (fun x hx ↦ hx.1)
  exact (moment_boundary_tendsto hσ k chebyshevMajorant43 h).comp tendsto_natCast_atTop_atTop

/-- For `σ > 1`, the lower Chebyshev envelope multiplied by the moment
weight tends to zero at the natural upper endpoints, preserving the lower
Abel estimate in the infinite-tail limit. -/
theorem minorant_moment_boundary_zero {σ : ℝ} (hσ : 1 < σ) (k : ℕ) :
    Filter.Tendsto (fun n : ℕ ↦ Arithmetic.mangoldtMomentWeight σ k n * chebyshevMinorant43 n)
      Filter.atTop (nhds 0) := by
  have h := chebyshev_envelopes_eventually_le.mono (fun x hx ↦ hx.2)
  exact (moment_boundary_tendsto hσ k chebyshevMinorant43 h).comp tendsto_natCast_atTop_atTop

/-- Under RH and the stated Rosser-type zero-count estimate, the limits of
the two envelope integrals bound the infinite Mangoldt moment tail. The
upper boundary terms vanish for `σ > 1`; the two integral limits remain
explicit hypotheses. -/
theorem mangoldt_tail_bounds_of_integrals (hRH : RiemannHypothesis) {σ a Il Iu : ℝ} (k : ℕ)
    (ha : 0 < a) (hL : 43 ≤ Real.log a) (hσ : 1 < σ) (hk : (k : ℝ) ≤ σ * Real.log a)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t))
    (hlo :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ t in Set.Ioc a (n : ℝ),
            Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMinorant43 t)
        Filter.atTop (nhds Il))
    (hhi :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ t in Set.Ioc a (n : ℝ),
            Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMajorant43 t)
        Filter.atTop (nhds Iu)) :
    -Arithmetic.mangoldtMomentWeight σ k a * Chebyshev.psi a - Il ≤
        (∑' m : ℕ, Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) -
          ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
            Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m ∧
      (∑' m : ℕ, Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) -
          (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
            Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) ≤
        -Arithmetic.mangoldtMomentWeight σ k a * Chebyshev.psi a - Iu := by
  apply mangoldt_tail_bounds_43 hRH k ha hL hσ hk hQ
  · simpa only [zero_sub, neg_mul] using
      ((minorant_moment_boundary_zero hσ k).sub_const
            (Arithmetic.mangoldtMomentWeight σ k a * Chebyshev.psi a)).sub
        hlo
  · simpa only [zero_sub, neg_mul] using
      ((majorant_moment_boundary_zero hσ k).sub_const
            (Arithmetic.mangoldtMomentWeight σ k a * Chebyshev.psi a)).sub
        hhi

/-- If a real function is integrable above `a`, its integrals on `(a,n]`
converge to the integral over `(a,∞)` as the natural upper endpoint tends to
infinity. Eventually the interval integral has the same orientation. -/
theorem integral_natural_prefix_limit {a : ℝ} (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f (Set.Ioi a)) :
    Filter.Tendsto (fun n : ℕ ↦ ∫ t in Set.Ioc a (n : ℝ), f t) Filter.atTop
      (nhds (∫ t in Set.Ioi a, f t)) := by
  have h :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi a hf
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  apply h.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop).eventually
      (Filter.eventually_ge_atTop a)] with
    n hn
  exact intervalIntegral.integral_of_le hn

/-- Under RH, the stated Rosser-type count estimate, and integrability of
both envelope kernels above `a`, the infinite Mangoldt moment tail lies
between the corresponding improper-integral bounds. The arithmetic
summability and vanishing upper boundary terms are proved independently. -/
theorem mangoldt_tail_bounds_of_integrable (hRH : RiemannHypothesis) {σ a : ℝ} (k : ℕ) (ha : 0 < a)
    (hL : 43 ≤ Real.log a) (hσ : 1 < σ) (hk : (k : ℝ) ≤ σ * Real.log a)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t))
    (hlo :
      MeasureTheory.IntegrableOn
        (fun t ↦ Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMinorant43 t) (Set.Ioi a))
    (hhi :
      MeasureTheory.IntegrableOn
        (fun t ↦ Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMajorant43 t) (Set.Ioi a)) :
    -Arithmetic.mangoldtMomentWeight σ k a * Chebyshev.psi a -
          (∫ t in Set.Ioi a, Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMinorant43 t) ≤
        (∑' m : ℕ, Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) -
          ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
            Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m ∧
      (∑' m : ℕ, Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) -
          (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
            Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) ≤
        -Arithmetic.mangoldtMomentWeight σ k a * Chebyshev.psi a -
          ∫ t in Set.Ioi a, Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMajorant43 t := by
  exact
    mangoldt_tail_bounds_of_integrals hRH k ha hL hσ hk hQ (integral_natural_prefix_limit _ hlo)
      (integral_natural_prefix_limit _ hhi)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
