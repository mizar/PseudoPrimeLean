/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevKernelIntegrable
public import PseudoPrime.Analysis.LogPowerTailIntegral

/-! # Explicit moment integrals for a logarithm-square envelope -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On positive inputs, multiplying the moment-weight derivative by the
Chebyshev main term gives two power-logarithm kernels. This identity prepares
the exact improper integral used in the tail estimate. -/
theorem moment_deriv_mul_id (σ : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Arithmetic.mangoldtMomentWeightDeriv σ k t * t =
      -σ * (Real.log t ^ k * t ^ (-σ)) + (k : ℝ) * (Real.log t ^ (k - 1) * t ^ (-σ)) := by
  have hp : t ^ (-σ - 1) = t ^ (-σ) * t⁻¹ := by rw [Real.rpow_sub ht, Real.rpow_one, div_eq_mul_inv]
  dsimp only [Arithmetic.mangoldtMomentWeightDeriv]
  rw [hp]
  have htne : t ≠ 0 := ht.ne'
  field_simp

/-- For `σ > 1` and `a ≥ 1`, evaluate the integral of the moment derivative
against the Chebyshev main term using the existing logarithmic tail
polynomials. The zero-degree case is included through the coefficient `k`. -/
theorem moment_main_integral {σ a : ℝ} (hσ : 1 < σ) (ha : 1 ≤ a) (k : ℕ) :
    (∫ t in Set.Ioi a, Arithmetic.mangoldtMomentWeightDeriv σ k t * t) =
      -σ * (a ^ (-(σ - 1)) * Analysis.logPowerTailPoly (σ - 1) k (Real.log a)) +
        (k : ℝ) * (a ^ (-(σ - 1)) * Analysis.logPowerTailPoly (σ - 1) (k - 1) (Real.log a)) := by
  have hr : 0 < σ - 1 := by linarith only [hσ]
  have h1 := Analysis.log_power_tail_integrable hr ha k
  have h2 := Analysis.log_power_tail_integrable hr ha (k - 1)
  have he : -(σ - 1) - 1 = -σ := by ring
  rw [he] at h1 h2
  have hi1 := Analysis.log_power_tail_integral hr ha k
  have hi2 := Analysis.log_power_tail_integral hr ha (k - 1)
  rw [he] at hi1 hi2
  have heq :
    (∫ t in Set.Ioi a, Arithmetic.mangoldtMomentWeightDeriv σ k t * t) =
      ∫ t in Set.Ioi a,
        -σ * (Real.log t ^ k * t ^ (-σ)) + (k : ℝ) * (Real.log t ^ (k - 1) * t ^ (-σ)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact moment_deriv_mul_id σ k (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) (ha.trans ht.le))
  rw [heq, MeasureTheory.integral_add (h1.const_mul (-σ)) (h2.const_mul (k : ℝ)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hi1, hi2]

/-- On positive inputs, the moment derivative multiplied by `sqrt t log² t`
is a sum of two power-logarithm kernels. Separate degree zero to preserve the
natural-number subtraction in the derivative. -/
theorem moment_deriv_mul_logsq (σ : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Arithmetic.mangoldtMomentWeightDeriv σ k t * (Real.sqrt t * Real.log t ^ 2) =
      -σ * (Real.log t ^ (k + 2) * t ^ (-σ - 1 / 2)) +
        (k : ℝ) * (Real.log t ^ (k + 1) * t ^ (-σ - 1 / 2)) := by
  have hp : t ^ (-σ) * t⁻¹ = t ^ (-σ - 1) := by rw [Real.rpow_sub ht, Real.rpow_one, div_eq_mul_inv]
  have hpow : t ^ (-σ - 1) * t ^ (1 / 2 : ℝ) = t ^ (-σ - 1 / 2) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  dsimp only [Arithmetic.mangoldtMomentWeightDeriv]
  rw [Real.sqrt_eq_rpow, ← hpow, ← hp]
  cases k with
  | zero =>
    norm_num only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.zero_add, pow_zero, mul_one]
    ring
  | succ k =>
    simp only [Nat.succ_sub_one, pow_add, pow_one]
    ring

/-- For `σ > 1` and `a ≥ 1`, evaluate the integral of the moment derivative
against `sqrt t log² t`. The two logarithmic tail polynomials retain the
separate degrees from differentiating the original moment weight. -/
theorem moment_logsq_integral {σ a : ℝ} (hσ : 1 < σ) (ha : 1 ≤ a) (k : ℕ) :
    (∫ t in Set.Ioi a,
        Arithmetic.mangoldtMomentWeightDeriv σ k t * (Real.sqrt t * Real.log t ^ 2)) =
      -σ * (a ^ (-(σ - 1 / 2)) * Analysis.logPowerTailPoly (σ - 1 / 2) (k + 2) (Real.log a)) +
        (k : ℝ) *
          (a ^ (-(σ - 1 / 2)) * Analysis.logPowerTailPoly (σ - 1 / 2) (k + 1) (Real.log a)) := by
  have hr : 0 < σ - 1 / 2 := by linarith only [hσ]
  have h1 := Analysis.log_power_tail_integrable hr ha (k + 2)
  have h2 := Analysis.log_power_tail_integrable hr ha (k + 1)
  have he : -(σ - 1 / 2) - 1 = -σ - 1 / 2 := by ring
  rw [he] at h1 h2
  have hi1 := Analysis.log_power_tail_integral hr ha (k + 2)
  have hi2 := Analysis.log_power_tail_integral hr ha (k + 1)
  rw [he] at hi1 hi2
  have heq :
    (∫ t in Set.Ioi a,
        Arithmetic.mangoldtMomentWeightDeriv σ k t * (Real.sqrt t * Real.log t ^ 2)) =
      ∫ t in Set.Ioi a,
        -σ * (Real.log t ^ (k + 2) * t ^ (-σ - 1 / 2)) +
          (k : ℝ) * (Real.log t ^ (k + 1) * t ^ (-σ - 1 / 2)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact
      moment_deriv_mul_logsq σ k (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) (ha.trans ht.le))
  rw [heq, MeasureTheory.integral_add (h1.const_mul (-σ)) (h2.const_mul (k : ℝ)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hi1, hi2]

/-- For `σ > 1` and `a ≥ 1`, the moment derivative multiplied by either
`t` or `sqrt t log² t` is integrable above `a`. Rewrite both kernels as
finite sums of the existing integrable power-logarithm functions. -/
theorem moment_simple_kernels_integrable {σ a : ℝ} (hσ : 1 < σ) (ha : 1 ≤ a) (k : ℕ) :
    MeasureTheory.IntegrableOn (fun t ↦ Arithmetic.mangoldtMomentWeightDeriv σ k t * t)
        (Set.Ioi a) ∧
      MeasureTheory.IntegrableOn
        (fun t ↦ Arithmetic.mangoldtMomentWeightDeriv σ k t * (Real.sqrt t * Real.log t ^ 2))
        (Set.Ioi a) := by
  have hr : 0 < σ - 1 := by linarith only [hσ]
  have hr2 : 0 < σ - 1 / 2 := by linarith only [hσ]
  have h1 := Analysis.log_power_tail_integrable hr ha k
  have h2 := Analysis.log_power_tail_integrable hr ha (k - 1)
  have h3 := Analysis.log_power_tail_integrable hr2 ha (k + 2)
  have h4 := Analysis.log_power_tail_integrable hr2 ha (k + 1)
  have he1 : -(σ - 1) - 1 = -σ := by ring
  have he2 : -(σ - 1 / 2) - 1 = -σ - 1 / 2 := by ring
  rw [he1] at h1 h2
  rw [he2] at h3 h4
  have hm :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦ -σ * (Real.log t ^ k * t ^ (-σ)) + (k : ℝ) * (Real.log t ^ (k - 1) * t ^ (-σ)))
      (Set.Ioi a) :=
    (h1.const_mul (-σ)).add (h2.const_mul (k : ℝ))
  have he :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦
        -σ * (Real.log t ^ (k + 2) * t ^ (-σ - 1 / 2)) +
          (k : ℝ) * (Real.log t ^ (k + 1) * t ^ (-σ - 1 / 2)))
      (Set.Ioi a) :=
    (h3.const_mul (-σ)).add (h4.const_mul (k : ℝ))
  constructor
  · apply hm.congr_fun ?_ measurableSet_Ioi
    intro t ht
    exact
      (moment_deriv_mul_id σ k
          (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) (ha.trans ht.le))).symm
  · apply he.congr_fun ?_ measurableSet_Ioi
    intro t ht
    exact
      (moment_deriv_mul_logsq σ k
          (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) (ha.trans ht.le))).symm

/-- At logarithmic scale at least 43, the existing Chebyshev envelopes lie
inside the simpler pair `t ± sqrt(t) log²(t)/(8π)`. The discarded
`log log t` contribution is nonnegative. -/
theorem chebyshev_envelopes_logsq {t : ℝ} (hL : 43 ≤ Real.log t) :
    chebyshevMajorant43 t ≤ t + Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi) ∧
      t - Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi) ≤ chebyshevMinorant43 t := by
  have hlog : 1 ≤ Real.log t := by linarith only [hL]
  have hll : 0 ≤ Real.log (Real.log t) := Real.log_nonneg hlog
  have hp : 0 ≤ Real.log t * Real.log (Real.log t) := mul_nonneg (by linarith only [hlog]) hll
  have hs := Real.sqrt_nonneg t
  have hpi : 0 ≤ 8 * Real.pi := mul_nonneg (by norm_num only) Real.pi_pos.le
  have hd := div_nonneg (mul_nonneg hs hp) hpi
  dsimp only [chebyshevMajorant43, chebyshevMinorant43]
  simp only [div_eq_mul_inv] at hd ⊢
  constructor <;> nlinarith only [hd]

/-- For `σ > 1` and `a ≥ 1`, integrate the moment derivative against the
simple upper and lower logarithm-square envelopes. Linearity separates each
integral into the main-term integral and the signed error-term integral. -/
theorem moment_simple_envelope_integrals {σ a : ℝ} (hσ : 1 < σ) (ha : 1 ≤ a) (k : ℕ) :
    let M := ∫ t in Set.Ioi a, Arithmetic.mangoldtMomentWeightDeriv σ k t * t
    let R :=
      (∫ t in Set.Ioi a,
          Arithmetic.mangoldtMomentWeightDeriv σ k t * (Real.sqrt t * Real.log t ^ 2)) /
        (8 * Real.pi)
    (∫ t in Set.Ioi a,
          Arithmetic.mangoldtMomentWeightDeriv σ k t *
            (t + Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi))) =
        M + R ∧
      (∫ t in Set.Ioi a,
          Arithmetic.mangoldtMomentWeightDeriv σ k t *
            (t - Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi))) =
        M - R := by
  dsimp only
  have hI := moment_simple_kernels_integrable hσ ha k
  have hdiv :
    MeasureTheory.IntegrableOn
      (fun t ↦
        (Arithmetic.mangoldtMomentWeightDeriv σ k t * (Real.sqrt t * Real.log t ^ 2)) /
          (8 * Real.pi))
      (Set.Ioi a) :=
    hI.2.div_const _
  have heq1 :
    (∫ t in Set.Ioi a,
        Arithmetic.mangoldtMomentWeightDeriv σ k t *
          (t + Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi))) =
      ∫ t in Set.Ioi a,
        Arithmetic.mangoldtMomentWeightDeriv σ k t * t +
          (Arithmetic.mangoldtMomentWeightDeriv σ k t * (Real.sqrt t * Real.log t ^ 2)) /
            (8 * Real.pi) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    ring
  have heq2 :
    (∫ t in Set.Ioi a,
        Arithmetic.mangoldtMomentWeightDeriv σ k t *
          (t - Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi))) =
      ∫ t in Set.Ioi a,
        Arithmetic.mangoldtMomentWeightDeriv σ k t * t -
          (Arithmetic.mangoldtMomentWeightDeriv σ k t * (Real.sqrt t * Real.log t ^ 2)) /
            (8 * Real.pi) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    ring
  constructor
  · rw [heq1, MeasureTheory.integral_add hI.1 hdiv, MeasureTheory.integral_div]
  · rw [heq2, MeasureTheory.integral_sub hI.1 hdiv, MeasureTheory.integral_div]

/-- For `σ > 1` and `a ≥ 1`, the moment derivative multiplied by either
simple logarithm-square envelope is integrable above `a`. Split each product
into its integrable main and error kernels. -/
theorem moment_simple_envelopes_integrable {σ a : ℝ} (hσ : 1 < σ) (ha : 1 ≤ a) (k : ℕ) :
    MeasureTheory.IntegrableOn
        (fun t ↦
          Arithmetic.mangoldtMomentWeightDeriv σ k t *
            (t + Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi)))
        (Set.Ioi a) ∧
      MeasureTheory.IntegrableOn
        (fun t ↦
          Arithmetic.mangoldtMomentWeightDeriv σ k t *
            (t - Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi)))
        (Set.Ioi a) := by
  have hI := moment_simple_kernels_integrable hσ ha k
  have hdiv :
    MeasureTheory.IntegrableOn
      (fun t ↦
        (Arithmetic.mangoldtMomentWeightDeriv σ k t * (Real.sqrt t * Real.log t ^ 2)) /
          (8 * Real.pi))
      (Set.Ioi a) :=
    hI.2.div_const _
  constructor
  · apply (hI.1.add hdiv).congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.add_apply]
    ring
  · apply (hI.1.sub hdiv).congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.sub_apply]
    ring

/-- When the moment weight decreases above `a`, its derivative reverses the
pointwise comparisons between the original Chebyshev envelopes and the
simpler logarithm-square envelopes. The resulting improper integrals exist
and compare in the directions needed for the tail bounds. -/
theorem moment_envelope_integrals_compare {σ a : ℝ} (hσ : 1 < σ) (ha : 0 < a) (hL : 43 ≤ Real.log a)
    (k : ℕ) (hk : (k : ℝ) ≤ σ * Real.log a) :
    (∫ t in Set.Ioi a,
          Arithmetic.mangoldtMomentWeightDeriv σ k t *
            (t + Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi))) ≤
        (∫ t in Set.Ioi a, Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMajorant43 t) ∧
      (∫ t in Set.Ioi a, Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMinorant43 t) ≤
        (∫ t in Set.Ioi a,
          Arithmetic.mangoldtMomentWeightDeriv σ k t *
            (t - Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi))) := by
  have ha1 : 1 ≤ a := (Real.log_pos_iff ha.le).mp (by linarith only [hL]) |>.le
  have hs := moment_simple_envelopes_integrable hσ ha1 k
  have hc := chebyshev_moment_kernels_integrable hσ ha hL k
  have hd : ∀ t ∈ Set.Ioi a, Arithmetic.mangoldtMomentWeightDeriv σ k t ≤ 0 := by
    intro t ht
    have hlog := Real.log_le_log ha ht.le
    have hm := mul_le_mul_of_nonneg_left hlog (le_of_lt (zero_lt_one.trans hσ))
    exact
      Arithmetic.mangoldt_moment_deriv_nonpos k (le_of_lt (zero_lt_one.trans hσ)) (ha1.trans ht.le)
        (hk.trans hm)
  constructor
  · apply MeasureTheory.setIntegral_mono_on hs.1 hc.2 measurableSet_Ioi
    intro t ht
    have hlog := Real.log_le_log ha ht.le
    have hp := chebyshev_envelopes_logsq (t := t) (by linarith only [hL, hlog])
    exact mul_le_mul_of_nonpos_left hp.1 (hd t ht)
  · apply MeasureTheory.setIntegral_mono_on hc.1 hs.2 measurableSet_Ioi
    intro t ht
    have hlog := Real.log_le_log ha ht.le
    have hp := chebyshev_envelopes_logsq (t := t) (by linarith only [hL, hlog])
    exact mul_le_mul_of_nonpos_left hp.2 (hd t ht)

/-- Under RH and the stated Rosser-type zero-count estimate, a decreasing
power-logarithm Mangoldt tail above logarithmic scale 43 lies between the two
displayed expressions. The improper integrals are evaluated using finite
tail polynomials; the count estimate remains an explicit hypothesis. -/
theorem mangoldt_tail_explicit_43 (hRH : RiemannHypothesis) {σ a : ℝ} (k : ℕ) (ha : 0 < a)
    (hL : 43 ≤ Real.log a) (hσ : 1 < σ) (hk : (k : ℝ) ≤ σ * Real.log a)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    let M :=
      -σ * (a ^ (-(σ - 1)) * Analysis.logPowerTailPoly (σ - 1) k (Real.log a)) +
        (k : ℝ) * (a ^ (-(σ - 1)) * Analysis.logPowerTailPoly (σ - 1) (k - 1) (Real.log a))
    let R :=
      -σ * (a ^ (-(σ - 1 / 2)) * Analysis.logPowerTailPoly (σ - 1 / 2) (k + 2) (Real.log a)) +
        (k : ℝ) * (a ^ (-(σ - 1 / 2)) * Analysis.logPowerTailPoly (σ - 1 / 2) (k + 1) (Real.log a))
    let S :=
      (∑' m : ℕ, Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) -
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
          Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m)
    (-Arithmetic.mangoldtMomentWeight σ k a * Chebyshev.psi a - M + R / (8 * Real.pi) ≤ S) ∧
      (S ≤ -Arithmetic.mangoldtMomentWeight σ k a * Chebyshev.psi a - M - R / (8 * Real.pi)) := by
  dsimp only
  have ha1 : 1 ≤ a := (Real.log_pos_iff ha.le).mp (by linarith only [hL]) |>.le
  have hb := mangoldt_tail_bounds_43_complete hRH k ha hL hσ hk hQ
  have hc := moment_envelope_integrals_compare hσ ha hL k hk
  have hi := moment_simple_envelope_integrals hσ ha1 k
  dsimp only at hi
  rw [hi.1, hi.2] at hc
  rw [moment_main_integral hσ ha1 k, moment_logsq_integral hσ ha1 k] at hc
  constructor
  · linarith only [hb.1, hc.2]
  · linarith only [hb.2, hc.1]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
