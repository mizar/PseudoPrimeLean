/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevBoundary43
import PseudoPrime.Analysis.LogPowerTailIntegral

/-! # Integrability of Chebyshev moment kernels -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `σ > 1` and `t ≥ 1`, an envelope bounded by `2t` turns the absolute
value of the moment-weight derivative times the envelope into two integrable
power-logarithm terms. The estimate keeps both derivative contributions. -/
theorem moment_kernel_bound {σ t : ℝ} (hσ : 1 < σ) (ht : 1 ≤ t) (k : ℕ) (E : ℝ) (hE : ‖E‖ ≤ 2 * t) :
    ‖Arithmetic.mangoldtMomentWeightDeriv σ k t * E‖ ≤
      2 * σ * (Real.log t ^ k * t ^ (-σ)) + 2 * (k : ℝ) * (Real.log t ^ (k - 1) * t ^ (-σ)) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hp : 0 ≤ t ^ (-σ) := Real.rpow_nonneg ht0.le _
  have hp1 : t ^ (-σ - 1) = t ^ (-σ) * t⁻¹ := by
    rw [Real.rpow_sub ht0, Real.rpow_one, div_eq_mul_inv]
  have htD :
    t * Arithmetic.mangoldtMomentWeightDeriv σ k t =
      t ^ (-σ) * (-σ * Real.log t ^ k + (k : ℝ) * Real.log t ^ (k - 1)) := by
    dsimp only [Arithmetic.mangoldtMomentWeightDeriv]
    rw [hp1]
    have htne : t ≠ 0 := ht0.ne'
    field_simp
  have hσ0 : 0 ≤ σ := by linarith only [hσ]
  have ha : 0 ≤ σ * Real.log t ^ k := mul_nonneg hσ0 (pow_nonneg hlog k)
  have hb : 0 ≤ (k : ℝ) * Real.log t ^ (k - 1) := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hlog _)
  have htDabs :
    |t * Arithmetic.mangoldtMomentWeightDeriv σ k t| ≤
      t ^ (-σ) * (σ * Real.log t ^ k + (k : ℝ) * Real.log t ^ (k - 1)) := by
    rw [htD, abs_mul, abs_of_nonneg hp, neg_mul]
    have hh := abs_add_le (-(σ * Real.log t ^ k)) ((k : ℝ) * Real.log t ^ (k - 1))
    rw [abs_neg, abs_of_nonneg ha, abs_of_nonneg hb] at hh
    exact mul_le_mul_of_nonneg_left hh hp
  have hmul :=
    mul_le_mul_of_nonneg_left hE (abs_nonneg (Arithmetic.mangoldtMomentWeightDeriv σ k t))
  rw [norm_mul, Real.norm_eq_abs]
  have htabs :
    |t * Arithmetic.mangoldtMomentWeightDeriv σ k t| =
      t * |Arithmetic.mangoldtMomentWeightDeriv σ k t| := by
    rw [abs_mul, abs_of_nonneg ht0.le]
  rw [htabs] at htDabs
  nlinarith only [hmul, htDabs]

/-- For `σ > 1`, a continuous envelope with eventual linear growth gives an
integrable moment-derivative kernel above any `a ≥ 1`. Compare the far tail
with two integrable power-logarithm functions and use continuity on the
remaining bounded interval. -/
theorem moment_kernel_integrable {σ a : ℝ} (hσ : 1 < σ) (ha : 1 ≤ a) (k : ℕ) (E : ℝ → ℝ)
    (hcont : ContinuousOn E (Set.Ici a)) (hE : ∀ᶠ x : ℝ in Filter.atTop, ‖E x‖ ≤ 2 * x) :
    MeasureTheory.IntegrableOn (fun t ↦ Arithmetic.mangoldtMomentWeightDeriv σ k t * E t)
      (Set.Ioi a) := by
  obtain ⟨d, hd⟩ := Filter.eventually_atTop.mp hE
  let c := max a d
  have hac : a ≤ c := le_max_left _ _
  have hdc : d ≤ c := le_max_right _ _
  have hc1 : 1 ≤ c := ha.trans hac
  have hc0 : 0 < a := zero_lt_one.trans_le ha
  have hD : ContinuousOn (Arithmetic.mangoldtMomentWeightDeriv σ k) (Set.Ici a) := by
    intro t ht
    have hp : 0 < t := lt_of_lt_of_le hc0 ht
    have hl := Real.continuousAt_log hp.ne'
    have hp1 := Real.continuousAt_rpow_const t (-σ - 1) (Or.inl hp.ne')
    have hp2 := Real.continuousAt_rpow_const t (-σ) (Or.inl hp.ne')
    have hi := continuousAt_inv₀ hp.ne'
    exact
      (((continuousAt_const.mul hp1).mul (hl.pow k)).add
          (hp2.mul ((continuousAt_const.mul (hl.pow (k - 1))).mul hi))).continuousWithinAt
  have hF : ContinuousOn (fun t ↦ Arithmetic.mangoldtMomentWeightDeriv σ k t * E t) (Set.Ici a) :=
    hD.mul hcont
  have hr : 0 < σ - 1 := by linarith only [hσ]
  have h1 := Analysis.log_power_tail_integrable hr hc1 k
  have h2 := Analysis.log_power_tail_integrable hr hc1 (k - 1)
  have hexp : -(σ - 1) - 1 = -σ := by ring
  rw [hexp] at h1 h2
  have hg :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦
        2 * σ * (Real.log t ^ k * t ^ (-σ)) + 2 * (k : ℝ) * (Real.log t ^ (k - 1) * t ^ (-σ)))
      (Set.Ioi c) :=
    (h1.const_mul (2 * σ)).add (h2.const_mul (2 * (k : ℝ)))
  have htail :
    MeasureTheory.IntegrableOn (fun t ↦ Arithmetic.mangoldtMomentWeightDeriv σ k t * E t)
      (Set.Ioi c) := by
    apply hg.mono'
    · exact (hF.mono (fun t ht ↦ hac.trans ht.le)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 ≤ t := hc1.trans ht.le
      have hEt := hd t (hdc.trans ht.le)
      exact moment_kernel_bound hσ ht1 k (E t) hEt
  have hlocal :
    MeasureTheory.IntegrableOn (fun t ↦ Arithmetic.mangoldtMomentWeightDeriv σ k t * E t)
      (Set.Ioc a c) := by
    exact ((hF.mono (fun t ht ↦ ht.1)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hu := hlocal.union htail
  rw [Set.Ioc_union_Ioi (show c ≤ max a c from le_max_right _ _), min_eq_left hac] at hu
  exact hu

/-- For `σ > 1` and `log a ≥ 43`, both Chebyshev envelope kernels are
integrable on `(a,∞)`. The envelopes are continuous there and have the
proved eventual linear-growth bound. -/
theorem chebyshev_moment_kernels_integrable {σ a : ℝ} (hσ : 1 < σ) (ha : 0 < a)
    (hL : 43 ≤ Real.log a) (k : ℕ) :
    MeasureTheory.IntegrableOn
        (fun t ↦ Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMinorant43 t) (Set.Ioi a) ∧
      MeasureTheory.IntegrableOn
        (fun t ↦ Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMajorant43 t)
        (Set.Ioi a) := by
  have ha1 : 1 ≤ a := (Real.log_pos_iff ha.le).mp (by linarith only [hL]) |>.le
  have hB :
    ContinuousOn
      (fun t : ℝ ↦
        Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)))
      (Set.Ici a) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht
    have hlog := Real.log_le_log ha ht
    have hl := Real.continuousAt_log ht0.ne'
    have hl0 : Real.log t ≠ 0 := ne_of_gt (by linarith only [hL, hlog])
    have hll := (Real.continuousAt_log hl0).comp hl
    exact
      (Real.continuous_sqrt.continuousAt.mul
          ((hl.mul (hl.sub hll)).div_const (8 * Real.pi))).continuousWithinAt
  have hminor : ContinuousOn chebyshevMinorant43 (Set.Ici a) := by exact continuousOn_id.sub hB
  have hmajor : ContinuousOn chebyshevMajorant43 (Set.Ici a) := by exact continuousOn_id.add hB
  have hlow := chebyshev_envelopes_eventually_le.mono (fun x hx ↦ hx.2)
  have hhigh := chebyshev_envelopes_eventually_le.mono (fun x hx ↦ hx.1)
  exact
    ⟨moment_kernel_integrable hσ ha1 k chebyshevMinorant43 hminor hlow,
      moment_kernel_integrable hσ ha1 k chebyshevMajorant43 hmajor hhigh⟩

/-- Under RH and the stated Rosser-type count estimate, the infinite
power-logarithm Mangoldt moment tail is bounded by the two Chebyshev envelope
integrals when `σ > 1`, `log a ≥ 43`, and the weight is decreasing above `a`.
The boundary convergence and both integrability conditions are proved; the
Rosser-type count estimate remains an explicit hypothesis. -/
theorem mangoldt_tail_bounds_43_complete (hRH : RiemannHypothesis) {σ a : ℝ} (k : ℕ) (ha : 0 < a)
    (hL : 43 ≤ Real.log a) (hσ : 1 < σ) (hk : (k : ℝ) ≤ σ * Real.log a)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
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
  have h := chebyshev_moment_kernels_integrable hσ ha hL k
  exact mangoldt_tail_bounds_of_integrable hRH k ha hL hσ hk hQ h.1 h.2

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
