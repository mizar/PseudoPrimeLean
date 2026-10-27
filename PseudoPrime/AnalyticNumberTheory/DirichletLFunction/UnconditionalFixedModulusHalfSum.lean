/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalFixedZeroLimits
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogRemainderBound
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-! # Unconditional small arithmetic errors at a fixed character modulus -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a fixed primitive nonprincipal character, the origin-free logarithmic
half-scale remainder divided by the scale tends to zero. Squeeze its norm using
the absolute `C(log x+1)` bound and the logarithmic decay limit. No zero-free
region or RH is required. -/
theorem tendsto_regularized_logarithmicHalfRemainder_div_scale {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) :
    Filter.Tendsto
      (fun x : ℝ ↦
        (logarithmicHalfRemainder hne x -
            (Real.log 2 : ℂ) *
              (logDeriv χ.completedLFunction 2 - logDeriv χ.completedLFunction 0)) /
          (x : ℂ))
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hC, hrem⟩ := exists_norm_regularized_logarithmicHalfRemainder_le_log
  have hlog : Filter.Tendsto (fun x : ℝ ↦ Real.log x / x) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hbound : Filter.Tendsto (fun x : ℝ ↦ C * (Real.log x + 1) / x) Filter.atTop (nhds 0) := by
    have h := (hlog.add tendsto_inv_atTop_zero).const_mul C
    simp only [zero_add, mul_zero] at h
    convert h using 1
    funext x
    ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun x ↦ norm_nonneg _)) ?_ hbound
  filter_upwards [Filter.eventually_ge_atTop (4 : ℝ)] with x hx
  have hxpos : 0 < x := by linarith only [hx]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxpos.le]
  exact div_le_div_of_nonneg_right (hrem q χ hp hne x hx) hxpos.le

/-- For a fixed primitive nonprincipal character with nonprincipal inverse and
modulus at least two, the half-scale arithmetic sum is `o(x)`. Combine the exact
regularized formula with dominated convergence of its zero sum and the normalized
remainder limit. This supplies fixed small conductors independently of the
quantitative exceptional-conductor argument. -/
theorem tendsto_characterLogWeightedSum_half_div_scale_unconditionally {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Filter.Tendsto
      (fun x : ℝ ↦
        (Arithmetic.characterLogWeightedSum x χ - Arithmetic.characterLogWeightedSum (x / 2) χ) /
          (x : ℂ))
      Filter.atTop (nhds 0) := by
  have hz := tendsto_tsum_regularizedLogHalfZeroTerm_div_scale_unconditionally hq hp hne hinv
  have hr := tendsto_regularized_logarithmicHalfRemainder_div_scale hp hne
  have ht := hz.neg.add hr
  have heq :
    (fun x : ℝ ↦
        (Arithmetic.characterLogWeightedSum x χ - Arithmetic.characterLogWeightedSum (x / 2) χ) /
          (x : ℂ)) =ᶠ[Filter.atTop]
      (fun x ↦
        -((∑' ρ : ℂ, regularizedLogHalfZeroTerm χ x ρ) / (x : ℂ)) +
          (logarithmicHalfRemainder hne x -
              (Real.log 2 : ℂ) *
                (logDeriv χ.completedLFunction 2 - logDeriv χ.completedLFunction 0)) /
            (x : ℂ)) := by
    filter_upwards [Filter.eventually_gt_atTop (2 : ℝ)] with x hx
    rw [characterLogWeightedSum_half_regularized_formula_unconditionally hq hp hne hinv hx, add_div,
      neg_div]
  simpa only [neg_zero, add_zero] using ht.congr' heq.symm

/-- For a fixed modulus at least two and any positive error rate, one real
threshold works for every primitive nonprincipal character with nonprincipal
inverse at that modulus. Take the normalized arithmetic limit for each character
and intersect the finitely many eventual bounds. The threshold may depend on
the modulus and error rate, but not on the character or scale. -/
theorem exists_uniform_fixed_modulus_half_sum_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ X : ℝ,
      1 ≤ X ∧
        ∀ x : ℝ,
          X ≤ x →
            ∀ χ : DirichletCharacter ℂ q,
              χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ‖Arithmetic.characterLogWeightedSum x χ -
                      Arithmetic.characterLogWeightedSum (x / 2) χ‖ ≤
                  ε * x := by
  classical
  have hχ (χ : DirichletCharacter ℂ q) :
    ∀ᶠ x : ℝ in Filter.atTop,
      χ.IsPrimitive →
        χ ≠ 1 →
        χ⁻¹ ≠ 1 →
        ‖Arithmetic.characterLogWeightedSum x χ - Arithmetic.characterLogWeightedSum (x / 2) χ‖ ≤
          ε * x := by
    by_cases hg : χ.IsPrimitive ∧ χ ≠ 1 ∧ χ⁻¹ ≠ 1
    · obtain ⟨hp, hne, hinv⟩ := hg
      have hn :=
        (tendsto_characterLogWeightedSum_half_div_scale_unconditionally hq hp hne hinv).norm
      simp only [norm_zero] at hn
      have he := hn.eventually (gt_mem_nhds hε)
      filter_upwards [he, Filter.eventually_ge_atTop (1 : ℝ)] with x he hx
      intro _ _ _
      have hxpos : 0 < x := zero_lt_one.trans_le hx
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxpos.le] at he
      exact ((div_lt_iff₀ hxpos).mp he).le
    · exact Filter.Eventually.of_forall (fun _ hp hne hinv ↦ (hg ⟨hp, hne, hinv⟩).elim)
  have hall := Filter.eventually_all.mpr hχ
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hall
  exact
    ⟨max 1 X, le_max_left _ _, fun x hx χ hp hne hinv ↦
      hX x ((le_max_right _ _).trans hx) χ hp hne hinv⟩

/-- For every positive error rate, all primitive nonprincipal complex characters
modulo four have half-scale arithmetic sums bounded by that rate times the scale
past one threshold. Apply the fixed-modulus theorem and derive nonprincipality of
the inverse. This permits erasing conductor four from the quantitative exceptional
set while retaining its actual arithmetic contribution without RH. -/
theorem exists_uniform_conductor_four_half_sum_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ,
      1 ≤ X ∧
        ∀ x : ℝ,
          X ≤ x →
            ∀ χ : DirichletCharacter ℂ 4,
              χ.IsPrimitive →
                χ ≠ 1 →
                ‖Arithmetic.characterLogWeightedSum x χ -
                      Arithmetic.characterLogWeightedSum (x / 2) χ‖ ≤
                  ε * x := by
  obtain ⟨X, hX, hbound⟩ :=
    exists_uniform_fixed_modulus_half_sum_bound (by norm_num only : 2 ≤ 4) hε
  exact ⟨X, hX, fun x hx χ hp hne ↦ hbound x hx χ hp hne (inv_ne_one.mpr hne)⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
