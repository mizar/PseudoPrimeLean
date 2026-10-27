/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogLowZeros
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogRightPowerWeights

/-! # Low-height regularized zeros below a general real threshold -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a real scale and threshold, combine the origin-regularized left-strip
majorant with `(8+4 log 2) x^sigma`. This bounds both the left strip and the
intermediate strip below the threshold. Its dependence on the scale is sublinear
when the threshold is fixed below one, apart from explicit logarithmic factors. -/
noncomputable def regularizedLowHeightMajorant (x σ : ℝ) : ℝ :=
  2 * Real.sqrt x * (Real.log x) ^ 2 + Real.log 2 * (Real.log x + 1) + (8 + 4 * Real.log 2) * x ^ σ

/-- At scale at least two, the combined low-height majorant is nonnegative for
any real threshold. Each logarithmic, square-root, and real-power factor is
nonnegative. This permits multiplication by the unconditional zero-count bound. -/
theorem regularizedLowHeightMajorant_nonneg {x σ : ℝ} (hx : 2 ≤ x) :
    0 ≤ regularizedLowHeightMajorant x σ := by
  have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  exact
    add_nonneg
      (add_nonneg (mul_nonneg (mul_nonneg (by norm_num only) (Real.sqrt_nonneg x)) (sq_nonneg _))
        (mul_nonneg htwo (by linarith only [hl])))
      (mul_nonneg (by linarith only [htwo]) (Real.rpow_nonneg (by linarith only [hx]) _))

/-- For a primitive nonprincipal character with nonprincipal inverse, scale at
least two, and real part below a threshold at most one, the regularized term is
bounded by its actual multiplicity times the combined low-height majorant.
Split at real part one half: use cancellation near the origin on the left and
the power-weighted kernel on the right. No RH or zero gap is required. -/
theorem norm_regularizedLogHalfZeroTerm_le_below_threshold {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x σ : ℝ}
    (hx : 2 ≤ x) (hσ : σ ≤ 1) {ρ : ℂ} (hre : ρ.re ≤ σ) :
    ‖regularizedLogHalfZeroTerm χ x ρ‖ ≤
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        regularizedLowHeightMajorant x σ := by
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (χ.differentiable_completedLFunction hne).analyticAt z
  have hD : (0 : ℝ) ≤ MeromorphicOn.divisor χ.completedLFunction Set.univ ρ := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have hK : 0 ≤ 8 + 4 * Real.log 2 := by linarith only [hlog2]
  have hleft : 0 ≤ 2 * Real.sqrt x * (Real.log x) ^ 2 + Real.log 2 * (Real.log x + 1) :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num only) (Real.sqrt_nonneg x)) (sq_nonneg _))
      (mul_nonneg hlog2 (by linarith only [hlog]))
  by_cases hh : ρ.re ≤ 1 / 2
  · have hb := norm_regularizedLogHalfZeroTerm_le_low_re hp hne hinv hx hh
    have hright := mul_nonneg hD (mul_nonneg hK (Real.rpow_nonneg (by linarith only [hx]) σ))
    dsimp only [regularizedLowHeightMajorant]
    nlinarith only [hb, hright]
  · have hlo : 1 / 2 ≤ ρ.re := (lt_of_not_ge hh).le
    have hb := norm_regularizedLogHalfZeroTerm_le_right_power_weight hne hx hlo (hre.trans hσ)
    have hdiv : x ^ ρ.re / (1 + ρ.im ^ 2) ≤ x ^ ρ.re :=
      div_le_self (Real.rpow_nonneg (by linarith only [hx]) _) (by nlinarith only [sq_nonneg ρ.im])
    have hpow := Real.rpow_le_rpow_of_exponent_le (by linarith only [hx] : 1 ≤ x) hre
    have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hdiv.trans hpow) hD) hK
    have he := mul_nonneg hD hleft
    dsimp only [regularizedLowHeightMajorant]
    nlinarith only [hb, hm, he]

/-- One positive absolute local-count constant bounds every finite regularized
norm sum below a real threshold at most one and within a natural height.
The character is primitive nonprincipal with nonprincipal inverse, modulus and
scale are at least two. Sum the combined kernel majorant and insert the proved
bounded-height count. This controls the left and intermediate strips uniformly. -/
theorem exists_sum_norm_regularizedLogHalfZeroTerm_below_threshold_bound :
    ∃ K : ℝ,
      0 < K ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ (x σ : ℝ),
                  2 ≤ x →
                    σ ≤ 1 →
                    ∀ (H : ℕ) (S : Finset ℂ),
                      (∀ ρ ∈ S, ρ.re ≤ σ) →
                        (∀ ρ ∈ S, |ρ.im| ≤ H) →
                        ∑ ρ ∈ S, ‖regularizedLogHalfZeroTerm χ x ρ‖ ≤
                          ((2 * (H : ℝ) + 1) * K * (Real.log q + Real.log (4 + (H : ℝ)) + 1)) *
                            regularizedLowHeightMajorant x σ := by
  obtain ⟨K, hK, hcount⟩ := exists_uniform_local_zeroMultiplicity_bound_unconditionally
  refine ⟨K, hK, ?_⟩
  intro q inst hq χ hp hne hinv x σ hx hσ H S hre hh
  have hc :=
    sum_completed_divisor_le_bounded_height_unconditionally hK (hcount q hq χ hp hne hinv) H S hh
  have hb :=
    Finset.sum_le_sum
      (fun ρ hρ ↦ norm_regularizedLogHalfZeroTerm_le_below_threshold hp hne hinv hx hσ (hre ρ hρ))
  rw [← Finset.sum_mul] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hc (regularizedLowHeightMajorant_nonneg hx))

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
