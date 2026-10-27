/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalOrdinaryHorizontal
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogHorizontalEdge

/-! # Unconditional logarithmic horizontal contour-edge limits -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Ordinary logarithmic-derivative envelopes at both signs of a positive height
give simultaneous logarithmic contour-kernel bounds on the central strip.
Apply the positive-imaginary pointwise estimate and rewrite the negative square.
This permits reusing any unconditional good-height sequence. -/
theorem logKernel_central_signed_point_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {x σ T η : ℝ} (hx : 1 ≤ x) (hσ : |σ| ≤ 2) (hT : 0 < T)
    (hplus : ‖logDeriv χ.LFunction ((σ : ℂ) + T * Complex.I)‖ / T ^ 2 ≤ η)
    (hminus : ‖logDeriv χ.LFunction ((σ : ℂ) - T * Complex.I)‖ / T ^ 2 ≤ η) :
    ‖dirichletLogContourKernel x χ ((σ : ℂ) + T * Complex.I)‖ ≤ x ^ 2 * η ∧
      ‖dirichletLogContourKernel x χ ((σ : ℂ) - T * Complex.I)‖ ≤ x ^ 2 * η := by
  have hform : (σ : ℂ) - (T : ℂ) * Complex.I = (σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  refine ⟨norm_dirichletLogContourKernel_horizontal_le hx hσ hT.ne' hplus, ?_⟩
  rw [hform] at hminus ⊢
  apply norm_dirichletLogContourKernel_horizontal_le hx hσ (neg_ne_zero.mpr hT.ne')
  simpa only [neg_sq] using hminus

/-- A uniform far-left ordinary logarithmic-derivative estimate gives simultaneous
logarithmic-kernel bounds at both signs of a height at least one. Reflect the
negative height and apply the existing pointwise kernel inequality. This handles
the part of a fixed contour to the left of the central strip without RH. -/
theorem logKernel_farLeft_signed_point_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (A : ℕ)
    (D : ℝ)
    (hD :
      ∀ σ t : ℝ,
        -(A : ℝ) - 1 / 2 ≤ σ →
          σ ≤ -2 → 1 ≤ |t| → ‖logDeriv χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D * (|t| + 1))
    {x σ T : ℝ} (hx : 1 ≤ x) (hσlo : -(A : ℝ) - 1 / 2 ≤ σ) (hσhi : σ ≤ -2) (hT : 1 ≤ T) :
    ‖dirichletLogContourKernel x χ ((σ : ℂ) + T * Complex.I)‖ ≤ D * (T + 1) / T ^ 2 ∧
      ‖dirichletLogContourKernel x χ ((σ : ℂ) - T * Complex.I)‖ ≤ D * (T + 1) / T ^ 2 := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hform : (σ : ℂ) - (T : ℂ) * Complex.I = (σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hplus := hD σ T hσlo hσhi (by rwa [abs_of_nonneg hTpos.le])
  rw [abs_of_nonneg hTpos.le] at hplus
  refine
    ⟨norm_dirichletLogContourKernel_farLeft_le hx hσhi hTpos.ne'
        (div_le_div_of_nonneg_right hplus (sq_nonneg T)),
      ?_⟩
  have hminus := hD σ (-T) hσlo hσhi (by rwa [abs_neg, abs_of_nonneg hTpos.le])
  rw [abs_neg, abs_of_nonneg hTpos.le] at hminus
  rw [hform]
  apply norm_dirichletLogContourKernel_farLeft_le hx hσhi (neg_ne_zero.mpr hTpos.ne')
  simpa only [neg_sq] using div_le_div_of_nonneg_right hminus (sq_nonneg T)

/-- A primitive nonprincipal character with nonprincipal inverse has one height
sequence tending to infinity along which both logarithmic horizontal contour edges
vanish on every fixed interval from a negative half-integer to two, for every
positive real scale at least one. The central completed edges remain nonzero.
Combine the unconditional ordinary envelope with the far-left functional-equation
bound and integrate a common majorant tending to zero.
This removes GRH from the horizontal-edge limit needed by smoothed explicit formulas. -/
theorem exists_unconditional_logKernel_horizontal_height_limits {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∃ T : ℕ → ℝ,
      Filter.Tendsto T Filter.atTop Filter.atTop ∧
        (∀ k : ℕ,
          (k : ℝ) + 1 ≤ T k ∧
            ∀ σ : ℝ,
              |σ| ≤ 2 →
                χ.completedLFunction ((σ : ℂ) + T k * Complex.I) ≠ 0 ∧
                  χ.completedLFunction ((σ : ℂ) - T k * Complex.I) ≠ 0) ∧
        ∀ (A : ℕ),
          2 ≤ A →
            ∀ x : ℝ,
              1 ≤ x →
                Filter.Tendsto
                    (fun k : ℕ ↦
                      ∫ σ in (-(A : ℝ) - 1 / 2)..2,
                        dirichletLogContourKernel x χ ((σ : ℂ) + T k * Complex.I))
                    Filter.atTop (nhds 0) ∧
                  Filter.Tendsto
                    (fun k : ℕ ↦
                      ∫ σ in (-(A : ℝ) - 1 / 2)..2,
                        dirichletLogContourKernel x χ ((σ : ℂ) - T k * Complex.I))
                    Filter.atTop (nhds 0) := by
  obtain ⟨T, η, hT, hη, hspec⟩ :=
    exists_unconditional_ordinary_horizontal_height_sequence hq hp hne hinv
  have hTk (k : ℕ) : 1 ≤ T k := (le_add_of_nonneg_left (Nat.cast_nonneg k)).trans (hspec k).1
  have hηnonneg (k : ℕ) : 0 ≤ η k :=
    (div_nonneg (norm_nonneg _) (sq_nonneg _)).trans ((hspec k).2 0 (by norm_num only)).1
  refine ⟨T, hT, ?_, ?_⟩
  · intro k
    exact ⟨(hspec k).1, fun σ hσ ↦ ⟨((hspec k).2 σ hσ).2.2.1, ((hspec k).2 σ hσ).2.2.2⟩⟩
  · intro A hA x hx
    obtain ⟨D, hDnonneg, hD⟩ :=
      exists_norm_logDeriv_dirichletLFunction_farLeft_le_general A hp hne hinv
    let μ := fun k : ℕ ↦ D * (T k + 1) / (T k) ^ 2
    have hμ : Filter.Tendsto μ Filter.atTop (nhds 0) := by
      have h := tendsto_constant_add_linear_div_sq T hT 0 D (le_refl 0) hDnonneg
      simpa only [zero_div, zero_add, μ] using h
    have hμnonneg (k : ℕ) : 0 ≤ μ k :=
      div_nonneg (mul_nonneg hDnonneg (by linarith only [hTk k])) (sq_nonneg _)
    have hkernel (k : ℕ) (σ : ℝ) (hσ : σ ∈ Set.uIoc (-(A : ℝ) - 1 / 2) 2) :
      ‖dirichletLogContourKernel x χ ((σ : ℂ) + T k * Complex.I)‖ ≤ x ^ 2 * η k + μ k ∧
        ‖dirichletLogContourKernel x χ ((σ : ℂ) - T k * Complex.I)‖ ≤ x ^ 2 * η k + μ k := by
      have hAreal : (2 : ℝ) ≤ A := by exact_mod_cast hA
      rw [Set.uIoc_of_le (by linarith only [hAreal])] at hσ
      by_cases hcentral : -2 ≤ σ
      · have hpoint :=
          logKernel_central_signed_point_bound hx (abs_le.mpr ⟨hcentral, hσ.2⟩)
            (zero_lt_one.trans_le (hTk k)) ((hspec k).2 σ (abs_le.mpr ⟨hcentral, hσ.2⟩)).1
            ((hspec k).2 σ (abs_le.mpr ⟨hcentral, hσ.2⟩)).2.1
        exact
          ⟨hpoint.1.trans (le_add_of_nonneg_right (hμnonneg k)),
            hpoint.2.trans (le_add_of_nonneg_right (hμnonneg k))⟩
      · have hpoint :=
          logKernel_farLeft_signed_point_bound A D hD hx hσ.1.le (le_of_lt (lt_of_not_ge hcentral))
            (hTk k)
        have hηx := mul_nonneg (sq_nonneg x) (hηnonneg k)
        exact
          ⟨hpoint.1.trans (le_add_of_nonneg_left hηx), hpoint.2.trans (le_add_of_nonneg_left hηx)⟩
    let L := |(2 : ℝ) - (-(A : ℝ) - 1 / 2)|
    have hbound (k : ℕ) :
      ‖∫ σ in (-(A : ℝ) - 1 / 2)..2, dirichletLogContourKernel x χ ((σ : ℂ) + T k * Complex.I)‖ ≤
          (x ^ 2 * η k + μ k) * L ∧
        ‖∫ σ in (-(A : ℝ) - 1 / 2)..2, dirichletLogContourKernel x χ ((σ : ℂ) - T k * Complex.I)‖ ≤
          (x ^ 2 * η k + μ k) * L :=
      ⟨intervalIntegral.norm_integral_le_of_norm_le_const (fun σ hσ ↦ (hkernel k σ hσ).1),
        intervalIntegral.norm_integral_le_of_norm_le_const (fun σ hσ ↦ (hkernel k σ hσ).2)⟩
    have henvelope :
      Filter.Tendsto (fun k : ℕ ↦ (x ^ 2 * η k + μ k) * L) Filter.atTop (nhds 0) := by
      have h := ((hη.const_mul (x ^ 2)).add hμ).mul_const L
      simpa only [mul_zero, add_zero, zero_mul] using h
    exact
      ⟨squeeze_zero_norm (fun k ↦ (hbound k).1) henvelope,
        squeeze_zero_norm (fun k ↦ (hbound k).2) henvelope⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
