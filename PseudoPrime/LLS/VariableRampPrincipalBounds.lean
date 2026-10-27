/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.JointRampPrincipalBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.VariableStencilIncrementBounds

/-! # Variable-width arithmetic error in the joint ramp-principal comparison -/

@[expose] public section

namespace PseudoPrime.LLS

/-- A common RH smoothed-error envelope on the enlarged interval up to (139/40)x.
For x at least one it bounds all three stencil values whenever the width is at most x.
It is used to keep the width free in the Chebyshev comparison. -/
noncomputable def variableRampEnvelope (x : ℝ) : ℝ :=
  Real.sqrt x / 10 + (1839 / 1000 : ℝ) * Real.log ((139 / 40 : ℝ) * x) + 21 / 20

/-- Under RH, x at least one, and positive t at most (139/40)x, the smoothed
Mangoldt error is bounded by the enlarged envelope. Bound sqrt t by 2sqrt x
and use logarithmic monotonicity. This supplies the variable-width stencil. -/
theorem logWeighted_error_le_variable_ramp (hRH : RiemannHypothesis) {x t : ℝ} (hx : 1 ≤ x)
    (ht : 0 < t) (htb : t ≤ (139 / 40 : ℝ) * x) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t| ≤ variableRampEnvelope x := by
  have hx0 := zero_lt_one.trans_le hx
  have he := logWeightedMangoldtSum_error_le_refined_global hRH ht
  have hs : Real.sqrt t ≤ 2 * Real.sqrt x := by
    apply Real.sqrt_le_iff.mpr
    exact
      ⟨mul_nonneg (by norm_num only) (Real.sqrt_nonneg x), by
        nlinarith only [htb, Real.sq_sqrt hx0.le]⟩
  have hmax : max 1 t ≤ (139 / 40 : ℝ) * x := max_le (by linarith only [hx]) htb
  have hl := Real.log_le_log (zero_lt_one.trans_le (le_max_left (1 : ℝ) t)) hmax
  unfold variableRampEnvelope
  linarith only [he, hs, hl]

/-- The short-ramp increment allowance for scale x and positive width h.
Its Chebyshev term is h+2E(x)((99/40)x+h)/h. The ramp width contributes x/200
and the endpoint ratio contributes 1/494. It feeds the joint error budget. -/
noncomputable def variableRampIncrement (x h : ℝ) : ℝ :=
  ((x / 200) + (h + 2 * variableRampEnvelope x * ((99 / 40 : ℝ) * x + h) / h)) / 494

/-- Under RH, x at least one, and width in (0,x], the actual smoothed-error
increment across the ramp is bounded by the variable-width allowance.
Apply the common-envelope stencil and simplify the endpoint ratio.
This connects width selection to the arithmetic function used by witness extraction. -/
theorem logWeighted_error_increment_variable_ramp (hRH : RiemannHypothesis) {x h : ℝ} (hx : 1 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) :
    |(AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (99 / 40)) - x * (99 / 40)) -
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (247 / 100)) -
            x * (247 / 100))| ≤
      variableRampIncrement x h := by
  have hx0 := zero_lt_one.trans_le hx
  have ha : 0 < x * (247 / 100 : ℝ) - h := by nlinarith only [hx, hhx]
  have hab : x * (247 / 100 : ℝ) ≤ x * (99 / 40 : ℝ) := by nlinarith only [hx]
  have hE :
    ∀ t ∈ Set.Icc (x * (247 / 100 : ℝ)) (x * (99 / 40 : ℝ)),
      |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (t - h) - (t - h)| ≤
          variableRampEnvelope x ∧
        |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t| ≤ variableRampEnvelope x ∧
        |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (t + h) - (t + h)| ≤
          variableRampEnvelope x := by
    intro t ht
    have hl : 0 < t - h := by linarith only [ha, ht.1]
    have ht0 : 0 < t := by linarith only [hl, hh]
    exact
      ⟨logWeighted_error_le_variable_ramp hRH hx hl (by nlinarith only [ht.2, hx, hh]),
        logWeighted_error_le_variable_ramp hRH hx ht0 (by nlinarith only [ht.2, hx]),
        logWeighted_error_le_variable_ramp hRH hx (by linarith only [ht0, hh])
          (by nlinarith only [ht.2, hhx])⟩
  have he :=
    AnalyticNumberTheory.Arithmetic.logWeighted_error_increment_le_of_variable_stencil hh ha hab hE
  have hid :
    ((x * (99 / 40 : ℝ) - x * (247 / 100)) +
            (h + 2 * variableRampEnvelope x * (x * (99 / 40) + h) / h)) *
          (x * (99 / 40) - x * (247 / 100)) /
        (x * (247 / 100)) =
      variableRampIncrement x h := by
    unfold variableRampIncrement
    field_simp [hx0.ne', hh.ne']
    ring
  exact he.trans_eq hid

/-- The joint error budget with a freely chosen stencil width h at scale x.
Replace only the short-ramp increment allowance in the existing joint comparison.
The resulting bound retains the common-error cancellation through the principal series. -/
noncomputable def variableRampPrincipalErrorNumerator (x h : ℝ) : ℝ :=
  (17 / 10 : ℝ) *
      (Real.sqrt x / 20 * (63 / 40 : ℝ) + (1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20) +
    84 * variableRampIncrement x h +
    (21 / 100 : ℝ) * (Real.sqrt x / 40 + (1839 / 1000 : ℝ) * Real.log x + 21 / 20) +
    (13 / 16 : ℝ) * (Real.sqrt x / 40 + 1839 / 1000)

/-- Under RH and x at least one, the actual scaled Mangoldt error has its joint functional
bounded uniformly at every principal cutoff beyond the ramp. Supply continuity on that finite
interval, the compact RH envelope, the short-ramp increment and the affine tail envelope.
This transfers common-density cancellation to the arithmetic function. -/
theorem jointRampPrincipal_actual_error_bound_variable_width (hRH : RiemannHypothesis) {x y h : ℝ}
    (hx : 1 ≤ x) (hh : 0 < h) (hhx : h ≤ x) (hy : (99 / 40 : ℝ) ≤ y) :
    |AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional
          (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) y| ≤
      variableRampPrincipalErrorNumerator x h := by
  have hx0 := zero_lt_one.trans_le hx
  have hf :
    ContinuousOn (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)
      (Set.Icc 0 y) :=
    (AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx0 y).sub
      (continuous_const.mul continuous_id).continuousOn
  apply AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional_abs_le hy hf
  · intro u hu
    have hs :=
      mul_le_mul_of_nonneg_left (Analysis.sqrt_le_ramp_right hu.2)
        (div_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 20))
    have he := logWeightedMangoldtSum_scaled_ramp_error hRH hx hu.1 hu.2
    linarith only [he, hs]
  · exact logWeighted_error_increment_variable_ramp hRH hx hh hhx
  · linarith only [Real.sqrt_nonneg x, Real.log_nonneg hx]
  · linarith only [Real.sqrt_nonneg x]
  · intro u hu
    have he := logWeighted_error_le_exponential_affine hRH hx (show 0 ≤ u by linarith only [hu.1])
    exact he.trans_eq (by ring)

/-- Under RH and x at least one, every finite exponential Mangoldt sum is bounded by x plus
twice the actual ramp error and the joint error budget. Use the lower side of the joint
functional norm bound, the exact main integral and the eventual-cutoff transfer. This preserves
the same ramp error through the passage to the principal series. -/
theorem exponentialMangoldtSum_upper_joint_error_variable_width (hRH : RiemannHypothesis) {x h : ℝ}
    (hx : 1 ≤ x) (hh : 0 < h) (hhx : h ≤ x) (N : ℕ) :
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (N : ℝ) ≤
      x +
        (2 *
            AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
              (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) +
          variableRampPrincipalErrorNumerator x h) := by
  apply exponentialMangoldtSum_upper_of_eventual_integral_cap hRH hx (99 / 40)
  intro y hy0 hy
  rw [logWeighted_exponential_integral_eq_main_add_error (zero_lt_one.trans_le hx) hy0]
  have hb := (abs_le.mp (jointRampPrincipal_actual_error_bound_variable_width hRH hx hh hhx hy)).1
  dsimp only [AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional,
    Analysis.exponentialRampVariationLeft] at hb
  have ht : 0 ≤ x * (y ^ 2 + y + 1) * Real.exp (-y) := by
    apply mul_nonneg _ (Real.exp_pos _).le
    exact mul_nonneg (zero_lt_one.trans_le hx).le (by nlinarith only [sq_nonneg y, hy0])
  linarith only [hb, ht]

/-- The lower cap on twice the normalized ramp sum minus the principal Gamma sum. Its main
term is (2M-1)sqrt x and its error is the joint budget divided by sqrt x. The cap retains the
cancellation of the common arithmetic error before taking norms. -/
noncomputable def variableRampPrincipalLower (x h : ℝ) : ℝ :=
  (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * Real.sqrt x -
    variableRampPrincipalErrorNumerator x h / Real.sqrt x

/-- Under RH at any scale at least one, the joint lower cap bounds the actual difference of
twice the normalized ramp sum and the full principal Gamma series. Bound every finite principal
sum using the same ramp error, pass to the summable series, and cancel that error with the exact
ramp identity. This is the common principal input for witness extraction. -/
theorem variableRampPrincipalLower_le_actual (hRH : RiemannHypothesis) {x h : ℝ} (hx : 1 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) :
    variableRampPrincipalLower x h ≤
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' n : ℕ,
            PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  have hx0 := zero_lt_one.trans_le hx
  have hs := Real.sqrt_pos.mpr hx0
  have hR :=
    AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum_normalized_eq_main_add_error hx0
  have hP :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        variableRampPrincipalLower x h := by
    apply PaperStatements.gamma_level_one_sum_upper_of_finite_upper hx0
    intro N
    have heq := PaperStatements.gamma_level_one_sum_eq_exponential (y := (N : ℝ)) hx0
    rw [Nat.floor_natCast] at heq
    rw [heq]
    apply (div_le_iff₀ hs).mpr
    have hb := exponentialMangoldtSum_upper_joint_error_variable_width hRH hx hh hhx N
    have he :
      (2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
            variableRampPrincipalLower x h) *
          Real.sqrt x =
        x +
          (2 *
              AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
                (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) +
            variableRampPrincipalErrorNumerator x h) := by
      rw [hR]
      dsimp only [variableRampPrincipalLower]
      calc
        _ =
            (Real.sqrt x) ^ 2 +
              2 *
                ((AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
                      (fun u ↦
                        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) /
                    Real.sqrt x) *
                  Real.sqrt x) +
              (variableRampPrincipalErrorNumerator x h / Real.sqrt x) * Real.sqrt x :=
          by ring
        _ = _ := by
          rw [Real.sq_sqrt hx0.le, div_mul_cancel₀ _ hs.ne', div_mul_cancel₀ _ hs.ne']
          ring
    exact hb.trans_eq he.symm
  linarith only [hP]

end PseudoPrime.LLS
