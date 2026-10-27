/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.JointRampPrincipalErrorBounds
public import PseudoPrime.LLS.GammaSignedVariationPrincipalBounds
public import PseudoPrime.LLS.GammaSmoothedPrincipalBounds

/-! # Actual joint ramp-principal bounds preserving common arithmetic errors -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The joint ramp-principal error budget at scale x. It combines the compact envelope with
coefficient 17/10, the paired increment with coefficient 84, and only the remaining affine tail.
This replaces adding separately bounded ramp and principal errors. -/
noncomputable def jointRampPrincipalErrorNumerator (x : ℝ) : ℝ :=
  (17 / 10 : ℝ) *
      (Real.sqrt x / 20 * (63 / 40 : ℝ) + (1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20) +
    84 * rampSmoothedIncrementError x +
    (21 / 100 : ℝ) * (Real.sqrt x / 40 + (1839 / 1000 : ℝ) * Real.log x + 21 / 20) +
    (13 / 16 : ℝ) * (Real.sqrt x / 40 + 1839 / 1000)

/-- Under RH and x at least one, the actual scaled Mangoldt error has its joint functional
bounded uniformly at every principal cutoff beyond the ramp. Supply continuity on that finite
interval, the compact RH envelope, the short-ramp increment and the affine tail envelope.
This transfers common-density cancellation to the arithmetic function. -/
theorem jointRampPrincipal_actual_error_bound (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 ≤ x)
    (hy : (99 / 40 : ℝ) ≤ y) :
    |AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional
          (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) y| ≤
      jointRampPrincipalErrorNumerator x := by
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
  · exact logWeighted_ramp_error_increment hRH hx
  · linarith only [Real.sqrt_nonneg x, Real.log_nonneg hx]
  · linarith only [Real.sqrt_nonneg x]
  · intro u hu
    have he := logWeighted_error_le_exponential_affine hRH hx (show 0 ≤ u by linarith only [hu.1])
    exact he.trans_eq (by ring)

/-- For positive x and nonnegative y, split the logarithmically weighted exponential integral
into its exact main term, endpoint remainder and arithmetic error integral. Use interval
linearity and the quadratic-exponential primitive. This retains the main endpoint sign in the
joint finite-sum transfer. -/
theorem logWeighted_exponential_integral_eq_main_add_error {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    (∫ u in (0 : ℝ)..y,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
          ((u - 1) * Real.exp (-u))) =
      x - x * (y ^ 2 + y + 1) * Real.exp (-y) +
        ∫ u in (0 : ℝ)..y,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            ((u - 1) * Real.exp (-u)) := by
  have hQ : Continuous (fun u : ℝ ↦ (u - 1) * Real.exp (-u)) :=
    (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have hA := AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx y
  rw [← Set.uIcc_of_le hy] at hA
  have hR :
    ContinuousOn (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)
      (Set.uIcc 0 y) :=
    hA.sub (continuous_const.mul continuous_id).continuousOn
  have heq :
    (fun u : ℝ ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
          ((u - 1) * Real.exp (-u))) =
      fun u ↦
      (x * u) * ((u - 1) * Real.exp (-u)) +
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
          ((u - 1) * Real.exp (-u)) := by
    funext u
    ring
  have hM :
    IntervalIntegrable (fun u : ℝ ↦ (x * u) * ((u - 1) * Real.exp (-u))) MeasureTheory.volume 0 y :=
    ((continuous_const.mul continuous_id).mul hQ).intervalIntegrable (0 : ℝ) y
  have hsplit := intervalIntegral.integral_add hM ((hR.mul hQ.continuousOn).intervalIntegrable)
  simp only [Pi.mul_apply] at hsplit
  rw [heq, hsplit]
  have hm :
    (∫ u in (0 : ℝ)..y, (x * u) * ((u - 1) * Real.exp (-u))) =
      x - x * (y ^ 2 + y + 1) * Real.exp (-y) := by
    have he :
      (fun u : ℝ ↦ (x * u) * ((u - 1) * Real.exp (-u))) = fun u ↦
        (0 + (-x) * u + x * u ^ 2) * Real.exp (-u) := by
      funext u; ring
    rw [he, Analysis.integral_exponential_quadratic]
    ring
  rw [hm]

/-- Under RH and x at least one, an upper cap on the arithmetic exponential integral beyond
any fixed cutoff bounds every finite exponential Mangoldt sum. Enlarge the cutoff above the
finite index, keep the boundary term, and let its polynomial-exponential envelope decay.
This requires an eventual integral estimate, not a bound at all small cutoffs. -/
theorem exponentialMangoldtSum_upper_of_eventual_integral_cap (hRH : RiemannHypothesis) {x E : ℝ}
    (hx : 1 ≤ x) (y0 : ℝ)
    (hI :
      ∀ y : ℝ,
        0 ≤ y →
          y0 ≤ y →
          (∫ u in (0 : ℝ)..y,
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
                ((u - 1) * Real.exp (-u))) ≤
            x + E)
    (N : ℕ) : AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (N : ℝ) ≤ x + E := by
  have hx0 := zero_lt_one.trans_le hx
  have ht := (tendsto_exponential_boundary_zero x).const_add (x + E)
  rw [add_zero] at ht
  apply ge_of_tendsto ht
  apply
    ((Filter.eventually_ge_atTop (max 0 y0)).and (Filter.eventually_ge_atTop ((N : ℝ) / x))).mono
  intro y hy
  have hy0 : 0 ≤ y := (le_max_left 0 y0).trans hy.1
  have hgate : y0 ≤ y := (le_max_right 0 y0).trans hy.1
  have hcut : (N : ℝ) ≤ x * y := by simpa only [mul_comm] using (div_le_iff₀ hx0).mp hy.2
  have hm :
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (N : ℝ) ≤
      AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (x * y) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hcut))
      (fun n _ _ ↦ mul_nonneg (Real.exp_pos _).le ArithmeticFunction.vonMangoldt_nonneg)
  have hb :
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (x * y) ≤
      x + E + ((4 * x + x ^ 2) * y ^ 2 + 4 * y) * Real.exp (-y) := by
    rw [AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum_eq_logWeighted_integral hx0 hy0]
    have ht := mul_nonneg hx0.le hy0
    have hA :=
      mul_le_mul_of_nonneg_left (logWeightedMangoldtSum_le_four_add_four hRH ht)
        (mul_nonneg hy0 (Real.exp_pos (-y)).le)
    have hP :=
      mul_le_mul_of_nonneg_left (AnalyticNumberTheory.Arithmetic.psi_le_self_sq ht)
        (Real.exp_pos (-y)).le
    nlinarith only [hI y hy0 hgate, hA, hP]
  exact hm.trans hb

/-- Under RH and x at least one, every finite exponential Mangoldt sum is bounded by x plus
twice the actual ramp error and the joint error budget. Use the lower side of the joint
functional norm bound, the exact main integral and the eventual-cutoff transfer. This preserves
the same ramp error through the passage to the principal series. -/
theorem exponentialMangoldtSum_upper_joint_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (N : ℕ) :
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (N : ℝ) ≤
      x +
        (2 *
            AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
              (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) +
          jointRampPrincipalErrorNumerator x) := by
  apply exponentialMangoldtSum_upper_of_eventual_integral_cap hRH hx (99 / 40)
  intro y hy0 hy
  rw [logWeighted_exponential_integral_eq_main_add_error (zero_lt_one.trans_le hx) hy0]
  have hb := (abs_le.mp (jointRampPrincipal_actual_error_bound hRH hx hy)).1
  dsimp only [AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional,
    Analysis.exponentialRampVariationLeft] at hb
  have ht : 0 ≤ x * (y ^ 2 + y + 1) * Real.exp (-y) := by
    apply mul_nonneg _ (Real.exp_pos _).le
    exact mul_nonneg (zero_lt_one.trans_le hx).le (by nlinarith only [sq_nonneg y, hy0])
  linarith only [hb, ht]

/-- The lower cap on twice the normalized ramp sum minus the principal Gamma sum. Its main
term is (2M-1)sqrt x and its error is the joint budget divided by sqrt x. The cap retains the
cancellation of the common arithmetic error before taking norms. -/
noncomputable def jointRampPrincipalLower (x : ℝ) : ℝ :=
  (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * Real.sqrt x -
    jointRampPrincipalErrorNumerator x / Real.sqrt x

/-- Under RH at any scale at least one, the joint lower cap bounds the actual difference of
twice the normalized ramp sum and the full principal Gamma series. Bound every finite principal
sum using the same ramp error, pass to the summable series, and cancel that error with the exact
ramp identity. This is the common principal input for witness extraction. -/
theorem jointRampPrincipalLower_le_actual (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    jointRampPrincipalLower x ≤
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
        jointRampPrincipalLower x := by
    apply PaperStatements.gamma_level_one_sum_upper_of_finite_upper hx0
    intro N
    have heq := PaperStatements.gamma_level_one_sum_eq_exponential (y := (N : ℝ)) hx0
    rw [Nat.floor_natCast] at heq
    rw [heq]
    apply (div_le_iff₀ hs).mpr
    have hb := exponentialMangoldtSum_upper_joint_error hRH hx N
    have he :
      (2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
            jointRampPrincipalLower x) *
          Real.sqrt x =
        x +
          (2 *
              AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
                (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) +
            jointRampPrincipalErrorNumerator x) := by
      rw [hR]
      dsimp only [jointRampPrincipalLower]
      calc
        _ =
            (Real.sqrt x) ^ 2 +
              2 *
                ((AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
                      (fun u ↦
                        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) /
                    Real.sqrt x) *
                  Real.sqrt x) +
              (jointRampPrincipalErrorNumerator x / Real.sqrt x) * Real.sqrt x :=
          by ring
        _ = _ := by
          rw [Real.sq_sqrt hx0.le, div_mul_cancel₀ _ hs.ne', div_mul_cancel₀ _ hs.ne']
          ring
    exact hb.trans_eq he.symm
  linarith only [hP]

end PseudoPrime.LLS
