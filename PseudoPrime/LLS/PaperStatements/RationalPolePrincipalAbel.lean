/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPolePrincipalWeight
public import PseudoPrime.LLS.RiemannChebyshevNumericalBounds
public import PseudoPrime.LLS.PaperStatements.PsiWeightedError

/-! # Scaled principal weights and their finite Mangoldt sums -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The actual fourth-pole weight at `t/x`, normalized by `sqrt x`, for principal sums. -/
noncomputable def fourScaledWeight (x t : ℝ) : ℝ :=
  fourPoleKernelWeight (t / x) / Real.sqrt x

/-- The chain-rule derivative of the scaled weight on its positive interior support. -/
noncomputable def fourScaledWeightDeriv (x t : ℝ) : ℝ :=
  fourPoleWeightDeriv (t / x) / (x * Real.sqrt x)

/-- The explicit derivative is continuous at every positive argument. -/
theorem fourPoleWeightDeriv_continuousAt {u : ℝ} (hu : 0 < u) :
    ContinuousAt fourPoleWeightDeriv u := by
  have hv := (fourPoleCoord_hasDerivAt hu).continuousAt
  have he : ContinuousAt (fun t ↦ Real.exp (-fourPoleCoord t)) u :=
    Real.continuous_exp.continuousAt.comp hv.neg
  have hden : ContinuousAt (fun t : ℝ ↦ 6 * t * Real.sqrt t) u :=
    (continuousAt_const.mul continuousAt_id).mul Real.continuous_sqrt.continuousAt
  have hp : (6 * u * Real.sqrt u : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num only) hu.ne') (Real.sqrt_pos.mpr hu).ne'
  change
    ContinuousAt
      (fun t : ℝ ↦
        Real.exp (-fourPoleCoord t) / (6 * t * Real.sqrt t) *
          ((6 / 13) * fourPoleCoord t ^ 3 - (75 / 26) * fourPoleCoord t ^ 2))
      u
  exact
    (he.div hden hp).mul
      ((continuousAt_const.mul (hv.pow 3)).sub (continuousAt_const.mul (hv.pow 2)))

/-- Below the unit cutoff, the actual kernel weight has the explicit scaled derivative. -/
theorem fourScaledWeight_hasDerivAt {x t : ℝ} (hx : 0 < x) (ht : 0 < t) (htx : t ≤ x) :
    HasDerivAt (fourScaledWeight x) (fourScaledWeightDeriv x t) t := by
  have hu := div_pos ht hx
  have hl : Real.log (t / x) < 28 / 25 :=
    (Real.log_nonpos hu.le ((div_le_one hx).mpr htx)).trans_lt (by norm_num only)
  have h :=
    ((fourPoleKernelWeight_hasDerivAt hu hl).comp t ((hasDerivAt_id t).div_const x)).div_const
      (Real.sqrt x)
  convert h using 1
  · rfl
  · dsimp only [fourScaledWeightDeriv]
    ring

/-- On `[2,x]` with `x ≥ 2`, the scaled weight has an integrable derivative. -/
theorem fourScaledWeight_deriv_integrable {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (deriv (fourScaledWeight x)) (Set.Icc 2 x) := by
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have hd : ContinuousOn (fourScaledWeightDeriv x) (Set.Icc 2 x) := by
    intro t ht
    have ht0 : 0 < t := (by norm_num only : (0 : ℝ) < 2).trans_le ht.1
    have h :=
      ContinuousAt.comp (g := fourPoleWeightDeriv) (f := fun t : ℝ ↦ t / x)
        (fourPoleWeightDeriv_continuousAt (div_pos ht0 hx0))
        (continuous_id.div_const x).continuousAt
    exact (h.div_const (x * Real.sqrt x)).continuousWithinAt
  apply hd.integrableOn_Icc.congr_fun ?_ measurableSet_Icc
  intro t ht
  exact
    (fourScaledWeight_hasDerivAt hx0 ((by norm_num only : (0 : ℝ) < 2).trans_le ht.1)
        ht.2).deriv.symm

/-- Under RH, the actual scaled finite principal sum has an explicit Abel error.
The lower endpoint correction remains visible until the missing interval is integrated. -/
theorem fourScaledWeight_mangoldt_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
          (∫ t : ℝ in (2 : ℝ)..x, fourScaledWeight x t) -
          2 * fourScaledWeight x 2| ≤
      13 *
        (x ^ (3 / 4 : ℝ) * |fourScaledWeight x x| +
          ∫ t : ℝ in (2 : ℝ)..x, t ^ (3 / 4 : ℝ) * |deriv (fourScaledWeight x) t|) := by
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  exact
    mangoldt_weighted_error hx
      (fun t ht ↦
        (fourScaledWeight_hasDerivAt hx0 ((by norm_num only : (0 : ℝ) < 2).trans_le ht.1)
            ht.2).differentiableAt)
      (fourScaledWeight_deriv_integrable hx)
      (fun t ht ↦ LLS.psi_error_le_thirteen hRH (by linarith only [ht.1]))

/-- On the positive support, the actual principal weight lies between zero and ten.
An elementary exponential estimate controls its cubic logarithmic factor uniformly. -/
theorem fourPoleKernelWeight_bounds {u : ℝ} (hu : 0 < u) (hl : Real.log u ≤ 28 / 25) :
    0 ≤ fourPoleKernelWeight u ∧ fourPoleKernelWeight u ≤ 10 := by
  have hv : 0 ≤ fourPoleCoord u := by
    dsimp only [fourPoleCoord]
    linarith only [hl]
  have hEq : fourPoleKernelWeight u = fourPoleWeight u := fourPoleKernelWeight_eq hu hl
  rw [hEq]
  constructor
  · dsimp only [fourPoleWeight]
    exact
      div_nonneg (mul_nonneg (pow_nonneg hv 3) (Real.exp_nonneg _))
        (mul_nonneg (by norm_num only) (Real.sqrt_nonneg _))
  · have he :
      Real.exp (-fourPoleCoord u) / Real.sqrt u =
        Real.exp (-(14 / 25 : ℝ)) * Real.exp (-((12 / 25 : ℝ) * fourPoleCoord u)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu, ← Real.exp_sub, ← Real.exp_add]
      congr 1
      dsimp only [fourPoleCoord]
      ring
    have hn :
      fourPoleWeight u =
        (Real.exp (-(14 / 25 : ℝ)) / 6) *
          (fourPoleCoord u ^ 3 * Real.exp (-((12 / 25 : ℝ) * fourPoleCoord u))) := by
      dsimp only [fourPoleWeight]
      calc
        _ = (fourPoleCoord u ^ 3 / 6) * (Real.exp (-fourPoleCoord u) / Real.sqrt u) := by ring
        _ = _ := by
          rw [he]; ring
    have ht :=
      Real.pow_div_factorial_le_exp ((12 / 25 : ℝ) * fourPoleCoord u)
        (mul_nonneg (by norm_num only) hv) 3
    norm_num only [Nat.factorial, Nat.cast_ofNat] at ht
    have hm := mul_le_mul_of_nonneg_right ht (Real.exp_pos (-((12 / 25 : ℝ) * fourPoleCoord u))).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
    have hp :
      fourPoleCoord u ^ 3 * Real.exp (-((12 / 25 : ℝ) * fourPoleCoord u)) ≤
        6 / (12 / 25 : ℝ) ^ 3 := by
      nlinarith only [hm]
    have hc : Real.exp (-(14 / 25 : ℝ)) / 6 ≤ 1 / 6 :=
      div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (by norm_num only)) (by norm_num only)
    rw [hn]
    exact
      (mul_le_mul hc hp (mul_nonneg (pow_nonneg hv 3) (Real.exp_nonneg _)) (by norm_num only)).trans
        (by norm_num only)

/-- For `x ≥ 2`, the lower endpoint correction is at most `20 / sqrt x`. -/
theorem fourScaledWeight_lower_endpoint {x : ℝ} (hx : 2 ≤ x) :
    |2 * fourScaledWeight x 2| ≤ 20 / Real.sqrt x := by
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have hu : 0 < 2 / x := div_pos (by norm_num only) hx0
  have hl : Real.log (2 / x) ≤ 28 / 25 :=
    (Real.log_nonpos hu.le ((div_le_one hx0).mpr hx)).trans (by norm_num only)
  have hb := fourPoleKernelWeight_bounds hu hl
  have hs : 0 ≤ fourScaledWeight x 2 := div_nonneg hb.1 (Real.sqrt_nonneg x)
  rw [abs_of_nonneg (mul_nonneg (by norm_num only) hs)]
  dsimp only [fourScaledWeight]
  calc
    2 * (fourPoleKernelWeight (2 / x) / Real.sqrt x) =
        (2 * fourPoleKernelWeight (2 / x)) / Real.sqrt x :=
      by ring
    _ ≤ 20 / Real.sqrt x :=
      div_le_div_of_nonneg_right (by linarith only [hb.2]) (Real.sqrt_nonneg x)

/-- Under RH, the finite principal sum differs from its integral on `[2,x]` by
the weighted variation error and an explicit lower endpoint budget. -/
theorem fourScaledWeight_principal_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
          (∫ t : ℝ in (2 : ℝ)..x, fourScaledWeight x t)| ≤
      13 *
          (x ^ (3 / 4 : ℝ) * |fourScaledWeight x x| +
            ∫ t : ℝ in (2 : ℝ)..x, t ^ (3 / 4 : ℝ) * |deriv (fourScaledWeight x) t|) +
        20 / Real.sqrt x := by
  have he := fourScaledWeight_mangoldt_error hRH hx
  have hb := fourScaledWeight_lower_endpoint hx
  have ht :=
    abs_add_le
      ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
        (∫ t : ℝ in (2 : ℝ)..x, fourScaledWeight x t) -
        2 * fourScaledWeight x 2)
      (2 * fourScaledWeight x 2)
  rw [sub_add_cancel] at ht
  exact ht.trans (add_le_add he hb)

end PseudoPrime.LLS.PaperStatements
