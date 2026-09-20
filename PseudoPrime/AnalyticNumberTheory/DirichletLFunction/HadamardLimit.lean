/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Meromorphic.LogDeriv
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Base
import PseudoPrime.AnalyticNumberTheory.General.CanonicalDecomposition
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Growth
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroCounting
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogDerivBound

/-!
# Ball-envelope growth for `completedLFunction`

Assembles `PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_completedLFunction_le` (`Re s ≥
1/2`) and `PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_completedLFunction_lt_half_le`
(`Re s < 1/2`) into a single `R`-only envelope
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunctionBallBound N R`, valid on the
whole closed ball `‖z‖ ≤ R`. It is the input to the Jensen zero-counting step.
The two branches have genuinely different shapes (the reflected factor
`N^{1/2 - Re s}` only appears for `Re s < 1/2`), so the envelope is built as the *sum* of each
branch's own bound rather than by forcing one uniform shape: on a given `z`, only one branch's
term matters, and the other is discarded via nonnegativity.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The common exponential growth factor `exp((x+2)log(x+2))` is monotone for `x ≥ 0`. -/
theorem expLog_two_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.exp ((x + 2) * Real.log (x + 2)) ≤ Real.exp ((y + 2) * Real.log (y + 2)) :=
  Real.exp_le_exp.mpr (Gamma.mul_log_mono_of_one_le (by linarith) (by linarith))

/-- An envelope for completed `L` on `‖z‖ ≤ R`, depending only on the level `N` and radius.
It adds the right-half-plane bound at norm `R` and the reflected bound using
`‖1-z‖ ≤ R+1` and `1/2-Re z ≤ R+1`. The next theorem supplies its hypotheses. -/
noncomputable def completedLFunctionBallBound (N : ℕ) (R : ℝ) : ℝ :=
  2 * N * R * (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 2) * Real.log (R + 2)))) +
    (N : ℝ) ^ (R + 1) * N * (2 * N * (R + 1)) *
      (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 3) * Real.log (R + 3))))

/-- For a primitive nontrivial character at level `N > 1`, with nontrivial inverse, the
completed `L`-function on `‖z‖ ≤ R`, `R ≥ 0`, is bounded by `completedLFunctionBallBound N R`.
Split at `Re z = 1/2`, apply the two growth bounds from `Growth`, and use monotonicity
and the triangle inequality to replace the point-dependent quantities by radius bounds. -/
theorem norm_completedLFunction_le_completedLFunctionBallBound {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {z : ℂ}
    {R : ℝ} (hR : 0 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖DirichletCharacter.completedLFunction χ z‖ ≤ completedLFunctionBallBound N R := by
  unfold completedLFunctionBallBound
  rcases lt_or_ge z.re (1 / 2 : ℝ) with hzre | hzre
  · have hb := norm_completedLFunction_lt_half_le hN1 hprimitive hinv hzre
    have hzre_ge : -R ≤ z.re := by
      have h1 : -‖z‖ ≤ z.re := neg_le_of_abs_le (Complex.abs_re_le_norm z)
      linarith
    have h1z : (1 : ℝ) / 2 - z.re ≤ R + 1 := by linarith
    have h1zpow : (N : ℝ) ^ (1 / 2 - z.re) ≤ (N : ℝ) ^ (R + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1.le) h1z
    have hnorm1z : ‖(1 : ℂ) - z‖ ≤ R + 1 := by
      have h1 : ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le 1 z
      rw [norm_one] at h1
      linarith
    have hexpstep :
      Real.exp ((‖(1 : ℂ) - z‖ + 2) * Real.log (‖(1 : ℂ) - z‖ + 2)) ≤
        Real.exp ((R + 3) * Real.log (R + 3)) :=
      Real.exp_le_exp.mpr
        (Gamma.mul_log_mono_of_one_le (by linarith [norm_nonneg ((1 : ℂ) - z)]) (by linarith))
    have h1 : (2 : ℝ) * N * ‖(1 : ℂ) - z‖ ≤ 2 * N * (R + 1) :=
      mul_le_mul_of_nonneg_left hnorm1z (by positivity)
    have e1 :
      (2 : ℝ) * N * ‖(1 : ℂ) - z‖ *
          (Real.pi ^ (-(1 : ℝ) / 4) *
            (4 * Real.exp ((‖(1 : ℂ) - z‖ + 2) * Real.log (‖(1 : ℂ) - z‖ + 2)))) =
        (2 * (N : ℝ) * ‖(1 : ℂ) - z‖) * (Real.pi ^ (-(1 : ℝ) / 4) * 4) *
          Real.exp ((‖(1 : ℂ) - z‖ + 2) * Real.log (‖(1 : ℂ) - z‖ + 2)) := by
      ring
    have e2 :
      (2 : ℝ) * N * (R + 1) *
          (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 3) * Real.log (R + 3)))) =
        (2 * (N : ℝ) * (R + 1)) * (Real.pi ^ (-(1 : ℝ) / 4) * 4) *
          Real.exp ((R + 3) * Real.log (R + 3)) := by
      ring
    have h2 :
      (2 : ℝ) * N * ‖(1 : ℂ) - z‖ *
          (Real.pi ^ (-(1 : ℝ) / 4) *
            (4 * Real.exp ((‖(1 : ℂ) - z‖ + 2) * Real.log (‖(1 : ℂ) - z‖ + 2)))) ≤
        2 * N * (R + 1) *
          (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 3) * Real.log (R + 3)))) := by
      rw [e1, e2]
      exact
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) hexpstep (Real.exp_pos _).le
          (by positivity)
    have hstep :
      (N : ℝ) ^ (1 / 2 - z.re) * N *
          (2 * N * ‖(1 : ℂ) - z‖ *
            (Real.pi ^ (-(1 : ℝ) / 4) *
              (4 * Real.exp ((‖(1 : ℂ) - z‖ + 2) * Real.log (‖(1 : ℂ) - z‖ + 2))))) ≤
        (N : ℝ) ^ (R + 1) * N *
          (2 * N * (R + 1) *
            (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 3) * Real.log (R + 3))))) :=
      mul_le_mul (mul_le_mul_of_nonneg_right h1zpow (by positivity)) h2 (by positivity)
        (by positivity)
    have e3 :
      (N : ℝ) ^ (R + 1) * N *
          (2 * N * (R + 1) *
            (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 3) * Real.log (R + 3))))) =
        (N : ℝ) ^ (R + 1) * N * (2 * N * (R + 1)) *
          (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 3) * Real.log (R + 3)))) := by
      ring
    rw [e3] at hstep
    exact hb.trans (hstep.trans (le_add_of_nonneg_left (by positivity)))
  · have hb := norm_completedLFunction_le hN1 hne hzre
    have h1 : (2 : ℝ) * (N : ℝ) * ‖z‖ ≤ 2 * (N : ℝ) * R :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    have h2 : Real.exp ((‖z‖ + 2) * Real.log (‖z‖ + 2)) ≤ Real.exp ((R + 2) * Real.log (R + 2)) :=
      expLog_two_mono (norm_nonneg z) hz
    have e1 :
      2 * (N : ℝ) * ‖z‖ *
          (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((‖z‖ + 2) * Real.log (‖z‖ + 2)))) =
        (2 * (N : ℝ) * ‖z‖) * (Real.pi ^ (-(1 : ℝ) / 4) * 4) *
          Real.exp ((‖z‖ + 2) * Real.log (‖z‖ + 2)) := by
      ring
    have e2 :
      2 * (N : ℝ) * R * (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 2) * Real.log (R + 2)))) =
        (2 * (N : ℝ) * R) * (Real.pi ^ (-(1 : ℝ) / 4) * 4) *
          Real.exp ((R + 2) * Real.log (R + 2)) := by
      ring
    have hstep :
      2 * (N : ℝ) * ‖z‖ *
          (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((‖z‖ + 2) * Real.log (‖z‖ + 2)))) ≤
        2 * (N : ℝ) * R *
          (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 2) * Real.log (R + 2)))) := by
      rw [e1, e2]
      exact
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h2 (Real.exp_pos _).le
          (by positivity)
    exact hb.trans (hstep.trans (le_add_of_nonneg_right (by positivity)))

/-! ### Jensen zero-counting

`AnalyticOnNhd.sum_divisor_le` bounds the zero count using the ball envelope and the
nonzero central value. No quantitative separation from zeros is required here.
-/

/-- For a primitive nontrivial character at level `N > 1`, with nontrivial inverse and `R > 0`,
Jensen's inequality bounds the multiplicity sum on `closedBall 0 R`. Apply it on the doubled
ball using `norm_completedLFunction_le_completedLFunctionBallBound` and nonvanishing at zero. -/
theorem finsum_divisor_completedLFunction_le {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 0 < R) :
    ∑ᶠ u,
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) R) u ≤
      Real.log
          (max 1 (completedLFunctionBallBound N (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 := by
  have hzero := dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have h2Rpos : (0 : ℝ) < 2 * R := by linarith
  have hanalytic :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) |2 * R|) :=
    fun z _ => hdiff.analyticAt z
  have hbound :
    ∀ z ∈ Metric.sphere (0 : ℂ) |2 * R|,
      ‖DirichletCharacter.completedLFunction χ z‖ ≤
        max 1 (completedLFunctionBallBound N (2 * R)) := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right, abs_of_pos h2Rpos] at hz
    exact
      le_max_of_le_right
        (norm_completedLFunction_le_completedLFunctionBallBound hN1 hprimitive hne hinv
          (by linarith) hz.le)
  have hjensen :=
    AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ)) (r := R) (R := 2 * R) (M :=
      max 1 (completedLFunctionBallBound N (2 * R))) (abs_pos.mpr hR.ne')
      (by
        rw [abs_of_pos hR, abs_of_pos h2Rpos]; linarith)
      (le_max_left 1 _) hanalytic hzero hbound
  rwa [abs_of_pos hR, show 2 * R / R = 2 from by field_simp] at hjensen

/-! ### Domain-independence of the divisor for the entire function `completedLFunction χ` -/

/-- `MeromorphicOn.divisor` of the entire function `completedLFunction χ` at a point `ρ` does not
depend on which set `U ∋ ρ` it is computed on: it is always the local `analyticOrderAt` (no
openness of `U` is needed, since `completedLFunction χ` is analytic at every point of `ℂ`). -/
theorem divisor_completedLFunction_domain_eq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {U : Set ℂ} {ρ : ℂ} (hρ : ρ ∈ U) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U ρ =
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hAnU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) U := fun z _ =>
    hdiff.analyticAt z
  have hAnV : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ =>
    hdiff.analyticAt z
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAnU hρ,
    MeromorphicOn.AnalyticOnNhd.divisor_apply hAnV (Set.mem_univ ρ)]

/-- Pointwise, the divisor of `completedLFunction χ` on the open ball `ball 0 R` is at most its
divisor on the closed ball `closedBall 0 R`: on the ball the two agree (domain-independence), and
elsewhere the closed-ball divisor is still `≥ 0`. -/
theorem divisor_completedLFunction_ball_le_closedBall {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {R : ℝ} (u : ℂ) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) u ≤
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R)
        u := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hAnClosed :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  by_cases hu : u ∈ Metric.ball (0 : ℂ) R
  · have heqBall := divisor_completedLFunction_domain_eq hne hu
    have heqClosed := divisor_completedLFunction_domain_eq hne (Metric.ball_subset_closedBall hu)
    rw [heqBall, heqClosed]
  · have hzero :
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) u =
        0 :=
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball (0 : ℂ) R)).apply_eq_zero_of_notMem
        hu
    rw [hzero]
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnClosed u

/-- The open-ball analogue of
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.finsum_divisor_completedLFunction_le`: the
multiplicity-counted
zero count of `completedLFunction χ` inside `ball 0 R` is bounded by the same explicit expression,
via the pointwise domination
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.divisor_completedLFunction_ball_le_closedBall`.
-/
theorem finsum_divisor_ball_completedLFunction_le {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 0 < R) :
    ∑ᶠ u,
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) u ≤
      Real.log
          (max 1 (completedLFunctionBallBound N (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 := by
  have hfinBall :=
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.ball (0 : ℂ) R)).finiteSupport
  have hfinClosed :=
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) R)).finiteSupport
      (isCompact_closedBall (x := (0 : ℂ)) (r := R))
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hAnClosed :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  have hfin :
    (Function.support
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.ball (0 : ℂ) R))).Finite :=
    hAnClosed.meromorphicOn.divisor_ball_support_finite
  have hstep :
    ∑ᶠ u,
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) u ≤
      ∑ᶠ u,
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) R) u :=
    finsum_le_finsum hfin hfinClosed (fun u => divisor_completedLFunction_ball_le_closedBall hne u)
  exact
    (Int.cast_le.mpr hstep).trans (finsum_divisor_completedLFunction_le hN1 hprimitive hne hinv hR)

/-! ### Exponential envelope

To derive a zero count of order `R log R`, bound each factor in `completedLFunctionBallBound`
by an exponential and combine them using `Real.exp_add`. This gives the explicit constant
`4N + 3` in the exponent for `N ≥ 2` and `R ≥ 1`.
-/

/-- `x ≤ exp x`, elementary consequence of `Real.add_one_le_exp`. -/
theorem le_self_exp (x : ℝ) : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]

/-- `1 ≤ log(R+3)` for `R ≥ 1` (since `R + 3 ≥ 4 > 3 > exp 1`). -/
theorem one_le_log_add_three {R : ℝ} (hR : 1 ≤ R) : 1 ≤ Real.log (R + 3) := by
  have h1 : Real.exp 1 < R + 3 := lt_of_lt_of_le Real.exp_one_lt_three (by linarith)
  have h2 : (1 : ℝ) < Real.log (R + 3) := by
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) h1
  linarith

/-- **The exponential envelope**:
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunctionBallBound N R ≤
exp((4N+3)(R+3)log(R+3))`
for `R ≥ 1`. -/
theorem completedLFunctionBallBound_le_exp {N : ℕ} (hN2 : 2 ≤ N) {R : ℝ} (hR : 1 ≤ R) :
    completedLFunctionBallBound N R ≤
      Real.exp ((4 * (N : ℝ) + 3) * ((R + 3) * Real.log (R + 3))) := by
  have hL1 : (1 : ℝ) ≤ Real.log (R + 3) := one_le_log_add_three hR
  have hR3 : (4 : ℝ) ≤ R + 3 := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set X : ℝ := (R + 3) * Real.log (R + 3) with hX_def
  have hX4 : (4 : ℝ) ≤ X := by
    calc
      (4 : ℝ) = 4 * 1 := by ring
      _ ≤ (R + 3) * Real.log (R + 3) := mul_le_mul hR3 hL1 (by norm_num only) (by linarith)
  have hCpos : Real.pi ^ (-(1 : ℝ) / 4) * 4 < 4 := by
    have h1 : Real.pi ^ (-(1 : ℝ) / 4) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith [Real.pi_gt_three]) (by norm_num only)
    nlinarith [Real.rpow_pos_of_pos Real.pi_pos (-(1 : ℝ) / 4)]
  -- T1 = A * (C * exp((R+2)log(R+2))), A := 2NR, C := π^{-1/4}*4
  have hA1 : (2 : ℝ) * N * R ≤ Real.exp (2 * (N : ℝ) * X) := by
    refine le_trans ?_ (le_self_exp _)
    calc
      (2 : ℝ) * N * R ≤ 2 * N * (R + 3) := by nlinarith
      _ ≤ 2 * N * X := by
        nlinarith [mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ R + 3)]
  have hC1 :
    Real.pi ^ (-(1 : ℝ) / 4) * 4 * Real.exp ((R + 2) * Real.log (R + 2)) ≤ Real.exp (2 * X) := by
    have hQ1 : Real.exp ((R + 2) * Real.log (R + 2)) ≤ Real.exp X := by
      apply Real.exp_le_exp.mpr
      rw [hX_def]
      exact Gamma.mul_log_mono_of_one_le (by linarith) (by linarith)
    have hCexp : Real.pi ^ (-(1 : ℝ) / 4) * 4 ≤ Real.exp X :=
      le_trans hCpos.le (le_trans hX4 (le_self_exp X))
    calc
      Real.pi ^ (-(1 : ℝ) / 4) * 4 * Real.exp ((R + 2) * Real.log (R + 2)) ≤
          Real.exp X * Real.exp X :=
        mul_le_mul hCexp hQ1 (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (2 * X) := by
        rw [← Real.exp_add]; ring_nf
  have hT1 :
    2 * (N : ℝ) * R * (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 2) * Real.log (R + 2)))) ≤
      Real.exp ((2 * (N : ℝ) + 2) * X) := by
    have heq :
      Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 2) * Real.log (R + 2))) =
        Real.pi ^ (-(1 : ℝ) / 4) * 4 * Real.exp ((R + 2) * Real.log (R + 2)) := by
      ring
    rw [heq]
    calc
      2 * (N : ℝ) * R * (Real.pi ^ (-(1 : ℝ) / 4) * 4 * Real.exp ((R + 2) * Real.log (R + 2))) ≤
          Real.exp (2 * (N : ℝ) * X) * Real.exp (2 * X) :=
        mul_le_mul hA1 hC1 (by positivity) (Real.exp_pos _).le
      _ = Real.exp ((2 * (N : ℝ) + 2) * X) := by
        rw [← Real.exp_add]; ring_nf
  -- T2 = (N^(R+1) * N * (2N(R+1))) * (C * exp((R+3)log(R+3)))
  have hA2 : (N : ℝ) ^ (R + 1) * N ≤ Real.exp (2 * (N : ℝ) * X) := by
    have hNR1 : (N : ℝ) ^ (R + 1) ≤ Real.exp ((N : ℝ) * X) := by
      rw [Real.rpow_def_of_pos hNpos]
      apply Real.exp_le_exp.mpr
      have hlogN : Real.log (N : ℝ) ≤ (N : ℝ) := by linarith [Real.log_le_sub_one_of_pos hNpos]
      calc
        Real.log (N : ℝ) * (R + 1) ≤ (N : ℝ) * (R + 3) := by nlinarith
        _ ≤ (N : ℝ) * X := by
          nlinarith [mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ R + 3)]
    have hNle : (N : ℝ) ≤ Real.exp ((N : ℝ) * X) := by
      refine le_trans ?_ (le_self_exp _)
      nlinarith
    calc
      (N : ℝ) ^ (R + 1) * N ≤ Real.exp ((N : ℝ) * X) * Real.exp ((N : ℝ) * X) :=
        mul_le_mul hNR1 hNle hNpos.le (Real.exp_pos _).le
      _ = Real.exp (2 * (N : ℝ) * X) := by
        rw [← Real.exp_add]; ring_nf
  have hB2 : (2 : ℝ) * N * (R + 1) ≤ Real.exp (2 * (N : ℝ) * X) := by
    refine le_trans ?_ (le_self_exp _)
    calc
      (2 : ℝ) * N * (R + 1) ≤ 2 * N * (R + 3) := by nlinarith
      _ ≤ 2 * N * X := by
        nlinarith [mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ R + 3)]
  have hAB2 : (N : ℝ) ^ (R + 1) * N * (2 * N * (R + 1)) ≤ Real.exp (4 * (N : ℝ) * X) := by
    calc
      (N : ℝ) ^ (R + 1) * N * (2 * N * (R + 1)) ≤
          Real.exp (2 * (N : ℝ) * X) * Real.exp (2 * (N : ℝ) * X) :=
        mul_le_mul hA2 hB2 (by positivity) (Real.exp_pos _).le
      _ = Real.exp (4 * (N : ℝ) * X) := by
        rw [← Real.exp_add]; ring_nf
  have hC2 :
    Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 3) * Real.log (R + 3))) ≤ Real.exp (2 * X) := by
    have hCexp : Real.pi ^ (-(1 : ℝ) / 4) * 4 ≤ Real.exp X :=
      le_trans hCpos.le (le_trans hX4 (le_self_exp X))
    have heq :
      Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 3) * Real.log (R + 3))) =
        Real.pi ^ (-(1 : ℝ) / 4) * 4 * Real.exp X := by
      rw [hX_def]; ring
    rw [heq]
    calc
      Real.pi ^ (-(1 : ℝ) / 4) * 4 * Real.exp X ≤ Real.exp X * Real.exp X :=
        mul_le_mul_of_nonneg_right hCexp (Real.exp_pos _).le
      _ = Real.exp (2 * X) := by
        rw [← Real.exp_add]; ring_nf
  have hT2 :
    (N : ℝ) ^ (R + 1) * N * (2 * N * (R + 1)) *
        (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 3) * Real.log (R + 3)))) ≤
      Real.exp ((4 * (N : ℝ) + 2) * X) := by
    calc
      (N : ℝ) ^ (R + 1) * N * (2 * N * (R + 1)) *
            (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 3) * Real.log (R + 3)))) ≤
          Real.exp (4 * (N : ℝ) * X) * Real.exp (2 * X) :=
        mul_le_mul hAB2 hC2 (by positivity) (Real.exp_pos _).le
      _ = Real.exp ((4 * (N : ℝ) + 2) * X) := by
        rw [← Real.exp_add]; ring_nf
  have h2leX : (2 : ℝ) ≤ Real.exp X := le_trans (by linarith) (le_trans hX4 (le_self_exp X))
  have hmax : Real.exp ((2 * (N : ℝ) + 2) * X) ≤ Real.exp ((4 * (N : ℝ) + 2) * X) :=
    Real.exp_le_exp.mpr (by nlinarith)
  unfold completedLFunctionBallBound
  calc
    2 * (N : ℝ) * R * (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 2) * Real.log (R + 2)))) +
          (N : ℝ) ^ (R + 1) * N * (2 * N * (R + 1)) *
            (Real.pi ^ (-(1 : ℝ) / 4) * (4 * Real.exp ((R + 3) * Real.log (R + 3)))) ≤
        Real.exp ((4 * (N : ℝ) + 2) * X) + Real.exp ((4 * (N : ℝ) + 2) * X) :=
      add_le_add (hT1.trans hmax) hT2
    _ = 2 * Real.exp ((4 * (N : ℝ) + 2) * X) := by ring
    _ ≤ Real.exp X * Real.exp ((4 * (N : ℝ) + 2) * X) :=
      mul_le_mul_of_nonneg_right h2leX (Real.exp_pos _).le
    _ = Real.exp ((4 * (N : ℝ) + 3) * X) := by
      rw [← Real.exp_add]; ring_nf

/-! ### Summability of the reciprocal-square zero weight

A cumulative zero count of order `R log R` gives a summable bound of order `k/2^k`
on the radial shells `2^k ≤ ‖ρ‖ < 2^(k+1)`. The bounded inner shell is handled separately.
-/

/-- The (Nat-valued) dyadic shell index of `s`:
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.shellIdx s = 0` for `‖s‖ < 2` (this bucket
also absorbs the origin), and `PseudoPrime.AnalyticNumberTheory.DirichletLFunction.shellIdx s = k ≥
1` exactly when `2^k ≤ ‖s‖ < 2^{k+1}`. -/
noncomputable def shellIdx (s : ℂ) : ℕ :=
  ⌊Real.logb 2 ‖s‖⌋₊

theorem norm_lt_two_of_shellIdx_eq_zero {s : ℂ} (hs : shellIdx s = 0) : ‖s‖ < 2 := by
  rw [shellIdx, Nat.floor_eq_zero] at hs
  rcases (norm_nonneg s).eq_or_lt with h0 | h0
  · linarith
  · rw [Real.logb_lt_iff_lt_rpow (by norm_num only) h0, Real.rpow_one] at hs
    exact hs

theorem two_pow_le_norm_of_shellIdx_eq {s : ℂ} {k : ℕ} (hk : k ≠ 0) (hs : shellIdx s = k) :
    (2 : ℝ) ^ k ≤ ‖s‖ := by
  have hpos : (0 : ℝ) < ‖s‖ := by
    rcases (norm_nonneg s).lt_or_eq with h | h
    · exact h
    · exfalso; apply hk
      rw [shellIdx, ← h, Real.logb_zero, Nat.floor_zero] at hs
      omega
  have hle : (k : ℝ) ≤ Real.logb 2 ‖s‖ := by
    rw [shellIdx] at hs
    exact_mod_cast (Nat.le_floor_iff' hk).mp hs.ge
  rw [Real.le_logb_iff_rpow_le (by norm_num only) hpos, Real.rpow_natCast] at hle
  exact hle

theorem norm_lt_two_pow_succ_of_shellIdx_eq {s : ℂ} {k : ℕ} (hs : shellIdx s = k) :
    ‖s‖ < (2 : ℝ) ^ (k + 1) := by
  rcases eq_or_ne ‖s‖ 0 with h0 | h0
  · rw [h0]; positivity
  · have hpos : (0 : ℝ) < ‖s‖ := (norm_nonneg s).lt_of_ne (Ne.symm h0)
    have hlt : Real.logb 2 ‖s‖ < (k : ℝ) + 1 := by
      rw [shellIdx] at hs
      have := Nat.lt_floor_add_one (Real.logb 2 ‖s‖)
      rwa [hs] at this
    have h2 : ‖s‖ < (2 : ℝ) ^ ((k : ℝ) + 1) :=
      (Real.logb_lt_iff_lt_rpow (by norm_num only) hpos).mp hlt
    have hexp : (2 : ℝ) ^ ((k : ℝ) + 1) = (2 : ℝ) ^ (k + 1) := by
      rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) from by
          push_cast; ring,
        Real.rpow_natCast]
    rwa [hexp] at h2

/-- Any finite `Finset` sum of the (nonnegative) divisor over an *arbitrary* `Finset` is bounded
by the total `finsum` over `closedBall 0 R`: points outside the ball contribute `0` to `D`
(by definition of `divisor` on a restricted domain), and points outside the divisor's (finite)
support also contribute `0`, so the `Finset.sum` only needs comparing against the support's
own `Finset`. -/
theorem sum_le_finsum_divisor_completedLFunction {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {R : ℝ} {t : Finset ℂ} :
    ∑ s ∈ t,
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R) s :
          ℝ) ≤
      (∑ᶠ u,
          MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R) u :
        ℝ) := by
  set D :=
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) R) with
    hD_def
  have hfin := D.finiteSupport (isCompact_closedBall (x := (0 : ℂ)) (r := R))
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalytic :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  have hnonneg : ∀ s, (0 : ℤ) ≤ D s := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic
  have hkey : ∑ s ∈ t, (D s : ℝ) ≤ ∑ s ∈ hfin.toFinset, (D s : ℝ) := by
    have h1 : ∑ s ∈ t, (D s : ℝ) ≤ ∑ s ∈ t ∪ hfin.toFinset, (D s : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun x _ _ => by exact_mod_cast hnonneg x)
    have h2 : ∑ s ∈ t ∪ hfin.toFinset, (D s : ℝ) = ∑ s ∈ hfin.toFinset, (D s : ℝ) := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro x _ hnx
      have hx0 : D x = 0 := by
        by_contra hne'
        exact hnx (hfin.mem_toFinset.mpr hne')
      simp only [hx0, Int.cast_zero]
    linarith [h1, h2]
  have heq : ∑ᶠ u : ℂ, (D u : ℝ) = ∑ s ∈ hfin.toFinset, (D s : ℝ) := by
    have hsub : Function.support (fun u : ℂ => (D u : ℝ)) ⊆ ↑hfin.toFinset := by
      intro x hx
      simp only [Function.mem_support, ne_eq] at hx
      have hx' : D x ≠ 0 := fun h =>
        hx
          (by
            rw [h]; simp only [Int.cast_zero])
      exact hfin.mem_toFinset.mpr hx'
    exact finsum_eq_sum_of_support_subset (fun u : ℂ => (D u : ℝ)) hsub
  rw [heq]
  exact hkey

/-- The (regularized, multiplicity-weighted) reciprocal-square weight of a `completedLFunction`
zero, using `Set.univ` so it is defined uniformly (no radius dependence). -/
noncomputable def completedLFunctionZeroWeight {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) : ℝ :=
  (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ s : ℝ) / (1 + ‖s‖ ^ 2)

theorem completedLFunctionZeroWeight_nonneg {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (s : ℂ) : 0 ≤ completedLFunctionZeroWeight χ s := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ =>
    hdiff.analyticAt z
  exact
    div_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic s)
      (by positivity)

/-- The `Set.univ`-divisor and the `closedBall`-divisor agree on the ball: both unfold to the
same `meromorphicOrderAt` value once the point is known to lie in the (smaller) domain. -/
theorem divisor_univ_eq_divisor_closedBall {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {R : ℝ} {s : ℂ} (hs : s ∈ Metric.closedBall (0 : ℂ) R) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ s =
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R)
        s := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have h1 : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ =>
    hdiff.analyticAt z
  have h2 :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  rw [MeromorphicOn.divisor_apply h1.meromorphicOn (Set.mem_univ s),
    MeromorphicOn.divisor_apply h2.meromorphicOn hs]

/-- For a finite set in dyadic shell `k ≠ 0`, divide the Jensen count at radius `2^(k+1)`
by `4^k`, the lower bound on `1 + ‖ρ‖²`. The exponential envelope at radius `2^(k+2)`
then yields the displayed reciprocal-square weight bound. -/
theorem sum_completedLFunctionZeroWeight_shell_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {k : ℕ}
    (hk : k ≠ 0) {t : Finset ℂ} (htk : ∀ s ∈ t, shellIdx s = k) :
    ∑ s ∈ t, completedLFunctionZeroWeight χ s ≤
      (((4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3) -
            Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2) /
        4 ^ k := by
  have hN1 : 1 < N := by omega
  have hzero := dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  have hR2k1 : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hjensen := finsum_divisor_completedLFunction_le hN1 hprimitive hne hinv hR2k1
  have hReq : (2 : ℝ) * (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k + 2) := by ring
  rw [hReq] at hjensen
  have hcast_eq :
    ((∑ᶠ u : ℂ,
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))) u :
          ℤ) :
        ℝ) =
      ∑ᶠ u : ℂ,
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))) u :
          ℝ) := by
    set D :=
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))) with
      hD_def
    have hfin := D.finiteSupport (isCompact_closedBall (x := (0 : ℂ)) (r := (2 : ℝ) ^ (k + 1)))
    exact (Int.castRingHom ℝ).toAddMonoidHom.map_finsum hfin
  rw [hcast_eq] at hjensen
  have h1leR : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := one_le_pow₀ (by norm_num only)
  have henv0 := completedLFunctionBallBound_le_exp (N := N) hN2 h1leR
  have hgroup :
    (4 * (N : ℝ) + 3) * (((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3)) =
      (4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3) := by
    ring
  rw [hgroup] at henv0
  have henv := henv0
  have hexp_ge1 :
    (1 : ℝ) ≤
      Real.exp
        ((4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3)) := by
    apply Real.one_le_exp
    have hL : (0 : ℝ) ≤ Real.log ((2 : ℝ) ^ (k + 2) + 3) :=
      Real.log_nonneg (by nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num only) (k + 2)])
    positivity
  have hmax_le :
    max 1 (completedLFunctionBallBound N ((2 : ℝ) ^ (k + 2))) ≤
      Real.exp ((4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3)) :=
    max_le hexp_ge1 henv
  have hzeronorm : (0 : ℝ) < ‖DirichletCharacter.completedLFunction χ 0‖ := by rwa [norm_pos_iff]
  have hlog_le :
    Real.log
        (max 1 (completedLFunctionBallBound N ((2 : ℝ) ^ (k + 2))) /
          ‖DirichletCharacter.completedLFunction χ 0‖) ≤
      (4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3) -
        Real.log ‖DirichletCharacter.completedLFunction χ 0‖ := by
    rw [Real.log_div (by positivity) hzeronorm.ne']
    have := Real.log_le_log (by positivity) hmax_le
    rw [Real.log_exp] at this
    linarith
  have hZC :
    ∑ᶠ u : ℂ,
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))) u :
          ℝ) ≤
      ((4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3) -
          Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 := by
    refine hjensen.trans ?_
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num only)
    exact div_le_div_of_nonneg_right hlog_le hlog2pos.le
  have hweight_le :
    ∀ s ∈ t,
      completedLFunctionZeroWeight χ s ≤
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))) s :
            ℝ) /
          4 ^ k := by
    intro s hs
    have hshell := htk s hs
    have hlb : (2 : ℝ) ^ k ≤ ‖s‖ := two_pow_le_norm_of_shellIdx_eq hk hshell
    have hub : ‖s‖ < (2 : ℝ) ^ (k + 1) := norm_lt_two_pow_succ_of_shellIdx_eq hshell
    have hmem : s ∈ Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1)) := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hub.le
    have hdeq := divisor_univ_eq_divisor_closedBall (χ := χ) hne hmem
    unfold completedLFunctionZeroWeight
    rw [hdeq]
    have h4k : (4 : ℝ) ^ k = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
      rw [show (4 : ℝ) = 2 * 2 from by norm_num only, mul_pow]
    have hsq : (2 : ℝ) ^ k * (2 : ℝ) ^ k ≤ ‖s‖ * ‖s‖ :=
      mul_le_mul hlb hlb (by positivity) (norm_nonneg s)
    have hden : (4 : ℝ) ^ k ≤ 1 + ‖s‖ ^ 2 := by
      rw [h4k, sq]; linarith
    have hnn :
      (0 : ℝ) ≤
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))) s :
          ℝ) := by
      have hdiff := DirichletCharacter.differentiable_completedLFunction hne
      have hanalytic :
        AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))) :=
        fun z _ => hdiff.analyticAt z
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic s
    apply div_le_div_of_nonneg_left hnn (by positivity) hden
  have hsum_le :
    ∑ s ∈ t, completedLFunctionZeroWeight χ s ≤
      ∑ s ∈ t,
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall (0 : ℂ) ((2 : ℝ) ^ (k + 1))) s :
            ℝ) /
          4 ^ k :=
    Finset.sum_le_sum hweight_le
  rw [← Finset.sum_div] at hsum_le
  refine hsum_le.trans ?_
  have hfsum_le :=
    sum_le_finsum_divisor_completedLFunction (N := N) (χ := χ) hne (R := (2 : ℝ) ^ (k + 1)) (t := t)
  have h4kpos : (0 : ℝ) < 4 ^ k := by positivity
  exact div_le_div_of_nonneg_right (hfsum_le.trans hZC) h4kpos.le

/-- The shell weight is bounded by `(A(k+3)+C)/2^k`, with the displayed constants depending
on the level and the central value. Use `2^(k+2)+3 ≤ 2^(k+3)` and a linear bound on its
logarithm, then cancel powers of two against `4^k`. This permits geometric comparison. -/
theorem sum_completedLFunctionZeroWeight_shell_le' {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {k : ℕ}
    (hk : k ≠ 0) {t : Finset ℂ} (htk : ∀ s ∈ t, shellIdx s = k) :
    ∑ s ∈ t, completedLFunctionZeroWeight χ s ≤
      (8 * (4 * (N : ℝ) + 3) * ((k : ℝ) + 3) +
          |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| / Real.log 2) /
        2 ^ k := by
  refine (sum_completedLFunctionZeroWeight_shell_le hN2 hprimitive hne hinv hk htk).trans ?_
  have hLpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num only)
  have hApos : (0 : ℝ) < 4 * (N : ℝ) + 3 := by positivity
  have hxle : (2 : ℝ) ^ (k + 2) + 3 ≤ (2 : ℝ) ^ (k + 3) := by
    have h1 : (3 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := by
      calc
        (3 : ℝ) ≤ 4 := by norm_num only
        _ = (2 : ℝ) ^ 2 := by norm_num only
        _ ≤ (2 : ℝ) ^ (k + 2) := by
          apply pow_le_pow_right₀ (by norm_num only)
          omega
    have h2 : (2 : ℝ) ^ (k + 3) = (2 : ℝ) ^ (k + 2) + (2 : ℝ) ^ (k + 2) := by
      rw [show k + 3 = (k + 2) + 1 from rfl, pow_succ]; ring
    linarith
  have hlogxle : Real.log ((2 : ℝ) ^ (k + 2) + 3) ≤ ((k : ℝ) + 3) * Real.log 2 := by
    calc
      Real.log ((2 : ℝ) ^ (k + 2) + 3) ≤ Real.log ((2 : ℝ) ^ (k + 3)) :=
        Real.log_le_log (by positivity) hxle
      _ = ((k : ℝ) + 3) * Real.log 2 := by
        rw [Real.log_pow]; push_cast; ring
  have hxpos : (0 : ℝ) < (2 : ℝ) ^ (k + 2) + 3 := by positivity
  have hnum_le :
    (4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3) ≤
      (4 * (N : ℝ) + 3) * (2 : ℝ) ^ (k + 3) * (((k : ℝ) + 3) * Real.log 2) := by
    have h1 : (4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) ≤ (4 * (N : ℝ) + 3) * (2 : ℝ) ^ (k + 3) :=
      mul_le_mul_of_nonneg_left hxle hApos.le
    have h1lex : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 2) + 3 := by
      nlinarith only [pow_pos (show (0 : ℝ) < 2 by norm_num only) (k + 2)]
    exact mul_le_mul h1 hlogxle (Real.log_nonneg h1lex) (by positivity)
  have hAoverL :
    (4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3) / Real.log 2 ≤
      (4 * (N : ℝ) + 3) * (2 : ℝ) ^ (k + 3) * ((k : ℝ) + 3) := by
    rw [div_le_iff₀ hLpos]
    calc
      (4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3) ≤
          (4 * (N : ℝ) + 3) * (2 : ℝ) ^ (k + 3) * (((k : ℝ) + 3) * Real.log 2) :=
        hnum_le
      _ = (4 * (N : ℝ) + 3) * (2 : ℝ) ^ (k + 3) * ((k : ℝ) + 3) * Real.log 2 := by ring
  have hyoverL :
    -Real.log ‖DirichletCharacter.completedLFunction χ 0‖ / Real.log 2 ≤
      |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| / Real.log 2 :=
    div_le_div_of_nonneg_right (neg_le_abs _) hLpos.le
  have hsplit :
    (((4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3) -
          Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2) =
      (4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3) / Real.log 2 +
        -Real.log ‖DirichletCharacter.completedLFunction χ 0‖ / Real.log 2 := by
    rw [← add_div]; ring_nf
  have hdiv_le :
    (((4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3) -
          Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2) ≤
      (4 * (N : ℝ) + 3) * (2 : ℝ) ^ (k + 3) * ((k : ℝ) + 3) +
        |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| / Real.log 2 := by
    rw [hsplit]; linarith [hAoverL, hyoverL]
  have h2kpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h4kpos' : (0 : ℝ) < (4 : ℝ) ^ k := by positivity
  have hpow_eq : (2 : ℝ) ^ (k + 3) = 8 * (2 : ℝ) ^ k := by
    rw [pow_add]; ring
  have h4eq : (4 : ℝ) ^ k = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
    rw [show (4 : ℝ) = 2 * 2 from by norm_num only, mul_pow]
  have hBeq :
    (4 * (N : ℝ) + 3) * (2 : ℝ) ^ (k + 3) * ((k : ℝ) + 3) / (4 : ℝ) ^ k =
      8 * (4 * (N : ℝ) + 3) * ((k : ℝ) + 3) / (2 : ℝ) ^ k := by
    rw [hpow_eq, h4eq]
    field_simp
  set yabs : ℝ := |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| / Real.log 2 with hyabs_def
  have habsle : yabs / (4 : ℝ) ^ k ≤ yabs / (2 : ℝ) ^ k := by
    apply
      div_le_div_of_nonneg_left
        (by
          rw [hyabs_def]; positivity)
        h2kpos
    rw [h4eq]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num only)
    nlinarith [h2kpos]
  calc
    (((4 * (N : ℝ) + 3) * ((2 : ℝ) ^ (k + 2) + 3) * Real.log ((2 : ℝ) ^ (k + 2) + 3) -
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) /
          4 ^ k ≤
        ((4 * (N : ℝ) + 3) * (2 : ℝ) ^ (k + 3) * ((k : ℝ) + 3) + yabs) / 4 ^ k :=
      div_le_div_of_nonneg_right hdiv_le h4kpos'.le
    _ = (4 * (N : ℝ) + 3) * (2 : ℝ) ^ (k + 3) * ((k : ℝ) + 3) / (4 : ℝ) ^ k + yabs / (4 : ℝ) ^ k :=
      by rw [add_div]
    _ ≤ 8 * (4 * (N : ℝ) + 3) * ((k : ℝ) + 3) / (2 : ℝ) ^ k + yabs / (2 : ℝ) ^ k := by
      rw [hBeq]; linarith [habsle]
    _ = (8 * (4 * (N : ℝ) + 3) * ((k : ℝ) + 3) + yabs) / 2 ^ k := by rw [add_div]

/-- The geometric comparison series for the shell bounds: `(A(k+3)+C)/2^k` is summable for any
constants `A, C`, via `k/2^k` and `1/2^k` each being (polynomial-times-)geometric with ratio
`1/2`. -/
theorem summable_shell_bound (A C : ℝ) :
    Summable (fun k : ℕ => (A * ((k : ℝ) + 3) + C) / (2 : ℝ) ^ k) := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs]; norm_num only
  have h1 : Summable (fun k : ℕ => (k : ℝ) * (1 / 2 : ℝ) ^ k) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 hr
    simpa only [pow_one] using this
  have h2 : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num only) (by norm_num only)
  have h1' : Summable (fun k : ℕ => A * ((k : ℝ) * (1 / 2 : ℝ) ^ k)) := h1.mul_left A
  have h2' : Summable (fun k : ℕ => (3 * A + C) * (1 / 2 : ℝ) ^ k) := h2.mul_left (3 * A + C)
  have hcomb :
    Summable (fun k : ℕ => A * ((k : ℝ) * (1 / 2 : ℝ) ^ k) + (3 * A + C) * (1 / 2 : ℝ) ^ k) :=
    h1'.add h2'
  apply hcomb.congr
  intro k
  have hpoweq : (1 / 2 : ℝ) ^ k = 1 / (2 : ℝ) ^ k := by
    rw [div_pow]
    norm_num only [one_pow]
  rw [hpoweq]
  ring

/-- The `k = 0` shell's contribution is bounded by a single fixed constant (the total zero
count, with multiplicity, in `closedBall 0 2`): `1 + ‖s‖² ≥ 1` there, so no shell-index-based
decay is even needed. -/
theorem sum_completedLFunctionZeroWeight_shell_zero_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {t : Finset ℂ} (htk : ∀ s ∈ t, shellIdx s = 0) :
    ∑ s ∈ t, completedLFunctionZeroWeight χ s ≤
      (∑ᶠ u,
          MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) 2) u :
        ℝ) := by
  have hweight_le :
    ∀ s ∈ t,
      completedLFunctionZeroWeight χ s ≤
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) 2) s :
          ℝ) := by
    intro s hs
    have hub : ‖s‖ < 2 := norm_lt_two_of_shellIdx_eq_zero (htk s hs)
    have hmem : s ∈ Metric.closedBall (0 : ℂ) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hub.le
    have hdeq := divisor_univ_eq_divisor_closedBall (χ := χ) hne hmem
    unfold completedLFunctionZeroWeight
    rw [hdeq]
    have hnn :
      (0 : ℝ) ≤
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) 2) s :
          ℝ) := by
      have hdiff := DirichletCharacter.differentiable_completedLFunction hne
      have hanalytic :
        AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) 2) :=
        fun z _ => hdiff.analyticAt z
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic s
    have hden : (1 : ℝ) ≤ 1 + ‖s‖ ^ 2 := by nlinarith [sq_nonneg ‖s‖]
    calc
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) 2)
                s :
              ℝ) /
            (1 + ‖s‖ ^ 2) ≤
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall (0 : ℂ) 2) s :
              ℝ) /
            1 :=
        div_le_div_of_nonneg_left hnn one_pos hden
      _ =
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall (0 : ℂ) 2) s :
            ℝ) :=
        by ring
  exact
    (Finset.sum_le_sum hweight_le).trans
      (sum_le_finsum_divisor_completedLFunction (N := N) (χ := χ) hne)

/-- For a primitive nontrivial character at level `N ≥ 2`, with nontrivial inverse,
`Σρ mρ/(1+‖ρ‖²)` is summable. Partition finite sums by dyadic shell, bound the inner shell
by its finite zero count, and sum the geometric majorants for the other shells. -/
theorem summable_completedLFunctionZeroWeight {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Summable (completedLFunctionZeroWeight χ) := by
  classical
  set L : ℝ :=
    (∑ᶠ u,
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) 2) u :
      ℝ) with
    hL_def
  set g : ℕ → ℝ := fun k =>
    (8 * (4 * (N : ℝ) + 3) * ((k : ℝ) + 3) +
        |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| / Real.log 2) /
      (2 : ℝ) ^ k with
    hg_def
  have hgsum : Summable g := summable_shell_bound _ _
  have hgnn : ∀ k, 0 ≤ g k := by
    intro k
    rw [hg_def]
    have habs : (0 : ℝ) ≤ |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| := abs_nonneg _
    positivity
  refine
    summable_of_sum_le (completedLFunctionZeroWeight_nonneg hne) (c := L + ∑' k, g k) fun u => ?_
  rw [← Finset.sum_filter_add_sum_filter_not u (fun s => shellIdx s = 0)]
  have hlow : ∑ s ∈ u.filter (fun s => shellIdx s = 0), completedLFunctionZeroWeight χ s ≤ L :=
    sum_completedLFunctionZeroWeight_shell_zero_le hne (fun s hs => (Finset.mem_filter.mp hs).2)
  have hhigh :
    ∑ s ∈ u.filter (fun s => ¬shellIdx s = 0), completedLFunctionZeroWeight χ s ≤ ∑' k, g k := by
    set uh := u.filter (fun s => ¬shellIdx s = 0) with huh_def
    set tt : Finset ℕ := uh.image shellIdx with htt_def
    have hmaps : ∀ s ∈ uh, shellIdx s ∈ tt := fun s hs => Finset.mem_image_of_mem _ hs
    have hband :
      ∀ j ∈ tt,
        ∑ s ∈ uh.filter (fun s => shellIdx s = j), completedLFunctionZeroWeight χ s ≤ g j := by
      intro j hj
      have hjne : j ≠ 0 := by
        rw [htt_def, Finset.mem_image] at hj
        obtain ⟨s, hs, hsj⟩ := hj
        rw [huh_def, Finset.mem_filter] at hs
        rw [← hsj]; exact hs.2
      calc
        ∑ s ∈ uh.filter (fun s => shellIdx s = j), completedLFunctionZeroWeight χ s ≤
            (8 * (4 * (N : ℝ) + 3) * ((j : ℝ) + 3) +
                |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| / Real.log 2) /
              (2 : ℝ) ^ j :=
          sum_completedLFunctionZeroWeight_shell_le' hN2 hprimitive hne hinv hjne
            (fun s hs => (Finset.mem_filter.mp hs).2)
        _ = g j := by rw [hg_def]
    calc
      ∑ s ∈ uh, completedLFunctionZeroWeight χ s =
          ∑ j ∈ tt, ∑ s ∈ uh.filter (fun s => shellIdx s = j), completedLFunctionZeroWeight χ s :=
        (Finset.sum_fiberwise_of_maps_to hmaps (completedLFunctionZeroWeight χ)).symm
      _ ≤ ∑ j ∈ tt, g j := Finset.sum_le_sum hband
      _ ≤ ∑' k, g k := hgsum.sum_le_tsum tt (fun k _ => hgnn k)
  linarith [hlow, hhigh]

/-! ### A zero-free sphere in every unit interval

Compact finiteness of the completed zero set and the infinitude of `(n,n+1)` give a radius
avoiding every zero norm. Canonical factors have norm one on this zero-free sphere.
-/

/-- Every interval `(n, n+1)` contains a radius `R` at which `completedLFunction χ` has
no zero on the circle `‖z‖ = R`. -/
theorem exists_zeroFree_sphere_radius {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1)
    (n : ℕ) :
    ∃ R : ℝ,
      (n : ℝ) < R ∧
        R < (n : ℝ) + 1 ∧ ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0 := by
  have hfin :=
    finite_dirichletCompletedLFunction_zerosOn χ hne
      (isCompact_closedBall (x := (0 : ℂ)) (r := (n : ℝ) + 1))
  have hnormfin :
    (norm ''
        (Metric.closedBall (0 : ℂ) ((n : ℝ) + 1) ∩
          (DirichletCharacter.completedLFunction χ) ⁻¹' {0})).Finite :=
    hfin.image _
  have hIooinf : (Set.Ioo (n : ℝ) ((n : ℝ) + 1)).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨R, hRmem, hRnotin⟩ := hIooinf.exists_notMem_finite hnormfin
  refine ⟨R, hRmem.1, hRmem.2, fun ρ hρ hcontra => hRnotin ?_⟩
  refine ⟨ρ, ⟨?_, hcontra⟩, hρ⟩
  rw [Metric.mem_closedBall, dist_zero_right, hρ]
  exact hRmem.2.le

/-! ### Extended canonical decomposition

Entirety and finite meromorphic order, supplied by `ZeroCounting`, allow
`MeromorphicOn.exists_ecanonicalDecomp` to produce an analytic zero-free factor on the ball.
-/

/-- `completedLFunction χ` admits an extended canonical decomposition on any
`closedBall 0 R`. -/
theorem exists_ecanonicalDecomp_completedLFunction {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (R : ℝ) :
    ∃ g, Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalytic :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  refine MeromorphicOn.exists_ecanonicalDecomp hanalytic.meromorphicOn fun u => ?_
  exact meromorphicOrderAt_dirichletCompletedLFunction_ne_top χ hne u

/-! ### Boundary norm equality

On a zero-free sphere `‖w‖ = R` , `ECanonicalDecomp.log_norm_eq` collapses: every
canonical-factor term has norm exactly `1`
(`Complex.norm_canonicalFactor_eval_circle_eq_one`) since its zero lies strictly inside the
ball while `w` sits on the boundary, and the sphere-divisor correction term vanishes outright
since `F` has no zero anywhere on the sphere — leaving `‖g w‖ = ‖F w‖`. -/

/-- On a zero-free sphere `‖w‖ = R`, the canonical-decomposition factor `g`
has the same norm as `F` itself. -/
theorem norm_ecanonicalDecomp_eq_of_zeroFree_sphere {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) {w : ℂ}
    (hw : ‖w‖ = R) : ‖g w‖ = ‖DirichletCharacter.completedLFunction χ w‖ := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalyticSphere :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.sphere (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  have hwmem : w ∈ Metric.closedBall (0 : ℂ) R := by rw [Metric.mem_closedBall, dist_zero_right, hw]
  have horderAt :
    ∀ i : ℂ,
      DirichletCharacter.completedLFunction χ i ≠ 0 →
        meromorphicOrderAt (DirichletCharacter.completedLFunction χ) i = 0 := by
    intro i hine
    rw [(hdiff.analyticAt i).meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hine)]
    rfl
  have horder := horderAt w (hzf w hw)
  have hlogeq := D.log_norm_eq hwmem horder hR
  have hspherezero :
    ∀ i : ℂ,
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.sphere (0 : ℂ) R)
                i :
              ℤ) :
            ℝ) *
          Real.log ‖w - i‖ =
        0 := by
    intro i
    by_cases hi : i ∈ Metric.sphere (0 : ℂ) R
    · have hine : ‖i‖ = R := by rwa [Metric.mem_sphere, dist_zero_right] at hi
      have hdiv0 :
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.sphere (0 : ℂ) R)
            i =
          0 := by
        rw [MeromorphicOn.divisor_apply hanalyticSphere.meromorphicOn hi, horderAt i (hzf i hine)]
        rfl
      simp only [hdiv0, Int.cast_zero, zero_mul]
    · have hdiv0 :
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.sphere (0 : ℂ) R)
            i =
          0 :=
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.sphere (0 : ℂ) R)).apply_eq_zero_of_notMem
          hi
      simp only [hdiv0, Int.cast_zero, zero_mul]
  have hballzero :
    ∀ i : ℂ,
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) i :
              ℤ) :
            ℝ) *
          Real.log ‖Complex.canonicalFactor R i w‖ =
        0 := by
    intro i
    by_cases hi0 :
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) i = 0
    · simp only [hi0, Int.cast_zero, zero_mul]
    · have hiball : i ∈ Metric.ball (0 : ℂ) R :=
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball (0 : ℂ) R)).supportWithinDomain
          hi0
      have hwsphere : w ∈ Metric.sphere (0 : ℂ) R := by
        rw [Metric.mem_sphere, dist_zero_right]; exact hw
      rw [Complex.norm_canonicalFactor_eval_circle_eq_one hiball hwsphere, Real.log_one, mul_zero]
  rw [finsum_eq_zero_of_forall_eq_zero hballzero, finsum_eq_zero_of_forall_eq_zero hspherezero,
    sub_zero, zero_add] at hlogeq
  have hFw_ne := hzf w hw
  have hgw_ne := D.ne_zero w hwmem
  have hmtc_eq :
    meromorphicTrailingCoeffAt (DirichletCharacter.completedLFunction χ) w =
      DirichletCharacter.completedLFunction χ w :=
    (hdiff.analyticAt w).meromorphicTrailingCoeffAt_of_ne_zero hFw_ne
  rw [hmtc_eq] at hlogeq
  have :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (norm_pos_iff.mpr hgw_ne))
      (Set.mem_Ioi.mpr (norm_pos_iff.mpr hFw_ne)) hlogeq
  exact this

/-- Nonvanishing at a point forces meromorphic order zero there, for the entire function
`completedLFunction χ` (used in the boundary and center computations). -/
theorem meromorphicOrderAt_dirichletCompletedLFunction_eq_zero_of_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {i : ℂ}
    (hi : DirichletCharacter.completedLFunction χ i ≠ 0) :
    meromorphicOrderAt (DirichletCharacter.completedLFunction χ) i = 0 := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  rw [(hdiff.analyticAt i).meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hi)]
  rfl

/-- The canonical-decomposition factor `g` is at least as large as `F` at the
center `0` — each canonical-factor term `‖canonicalFactor R i 0‖ = R/‖i‖ ≥ 1` for an interior
zero `i` (`‖i‖ < R`), so the boundary correction in `log_norm_eq` at `w = 0` is nonnegative. -/
theorem norm_ecanonicalDecomp_zero_ge {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) :
    ‖DirichletCharacter.completedLFunction χ 0‖ ≤ ‖g 0‖ := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalyticBall :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) := fun z _ =>
    hdiff.analyticAt z
  have hF0ne := dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    simp only [Metric.mem_closedBall, dist_self, hR.le]
  have horder0 := meromorphicOrderAt_dirichletCompletedLFunction_eq_zero_of_ne_zero hne hF0ne
  have hlogeq := D.log_norm_eq h0mem horder0 hR
  have hspherezero :
    ∀ i : ℂ,
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.sphere (0 : ℂ) R)
                i :
              ℤ) :
            ℝ) *
          Real.log ‖(0 : ℂ) - i‖ =
        0 := by
    intro i
    by_cases hi : i ∈ Metric.sphere (0 : ℂ) R
    · have hine : ‖i‖ = R := by rwa [Metric.mem_sphere, dist_zero_right] at hi
      have hanalyticSphere :
        AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.sphere (0 : ℂ) R) :=
        fun z _ => hdiff.analyticAt z
      have hdiv0 :
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.sphere (0 : ℂ) R)
            i =
          0 := by
        rw [MeromorphicOn.divisor_apply hanalyticSphere.meromorphicOn hi,
          meromorphicOrderAt_dirichletCompletedLFunction_eq_zero_of_ne_zero hne (hzf i hine)]
        rfl
      simp only [hdiv0, Int.cast_zero, zero_mul]
    · have hdiv0 :
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.sphere (0 : ℂ) R)
            i =
          0 :=
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.sphere (0 : ℂ) R)).apply_eq_zero_of_notMem
          hi
      simp only [hdiv0, Int.cast_zero, zero_mul]
  have hballnonneg :
    ∀ i : ℂ,
      (0 : ℝ) ≤
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                i :
              ℤ) :
            ℝ) *
          Real.log ‖Complex.canonicalFactor R i 0‖ := by
    intro i
    by_cases hi0 :
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) i = 0
    · simp only [hi0, Int.cast_zero, zero_mul, Std.le_refl]
    · have hiball : i ∈ Metric.ball (0 : ℂ) R :=
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball (0 : ℂ) R)).supportWithinDomain
          hi0
      have hine0 : i ≠ 0 := by
        rintro rfl
        apply hi0
        rw [MeromorphicOn.divisor_apply hanalyticBall.meromorphicOn hiball, horder0]
        rfl
      have hnormlt : ‖i‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hiball
      have hnormeq : ‖Complex.canonicalFactor R i 0‖ = R / ‖i‖ := by
        rw [Complex.canonicalFactor_apply]
        simp only [mul_zero, sub_zero, zero_sub, norm_div, norm_mul, norm_neg, norm_pow]
        rw [Complex.norm_real, Real.norm_of_nonneg hR.le, sq, mul_div_mul_left R ‖i‖ hR.ne']
      have hge1 : (1 : ℝ) ≤ ‖Complex.canonicalFactor R i 0‖ := by
        rw [hnormeq, le_div_iff₀ (norm_pos_iff.mpr hine0)]
        linarith
      have hlognn : (0 : ℝ) ≤ Real.log ‖Complex.canonicalFactor R i 0‖ := Real.log_nonneg hge1
      have hdivnn :
        (0 : ℝ) ≤
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                i :
              ℤ) :
            ℝ) := by
        exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalyticBall i
      exact mul_nonneg hdivnn hlognn
  rw [finsum_eq_zero_of_forall_eq_zero hspherezero, sub_zero] at hlogeq
  have hballnn :
    (0 : ℝ) ≤
      ∑ᶠ i,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                i :
              ℤ) :
            ℝ) *
          Real.log ‖Complex.canonicalFactor R i 0‖ :=
    finsum_nonneg hballnonneg
  have hmtc_eq :
    meromorphicTrailingCoeffAt (DirichletCharacter.completedLFunction χ) 0 =
      DirichletCharacter.completedLFunction χ 0 :=
    (hdiff.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero hF0ne
  rw [hmtc_eq] at hlogeq
  have hg0_pos : (0 : ℝ) < ‖g 0‖ := norm_pos_iff.mpr (D.ne_zero 0 h0mem)
  have hF0_pos : (0 : ℝ) < ‖DirichletCharacter.completedLFunction χ 0‖ := norm_pos_iff.mpr hF0ne
  have hlog_le : Real.log ‖DirichletCharacter.completedLFunction χ 0‖ ≤ Real.log ‖g 0‖ := by
    rw [hlogeq]; linarith
  exact (Real.log_le_log_iff hF0_pos hg0_pos).mp hlog_le

/-- On a zero-free sphere, the norm of the canonical analytic factor equals the completed
`L` norm. The maximum modulus principle extends the ball envelope to every point inside. -/
theorem norm_ecanonicalDecomp_le_ballBound {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 0 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) : ‖g z‖ ≤ completedLFunctionBallBound N R := by
  have hcl : closure (Metric.ball (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R := closure_ball 0 hR.ne'
  have hd : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R) := by
    apply DifferentiableOn.diffContOnCl
    rw [hcl]
    exact D.analyticOnNhd.differentiableOn
  have hfrontier : frontier (Metric.ball (0 : ℂ) R) = Metric.sphere (0 : ℂ) R :=
    frontier_ball 0 hR.ne'
  have hC : ∀ w ∈ frontier (Metric.ball (0 : ℂ) R), ‖g w‖ ≤ completedLFunctionBallBound N R := by
    intro w hw
    rw [hfrontier, Metric.mem_sphere, dist_zero_right] at hw
    rw [norm_ecanonicalDecomp_eq_of_zeroFree_sphere hne hR D hzf hw]
    exact norm_completedLFunction_le_completedLFunctionBallBound hN1 hprimitive hne hinv hR.le hw.le
  have hzcl : z ∈ closure (Metric.ball (0 : ℂ) R) := hcl ▸ hz
  exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd hC hzcl

/-- The canonical factor's log-norm oscillation relative to zero is bounded by the logarithm
of the completed ball envelope minus the logarithm of the completed central value.
Combine its upper norm bound with its central lower bound; both values are positive. -/
theorem ecanonicalDecomp_log_norm_oscillation_le {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 0 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    Real.log ‖g z‖ - Real.log ‖g 0‖ ≤
      Real.log (completedLFunctionBallBound N R) -
        Real.log ‖DirichletCharacter.completedLFunction χ 0‖ := by
  have hzle := norm_ecanonicalDecomp_le_ballBound hN1 hprimitive hne hinv hR D hzf hz
  have hF0ge := norm_ecanonicalDecomp_zero_ge hprimitive hne hR D hzf
  have hgz_pos : (0 : ℝ) < ‖g z‖ := norm_pos_iff.mpr (D.ne_zero z hz)
  have hg0_pos : (0 : ℝ) < ‖g 0‖ :=
    norm_pos_iff.mpr (D.ne_zero 0 (by simp only [Metric.mem_closedBall, dist_self, hR.le]))
  have hF0_pos : (0 : ℝ) < ‖DirichletCharacter.completedLFunction χ 0‖ :=
    norm_pos_iff.mpr (dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne)
  have hbound_pos : (0 : ℝ) < completedLFunctionBallBound N R := hgz_pos.trans_le hzle
  have h1 : Real.log ‖g z‖ ≤ Real.log (completedLFunctionBallBound N R) :=
    (Real.log_le_log_iff hgz_pos hbound_pos).mpr hzle
  have h2 : Real.log ‖DirichletCharacter.completedLFunction χ 0‖ ≤ Real.log ‖g 0‖ :=
    (Real.log_le_log_iff hF0_pos hg0_pos).mpr hF0ge
  linarith

/-! ### Derivative variation

`General.norm_hasDerivAt_sub_le_of_re_le`, in `General.CanonicalDecomposition`, combines
Borel–Carathéodory, an order-two Cauchy estimate, and the mean value theorem.
It bounds variation of the logarithmic derivative by `O(‖s‖ A_R/R²)` from a real-part
oscillation bound `A_R`. For fixed `s`, this tends to zero when `A_R = O(R log R)`.
-/

/-! ### Bounding variation of the zero-free factor

Combine the canonical factor's logarithm, its oscillation bound, and the derivative-variation
estimate. The resulting error has shape `(R+3)log(R+3)/R²` for a fixed evaluation point.
-/

/-- The log-derivative of the zero-free factor `g` (from an `ECanonicalDecomp`
of `F` on a zero-free sphere of radius `R`) varies little between `0` and `s`, with an explicit
`O(R log R / R²)` bound. -/
theorem norm_logDeriv_ecanonicalDecomp_sub_le {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 1 ≤ R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) {s : ℂ}
    (hs : ‖s‖ ≤ R / 2) :
    ‖logDeriv g s - logDeriv g 0‖ ≤
      192 * ‖s‖ *
          ((4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
            1) /
        R ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hN2 : 2 ≤ N := hN1
  have hanalyticBall : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) R) := fun z hz =>
    D.analyticOnNhd z (Metric.ball_subset_closedBall hz)
  have hgne : ∀ w ∈ Metric.ball (0 : ℂ) R, g w ≠ 0 := fun w hw =>
    D.ne_zero w (Metric.ball_subset_closedBall hw)
  obtain ⟨hh, hh', hh_re⟩ :=
    RiemannZeta.exists_hasDerivAt_logDeriv_re_eq_log_norm hR0 hanalyticBall hgne
  have hF0_pos : (0 : ℝ) < ‖DirichletCharacter.completedLFunction χ 0‖ :=
    norm_pos_iff.mpr (dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne)
  have h0R : ‖(0 : ℂ)‖ ≤ R := by
    rw [norm_zero]; linarith
  have hboundge : ‖DirichletCharacter.completedLFunction χ 0‖ ≤ completedLFunctionBallBound N R :=
    norm_completedLFunction_le_completedLFunctionBallBound hN1 hprimitive hne hinv hR0.le h0R
  have hboundpos : (0 : ℝ) < completedLFunctionBallBound N R := hF0_pos.trans_le hboundge
  have hbound_exp := completedLFunctionBallBound_le_exp (N := N) hN2 hR
  have hlog_bound_le :
    Real.log (completedLFunctionBallBound N R) ≤
      (4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) := by
    have hlog := Real.log_le_log hboundpos hbound_exp
    rw [Real.log_exp] at hlog
    linarith [hlog,
      show
        (4 * (N : ℝ) + 3) * ((R + 3) * Real.log (R + 3)) =
          (4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3)
        from by ring]
  have hlogF0_le_bound :
    Real.log ‖DirichletCharacter.completedLFunction χ 0‖ ≤
      Real.log (completedLFunctionBallBound N R) :=
    Real.log_le_log hF0_pos hboundge
  have hosc :
    ∀ w ∈ Metric.ball (0 : ℂ) R,
      (hh w).re ≤
        (hh 0).re +
          ((4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
            Real.log ‖DirichletCharacter.completedLFunction χ 0‖) := by
    intro w hw
    have hwcl : w ∈ Metric.closedBall (0 : ℂ) R := Metric.ball_subset_closedBall hw
    have h0cl : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
      simp only [Metric.mem_closedBall, dist_self, hR0.le]
    have h0ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self hR0
    have hoscR := ecanonicalDecomp_log_norm_oscillation_le hN1 hprimitive hne hinv hR0 D hzf hwcl
    have hew := hh_re w hw
    have he0 := hh_re 0 h0ball
    linarith [hoscR, hlog_bound_le, hew, he0]
  set M : ℝ :=
    (hh 0).re +
      ((4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
        Real.log ‖DirichletCharacter.completedLFunction χ 0‖) +
      1 with
    hM_def
  have hM0 : (hh 0).re < M := by
    rw [hM_def]; linarith [hlog_bound_le, hlogF0_le_bound]
  have hRe_le : ∀ w ∈ Metric.ball (0 : ℂ) R, (hh w).re ≤ M := by
    intro w hw
    have := hosc w hw
    rw [hM_def]; linarith
  have h7 := General.norm_hasDerivAt_sub_le_of_re_le hR0 hh' hM0 hRe_le hs
  have hMcalc :
    M - (hh 0).re =
      (4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
          Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
        1 := by
    rw [hM_def]; ring
  rw [hMcalc] at h7
  set A : ℝ :=
    (4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
        Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
      1 with
    hA_def
  have hApos : 0 < A := by
    rw [← hMcalc]; linarith
  have hsnn : 0 ≤ ‖s‖ := norm_nonneg s
  have hRs : R / 2 ≤ R - ‖s‖ := by linarith
  have hRspos : 0 < R - ‖s‖ := by linarith
  have hratio : (R + ‖s‖) / (R - ‖s‖) ^ 3 ≤ 12 / R ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (R / 2) ^ 3 ≤ (R - ‖s‖) ^ 3 := pow_le_pow_left₀ (by linarith) hRs 3
    have hstep1 : (R + ‖s‖) * R ^ 2 ≤ (3 / 2) * R * R ^ 2 := by
      have hsum : R + ‖s‖ ≤ (3 / 2 : ℝ) * R := by linarith only [hs]
      exact mul_le_mul_of_nonneg_right hsum (sq_nonneg R)
    have hstep2 : (3 / 2 : ℝ) * R * R ^ 2 = 12 * (R ^ 3 / 8) := by ring
    have hstep3 : (12 : ℝ) * (R ^ 3 / 8) ≤ 12 * (R - ‖s‖) ^ 3 := by
      have : (R : ℝ) ^ 3 / 8 = (R / 2) ^ 3 := by ring
      linarith only [h3, this]
    linarith only [hstep1, hstep2, hstep3]
  have hcrude : 16 * A * (R + ‖s‖) / (R - ‖s‖) ^ 3 * ‖s‖ ≤ 192 * ‖s‖ * A / R ^ 2 := by
    have hAnn : (0 : ℝ) ≤ 16 * A := by linarith [hApos]
    have h1 : 16 * A * ((R + ‖s‖) / (R - ‖s‖) ^ 3) ≤ 16 * A * (12 / R ^ 2) :=
      mul_le_mul_of_nonneg_left hratio hAnn
    calc
      16 * A * (R + ‖s‖) / (R - ‖s‖) ^ 3 * ‖s‖ = 16 * A * ((R + ‖s‖) / (R - ‖s‖) ^ 3) * ‖s‖ := by
        ring
      _ ≤ 16 * A * (12 / R ^ 2) * ‖s‖ := by exact mul_le_mul_of_nonneg_right h1 hsnn
      _ = 192 * ‖s‖ * A / R ^ 2 := by ring
  calc
    ‖logDeriv g s - logDeriv g 0‖ ≤ 16 * A * (R + ‖s‖) / (R - ‖s‖) ^ 3 * ‖s‖ := h7
    _ ≤ 192 * ‖s‖ * A / R ^ 2 := hcrude

/-- `(R+3)log(R+3)/R²` tends to zero at infinity. This subquadratic-growth limit is
used for the canonical-factor variation and the radius-scaled correction estimate. -/
theorem tendsto_add_mul_log_div_sq_atTop :
    Filter.Tendsto (fun R : ℝ => (R + 3) * Real.log (R + 3) / R ^ 2) Filter.atTop (nhds 0) := by
  have hlogdiv : Filter.Tendsto (fun t : ℝ => Real.log t / t) Filter.atTop (nhds 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (one_ne_zero)
    simpa only [pow_one, one_mul, add_zero] using h
  have ht : Filter.Tendsto (fun R : ℝ => R + 3) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 3 Filter.tendsto_id
  have hcomp : Filter.Tendsto (fun R : ℝ => Real.log (R + 3) / (R + 3)) Filter.atTop (nhds 0) :=
    hlogdiv.comp ht
  have hratio1 : Filter.Tendsto (fun R : ℝ => (R + 3) / R) Filter.atTop (nhds 1) := by
    have hdiv3 : Filter.Tendsto (fun R : ℝ => (3 : ℝ) / R) Filter.atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (3 : ℝ)
    have hadd : Filter.Tendsto (fun R : ℝ => 1 + 3 / R) Filter.atTop (nhds 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add hdiv3
    have heq2 : (fun R : ℝ => 1 + 3 / R) =ᶠ[Filter.atTop] (fun R : ℝ => (R + 3) / R) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
      have hRne : R ≠ 0 := hR.ne'
      field_simp
    exact hadd.congr' heq2
  have hratiosq : Filter.Tendsto (fun R : ℝ => ((R + 3) / R) ^ 2) Filter.atTop (nhds 1) := by
    have := hratio1.pow 2
    simpa only [one_pow] using this
  have hmul :
    Filter.Tendsto (fun R : ℝ => (Real.log (R + 3) / (R + 3)) * ((R + 3) / R) ^ 2) Filter.atTop
      (nhds 0) := by
    have := hcomp.mul hratiosq
    simpa only [mul_one] using this
  have heq1 :
    (fun R : ℝ => (R + 3) * Real.log (R + 3) / R ^ 2) =ᶠ[Filter.atTop]
      (fun R : ℝ => (Real.log (R + 3) / (R + 3)) * ((R + 3) / R) ^ 2) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    have hRne : R ≠ 0 := hR.ne'
    have hR3ne : R + 3 ≠ 0 := by positivity
    field_simp
  exact hmul.congr' heq1.symm

/-- For arbitrary real constants, `K1 * (K2*(R+3)*log(R+3)+c0)/R²` tends to zero.
Combine the logarithmic-growth limit with constant multiplication and the inverse-square limit. -/
theorem tendsto_const_mul_add_mul_log_add_const_div_sq_atTop (K1 K2 c0 : ℝ) :
    Filter.Tendsto (fun R : ℝ => K1 * (K2 * (R + 3) * Real.log (R + 3) + c0) / R ^ 2) Filter.atTop
      (nhds 0) := by
  have hlog2 :
    Filter.Tendsto (fun R : ℝ => (R + 3) * Real.log (R + 3) / R ^ 2) Filter.atTop (nhds 0) :=
    tendsto_add_mul_log_div_sq_atTop
  have hinv2 : Filter.Tendsto (fun R : ℝ => (R ^ 2)⁻¹) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun R : ℝ => R ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_pow_atTop (two_ne_zero)
    exact tendsto_inv_atTop_zero.comp h1
  have hK1K2 :
    Filter.Tendsto (fun R : ℝ => (K1 * K2) * ((R + 3) * Real.log (R + 3) / R ^ 2)) Filter.atTop
      (nhds 0) := by
    have := hlog2.const_mul (K1 * K2)
    simpa only [mul_zero] using this
  have hconst : Filter.Tendsto (fun R : ℝ => (K1 * c0) * (R ^ 2)⁻¹) Filter.atTop (nhds 0) := by
    have := hinv2.const_mul (K1 * c0)
    simpa only [mul_zero] using this
  have hsum :
    Filter.Tendsto
      (fun R : ℝ => (K1 * K2) * ((R + 3) * Real.log (R + 3) / R ^ 2) + (K1 * c0) * (R ^ 2)⁻¹)
      Filter.atTop (nhds 0) := by
    have := hK1K2.add hconst
    simpa only [add_zero] using this
  refine hsum.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
  have hRne : R ≠ 0 := hR.ne'
  field_simp

/-! ### A good-radius sequence

Choose zero-free radii in `(n+2,n+3)`. They tend to infinity and exceed two, so the
finite-radius estimate applies at `s = 1`. Canonical factors are chosen locally inside proofs.
-/

/-- A zero-free radius past `n + 2` chosen once and for all so later statements can refer
to `R_n` without re-choosing at each use site. -/
noncomputable def completedLFunctionGoodRadius {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (n : ℕ) : ℝ :=
  Classical.choose (exists_zeroFree_sphere_radius hne (n + 2))

/-- The chosen radius lies in `(n+2,n+3)` and the completed `L`-function does not vanish
on its sphere. Package the three consequences of `Classical.choose_spec` for later use. -/
theorem completedLFunctionGoodRadius_spec {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (n : ℕ) :
    ((n : ℝ) + 2 < completedLFunctionGoodRadius hne n) ∧
      (completedLFunctionGoodRadius hne n < (n : ℝ) + 2 + 1) ∧
      (∀ ρ : ℂ,
        ‖ρ‖ = completedLFunctionGoodRadius hne n →
          DirichletCharacter.completedLFunction χ ρ ≠ 0) := by
  unfold completedLFunctionGoodRadius
  exact_mod_cast Classical.choose_spec (exists_zeroFree_sphere_radius hne (n + 2))

theorem completedLFunctionGoodRadius_gt {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (n : ℕ) : (n : ℝ) + 2 < completedLFunctionGoodRadius hne n :=
  (completedLFunctionGoodRadius_spec hne n).1

theorem completedLFunctionGoodRadius_zeroFree {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (n : ℕ) :
    ∀ ρ : ℂ,
      ‖ρ‖ = completedLFunctionGoodRadius hne n → DirichletCharacter.completedLFunction χ ρ ≠ 0 :=
  (completedLFunctionGoodRadius_spec hne n).2.2

/-- The good-radius sequence tends to infinity, sandwiched between `n + 2` and `n + 3`. -/
theorem tendsto_completedLFunctionGoodRadius_atTop {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) :
    Filter.Tendsto (completedLFunctionGoodRadius hne) Filter.atTop Filter.atTop := by
  have hlow : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 2 tendsto_natCast_atTop_atTop
  exact Filter.tendsto_atTop_mono (fun n => (completedLFunctionGoodRadius_gt hne n).le) hlow

/-! ### Centered logarithmic derivative at finite radius

Differentiate the finite canonical-factor product, then center the identity at zero.
The negative divisor exponents give the genus-one sum and a radius-dependent correction.
-/

/-! The canonical-factor identities in `General.CanonicalDecomposition` compute the
logarithmic derivative of `(R²-conj(w)z)/(R(z-w))`. After multiplication by the exponent
`-m_w`, centering gives `m_w * (1/(s-w)+1/w)` and
`m_w * (conj(w)/(R²-conj(w)s)-conj(w)/R²)`.
The same module supplies `preperfect_closedBall`, used to pass from codiscrete equality
to punctured-neighborhood equality. -/

/-- On a zero-free sphere, the sphere-divisor exponent factor in
`ECanonicalDecomp.eventuallyEq` (the boundary rational-function correction, present in general
to account for zeros or poles located exactly on the sphere) is identically `1`, since `F` has
no such zeros. -/
theorem sphereFactor_eq_one_of_zeroFree {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {R : ℝ} (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) :
    (∏ᶠ v : ℂ,
        (fun z : ℂ => z - v) ^
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.sphere (0 : ℂ) R)
            v)) =
      (1 : ℂ → ℂ) := by
  apply finprod_eq_one_of_forall_eq_one
  intro v
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  by_cases hv : v ∈ Metric.sphere (0 : ℂ) R
  · have hvne : ‖v‖ = R := by rwa [Metric.mem_sphere, dist_zero_right] at hv
    have hanalyticSphere :
      AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.sphere (0 : ℂ) R) :=
      fun z _ => hdiff.analyticAt z
    have hdiv0 :
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.sphere (0 : ℂ) R) v =
        0 := by
      rw [MeromorphicOn.divisor_apply hanalyticSphere.meromorphicOn hv,
        meromorphicOrderAt_dirichletCompletedLFunction_eq_zero_of_ne_zero hne (hzf v hvne)]
      rfl
    rw [hdiv0]; funext z
    simp only [Pi.pow_apply, zpow_ofNat, pow_zero, Pi.one_apply]
  · have hdiv0 :
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.sphere (0 : ℂ) R) v =
        0 :=
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.sphere (0 : ℂ) R)).apply_eq_zero_of_notMem
        hv
    rw [hdiv0]; funext z
    simp only [Pi.pow_apply, zpow_ofNat, pow_zero, Pi.one_apply]

/-- The right side of `ECanonicalDecomp.eventuallyEq` is
`MeromorphicAt` at every point (needed as a hypothesis of
`MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect`) — a finite
product of canonical factors (each a rational function, hence meromorphic via `finprod`'s
unconditional meromorphicity) times the (here identically-`1`, since zero-free) sphere factor,
times the analytic `g`. -/
theorem meromorphicAt_ecanonicalDecompRHS {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {R : ℝ} {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) {x : ℂ}
    (hx : x ∈ Metric.closedBall (0 : ℂ) R) :
    MeromorphicAt
      (((∏ᶠ u : ℂ,
            (Complex.canonicalFactor R u) ^
              (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                  (Metric.ball (0 : ℂ) R) u)) *
          (∏ᶠ v : ℂ,
            (fun z : ℂ => z - v) ^
              (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.sphere (0 : ℂ) R) v))) •
        g)
      x := by
  have hprod :
    MeromorphicAt
      (∏ᶠ u : ℂ,
        (Complex.canonicalFactor R u) ^
          (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
              u))
      x :=
    MeromorphicAt.finprod (fun u => (Complex.meromorphic_canonicalFactor R u x).zpow _)
  have hsphere1 := sphereFactor_eq_one_of_zeroFree hne hzf (R := R)
  have hgAt : MeromorphicAt g x := (D.analyticOnNhd x hx).meromorphicAt
  rw [hsphere1, mul_one]
  exact hprod.smul hgAt

/-- The log-derivative of the canonical-factor product expands to
the weighted sum of individual log-derivatives, away from a codiscrete subset of `ball 0 R` —
a direct application of `MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq`, requiring only that
each `canonicalFactor` is meromorphic everywhere with finite order (both already available:
`Complex.meromorphic_canonicalFactor`, `Complex.meromorphicOrderAt_canonicalFactor_ne_top`) and
that the divisor of `F` on `ball 0 R` has finite support
(`MeromorphicOn.divisor_ball_support_finite`). -/
theorem logDeriv_canonicalFactorProduct_eventuallyEq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {R : ℝ} (hR : 0 < R) :
    logDeriv
        (∏ᶠ u : ℂ,
          (Complex.canonicalFactor R u) ^
            (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.ball (0 : ℂ) R) u)) =ᶠ[Filter.codiscreteWithin (Metric.ball (0 : ℂ) R)]
      fun z =>
      ∑ᶠ u : ℂ,
        (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
              u) •
          logDeriv (Complex.canonicalFactor R u) z := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalyticClosed :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  have hfin :
    (Function.support
        (fun u : ℂ =>
          -MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
              u)).Finite := by
    have hfin' := hanalyticClosed.meromorphicOn.divisor_ball_support_finite
    have hset :
      Function.support
          (fun u : ℂ =>
            -MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                u) =
        Function.support
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball (0 : ℂ) R)) := by
      ext u
      simp only [Function.mem_support]
      constructor
      · intro h hz
        apply h
        rw [hz, neg_zero]
      · intro h hz
        apply h
        exact neg_eq_zero.mp hz
    rw [hset]
    exact hfin'
  exact
    MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq hfin
      (fun u x _ => Complex.meromorphic_canonicalFactor R u x)
      (fun u x _ => Complex.meromorphicOrderAt_canonicalFactor_ne_top u hR)

/-! The continuity lemma `General.eq_of_eventuallyEq_nhdsNE_of_continuousAt`
upgrades punctured-neighborhood equality to equality at the evaluation point. -/

/-- At a point `x` where `F` does not vanish, the canonical-factor product is
`AnalyticAt` — avoiding the circularity of trying to derive this from the very
`codiscreteWithin` identity it will be used to upgrade. Each factor `canonicalFactor R u ^
(-divisor u)` is handled by cases on whether `divisor u = 0` (then the factor is the constant
`1`, trivially analytic) or not (then `u ≠ x`, since `F x ≠ 0` forces `divisor x = 0`, so
`canonicalFactor R u` is analytic and nonzero at `x`, hence so is its integer power). -/
theorem analyticAt_canonicalFactorProduct_of_completedLFunction_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {R : ℝ} {x : ℂ}
    (hxclosed : x ∈ Metric.closedBall (0 : ℂ) R)
    (hxne : DirichletCharacter.completedLFunction χ x ≠ 0) :
    AnalyticAt ℂ
      (∏ᶠ u : ℂ,
        (Complex.canonicalFactor R u) ^
          (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
              u))
      x := by
  apply analyticAt_finprod
  intro u
  by_cases hdu :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) u = 0
  · rw [hdu, neg_zero, zpow_zero]
    exact analyticAt_const
  · have huball : u ∈ Metric.ball (0 : ℂ) R :=
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball (0 : ℂ) R)).supportWithinDomain
        hdu
    have huxne : u ≠ x := by
      rintro rfl
      apply hdu
      have hdiff := DirichletCharacter.differentiable_completedLFunction hne
      have hanalyticBall :
        AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) :=
        fun z _ => hdiff.analyticAt z
      rw [MeromorphicOn.divisor_apply hanalyticBall.meromorphicOn huball,
        meromorphicOrderAt_dirichletCompletedLFunction_eq_zero_of_ne_zero hne hxne]
      rfl
    have hcfAt : AnalyticAt ℂ (Complex.canonicalFactor R u) x :=
      Complex.analyticOnNhd_canonicalFactor R u x huxne.symm
    have hcfne : Complex.canonicalFactor R u x ≠ 0 :=
      Complex.canonicalFactor_ne_zero huball hxclosed huxne.symm
    exact hcfAt.zpow hcfne

/-- At a nonzero value of the completed `L`-function in the closed ball, its logarithmic
derivative is that of the canonical product plus that of the analytic factor. Remove the
sphere factor using zero-freeness, upgrade codiscrete equality locally, and differentiate
where the canonical product and analytic factor are nonzero. -/
theorem ecanonicalDecomp_logDeriv_eq_at {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) {x : ℂ}
    (hxclosed : x ∈ Metric.closedBall (0 : ℂ) R)
    (hxne : DirichletCharacter.completedLFunction χ x ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) x =
      logDeriv
          (∏ᶠ u : ℂ,
            (Complex.canonicalFactor R u) ^
              (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                  (Metric.ball (0 : ℂ) R) u))
          x +
        logDeriv g x := by
  set P : ℂ → ℂ :=
    ∏ᶠ u : ℂ,
      (Complex.canonicalFactor R u) ^
        (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
            u) with
    hP_def
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hFAt : MeromorphicAt (DirichletCharacter.completedLFunction χ) x :=
    (hdiff.analyticAt x).meromorphicAt
  have hRHSAt := meromorphicAt_ecanonicalDecompRHS hne D hzf hxclosed
  have hFeqRHS :=
    hFAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect hRHSAt hxclosed
      (General.preperfect_closedBall hR) D.eventuallyEq
  have hsphere1 := sphereFactor_eq_one_of_zeroFree hne hzf (R := R)
  have hFeqPg : (DirichletCharacter.completedLFunction χ) =ᶠ[nhdsWithin x {x}ᶜ] (P * g) := by
    have hrw :
      (((P *
              (∏ᶠ v : ℂ,
                (fun z : ℂ => z - v) ^
                  (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                    (Metric.sphere (0 : ℂ) R) v))) •
            g) :
          ℂ → ℂ) =
        P * g := by
      rw [hsphere1, mul_one]; funext z
      simp only [Pi.smul_apply', smul_eq_mul, Pi.mul_apply]
    rwa [hrw] at hFeqRHS
  have hPAt : AnalyticAt ℂ P x :=
    analyticAt_canonicalFactorProduct_of_completedLFunction_ne_zero hne hxclosed hxne
  have hgxne : g x ≠ 0 := D.ne_zero x hxclosed
  have hPxne : P x ≠ 0 := by
    have hFxeqPg : (DirichletCharacter.completedLFunction χ) x = (P * g) x :=
      General.eq_of_eventuallyEq_nhdsNE_of_continuousAt (hdiff.analyticAt x).continuousAt
        (hPAt.continuousAt.mul (D.analyticOnNhd x hxclosed).continuousAt) hFeqPg
    intro hP0
    rw [show (P * g) x = P x * g x from rfl, hP0, zero_mul] at hFxeqPg
    exact hxne hFxeqPg
  have hlogDerivEq :
    logDeriv (DirichletCharacter.completedLFunction χ) =ᶠ[nhdsWithin x {x}ᶜ] logDeriv (P * g) :=
    logDeriv_congr_nhdsNE hFeqPg
  have hFContAt : ContinuousAt (logDeriv (DirichletCharacter.completedLFunction χ)) x := by
    have h1 : ContinuousAt (deriv (DirichletCharacter.completedLFunction χ)) x :=
      (hdiff.deriv.analyticAt x).continuousAt
    exact h1.div (hdiff.analyticAt x).continuousAt hxne
  have hPgContAt : ContinuousAt (logDeriv (P * g)) x := by
    have hderivPg : ContinuousAt (deriv (P * g)) x := by
      have : AnalyticAt ℂ (deriv (P * g)) x := (hPAt.mul (D.analyticOnNhd x hxclosed)).deriv
      exact this.continuousAt
    have hPgcont : ContinuousAt (P * g) x :=
      hPAt.continuousAt.mul (D.analyticOnNhd x hxclosed).continuousAt
    have hPgne : (P * g) x ≠ 0 := mul_ne_zero hPxne hgxne
    exact hderivPg.div hPgcont hPgne
  have hval := General.eq_of_eventuallyEq_nhdsNE_of_continuousAt hFContAt hPgContAt hlogDerivEq
  rw [hval]
  exact
    logDeriv_mul x hPxne hgxne hPAt.differentiableAt (D.analyticOnNhd x hxclosed).differentiableAt

/-- Shared step for the finite-radius divisor identities: a point `u` in the support of the divisor
of `F` on `ball 0 R`
cannot equal an evaluation point `x` where `F` does not vanish. -/
theorem ne_of_mem_divisorBallSupport_of_completedLFunction_ne_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {R : ℝ} {u x : ℂ}
    (hu :
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) u ≠ 0)
    (hxne : DirichletCharacter.completedLFunction χ x ≠ 0) : u ≠ x := by
  rintro rfl
  apply hu
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have huball : u ∈ Metric.ball (0 : ℂ) R :=
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.ball (0 : ℂ) R)).supportWithinDomain
      hu
  have hanalyticBall :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) := fun z _ =>
    hdiff.analyticAt z
  rw [MeromorphicOn.divisor_apply hanalyticBall.meromorphicOn huball,
    meromorphicOrderAt_dirichletCompletedLFunction_eq_zero_of_ne_zero hne hxne]
  rfl

/-- The log-derivative of the canonical-factor product, evaluated at a point
`x` where `F` does not vanish, equals the finite sum (packaged as a `finsum`) of the individual
weighted log-derivatives — rewriting the `finprod` to a `Finset.prod` over the (finite) divisor
support and applying `logDeriv_prod`/`logDeriv_fun_zpow` pointwise, using
`DirichletLFunction.ne_of_mem_divisorBallSupport_of_completedLFunction_ne_zero`
to see that no support point
coincides with `x`. -/
theorem logDeriv_canonicalFactorProduct_eq_finsum_at {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {R : ℝ} {x : ℂ} (hxclosed : x ∈ Metric.closedBall (0 : ℂ) R)
    (hxne : DirichletCharacter.completedLFunction χ x ≠ 0) :
    logDeriv
        (∏ᶠ u : ℂ,
          (Complex.canonicalFactor R u) ^
            (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.ball (0 : ℂ) R) u))
        x =
      ∑ᶠ u : ℂ,
        ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                  u :
              ℤ) :
            ℂ) *
          logDeriv (Complex.canonicalFactor R u) x := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalyticClosed :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  have hfin := hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have hdfin :
    (Function.support
        (fun u : ℂ =>
          -MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
              u)).Finite := by
    have hset :
      Function.support
          (fun u : ℂ =>
            -MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                u) =
        Function.support
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball (0 : ℂ) R)) := by
      ext u
      simp only [Function.mem_support]
      constructor
      · intro h hz
        apply h
        rw [hz, neg_zero]
      · intro h hz
        apply h
        exact neg_eq_zero.mp hz
    rw [hset]
    exact hfin
  -- key facts about each `i` in the (finite) support, bundled once
  have hkey : ∀ i ∈ hdfin.toFinset, i ≠ x ∧ i ∈ Metric.ball (0 : ℂ) R := by
    intro i hi
    rw [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, neg_eq_zero] at hi
    have hine : i ≠ x := ne_of_mem_divisorBallSupport_of_completedLFunction_ne_zero hne hi hxne
    exact
      ⟨hine,
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball (0 : ℂ) R)).supportWithinDomain
          hi⟩
  have h0 :
    (∏ᶠ u : ℂ,
        (Complex.canonicalFactor R u) ^
          (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
              u)) =
      ∏ i ∈ hdfin.toFinset,
        (Complex.canonicalFactor R i) ^
          (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
              i) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro i hi
    simp only [Function.mem_mulSupport] at hi
    simp only [Set.Finite.coe_toFinset, Function.mem_support, ne_eq, neg_eq_zero]
    intro hi0
    exact
      hi
        (by
          rw [hi0]; rfl)
  have hAnalyticAll : ∀ i ∈ hdfin.toFinset, AnalyticAt ℂ (Complex.canonicalFactor R i) x :=
    fun i hi => Complex.analyticOnNhd_canonicalFactor R i x (hkey i hi).1.symm
  have hcfxne :
    ∀ i ∈ hdfin.toFinset,
      Complex.canonicalFactor R i x ^
          (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
              i) ≠
        0 :=
    fun i hi =>
    zpow_ne_zero _ (Complex.canonicalFactor_ne_zero (hkey i hi).2 hxclosed (hkey i hi).1.symm)
  have hdAt :
    ∀ i ∈ hdfin.toFinset,
      DifferentiableAt ℂ
        (fun z =>
          (Complex.canonicalFactor R i z) ^
            (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.ball (0 : ℂ) R) i))
        x :=
    fun i hi =>
    (hAnalyticAll i hi).differentiableAt.zpow
      (Or.inl (Complex.canonicalFactor_ne_zero (hkey i hi).2 hxclosed (hkey i hi).1.symm))
  have hprodfun :
    (fun a =>
        ∏ i ∈ hdfin.toFinset,
          (Complex.canonicalFactor R i a) ^
            (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.ball (0 : ℂ) R) i)) =
      ∏ i ∈ hdfin.toFinset,
        (fun a =>
          (Complex.canonicalFactor R i a) ^
            (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.ball (0 : ℂ) R) i)) := by
    funext a
    rw [Finset.prod_apply]
  have hstep :
    logDeriv
        (fun a =>
          ∏ i ∈ hdfin.toFinset,
            (Complex.canonicalFactor R i a) ^
              (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                  (Metric.ball (0 : ℂ) R) i))
        x =
      ∑ i ∈ hdfin.toFinset,
        logDeriv
          (fun z =>
            (Complex.canonicalFactor R i z) ^
              (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                  (Metric.ball (0 : ℂ) R) i))
          x := by
    rw [hprodfun]
    exact logDeriv_prod hcfxne hdAt
  rw [h0, Finset.prod_fn]
  rw [show
      (fun a =>
          ∏ i ∈ hdfin.toFinset,
            (Complex.canonicalFactor R i ^
                (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                    (Metric.ball (0 : ℂ) R) i))
              a) =
        (fun a =>
          ∏ i ∈ hdfin.toFinset,
            (Complex.canonicalFactor R i a) ^
              (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                  (Metric.ball (0 : ℂ) R) i))
      from rfl,
    hstep]
  have hsub :
    Function.support
        (fun i : ℂ =>
          ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                    i :
                ℤ) :
              ℂ) *
            logDeriv (Complex.canonicalFactor R i) x) ⊆
      hdfin.toFinset := by
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro h0'
    apply hi
    rw [h0']; simp only [Int.cast_zero, zero_mul]
  rw [show
      (∑ i ∈ hdfin.toFinset,
          logDeriv
            (fun z =>
              (Complex.canonicalFactor R i z) ^
                (-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                    (Metric.ball (0 : ℂ) R) i))
            x) =
        ∑ i ∈ hdfin.toFinset,
          ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                    i :
                ℤ) :
              ℂ) *
            logDeriv (Complex.canonicalFactor R i) x
      from
      Finset.sum_congr rfl
        (fun i hi => by rw [logDeriv_fun_zpow (hAnalyticAll i hi).differentiableAt, mul_comm])]
  exact (finsum_eq_sum_of_support_subset _ hsub).symm

/-- For a primitive nontrivial character and a zero-free sphere of positive radius, subtract
the pointwise canonical-decomposition identity at zero from the one at `s` in the closed ball,
where the completed `L`-value is nonzero. The result is the difference of the two weighted
canonical-factor sums plus `logDeriv g s - logDeriv g 0`, used in the finite-radius error bound. -/
theorem ecanonicalDecomp_centered_logDeriv_eq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) {s : ℂ}
    (hsclosed : s ∈ Metric.closedBall (0 : ℂ) R)
    (hsne : DirichletCharacter.completedLFunction χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s -
        logDeriv (DirichletCharacter.completedLFunction χ) 0 =
      ((∑ᶠ u : ℂ,
            ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                      (Metric.ball (0 : ℂ) R) u :
                  ℤ) :
                ℂ) *
              logDeriv (Complex.canonicalFactor R u) s) -
          (∑ᶠ u : ℂ,
            ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                      (Metric.ball (0 : ℂ) R) u :
                  ℤ) :
                ℂ) *
              logDeriv (Complex.canonicalFactor R u) 0)) +
        (logDeriv g s - logDeriv g 0) := by
  have h0closed : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    simp only [Metric.mem_closedBall, dist_self, hR.le]
  have h0ne : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  have heqs := ecanonicalDecomp_logDeriv_eq_at hne hR D hzf hsclosed hsne
  have heq0 := ecanonicalDecomp_logDeriv_eq_at hne hR D hzf h0closed h0ne
  rw [logDeriv_canonicalFactorProduct_eq_finsum_at hne hsclosed hsne] at heqs
  rw [logDeriv_canonicalFactorProduct_eq_finsum_at hne h0closed h0ne] at heq0
  linear_combination heqs - heq0

/-! ### the finite-radius estimate preliminary: unify the ball-divisor with the global divisor

`divisor F (ball 0 R)` (used throughout the finite-radius argument) and `divisor F Set.univ` (used
by the global argument)
agree wherever the ball-divisor is even eligible to be nonzero: both unfold to the same
`meromorphicOrderAt`-derived value at any point of the ball, and the ball-divisor is
identically `0` outside it. This lets later sums over `ball 0 R` be rewritten as `Set.univ`-sums
with an indicator, matching reciprocal-square weight summability and simplifying the finite-radius
estimate's dominated-convergence
argument. -/

/-- `divisor F (ball 0 R) ρ` equals `divisor F Set.univ ρ` if
`‖ρ‖ < R`, and `0` otherwise. -/
theorem divisor_ball_eq_if_univ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1)
    {R : ℝ} (ρ : ℂ) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) ρ =
      if ‖ρ‖ < R then MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ
      else 0 := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  split_ifs with hρ
  · have hρball : ρ ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right]; exact hρ
    have hanalyticBall :
      AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) :=
      fun z _ => hdiff.analyticAt z
    have hanalyticUniv : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
      fun z _ => hdiff.analyticAt z
    rw [MeromorphicOn.divisor_apply hanalyticBall.meromorphicOn hρball,
      MeromorphicOn.divisor_apply hanalyticUniv.meromorphicOn (Set.mem_univ ρ)]
  · exact
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball (0 : ℂ) R)).apply_eq_zero_of_notMem
        (by
          rw [Metric.mem_ball, dist_zero_right]; exact hρ)

/-! ### the finite-radius estimate: the canonical correction is `O(‖s‖/R²)`, pointwise and summed

`PseudoPrime.AnalyticNumberTheory.General.norm_canonicalCorrection_le` in
`General.CanonicalDecomposition` gives the pointwise bound on
the canonical correction term `ρ̄/(R²-ρ̄s) - ρ̄/R²`, using only `‖ρ‖ < R` and `‖s‖ ≤ R/2`. -/

/-- Points inside `ball 0 R` have the same divisor whether computed relative to `ball 0 R` or
`closedBall 0 R`: chain
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.divisor_ball_eq_if_univ` (ball agrees with
`Set.univ` inside the ball)
with `PseudoPrime.AnalyticNumberTheory.DirichletLFunction.divisor_univ_eq_divisor_closedBall`
(`Set.univ` agrees with `closedBall` inside it). -/
theorem divisor_ball_eq_divisor_closedBall_of_mem_ball {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {R : ℝ} {ρ : ℂ} (hρ : ρ ∈ Metric.ball (0 : ℂ) R) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) ρ =
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R)
        ρ := by
  have hρnorm : ‖ρ‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hρ
  rw [divisor_ball_eq_if_univ hne, ite_eq_left hρnorm,
    divisor_univ_eq_divisor_closedBall hne (Metric.ball_subset_closedBall hρ)]

/-- Sum the bound `2‖s‖/R²` for the canonical correction over the finite divisor support,
weighted by nonnegative multiplicities. Jensen's zero-count bound controls the resulting
multiplicity sum. No infinite-series summability hypothesis is used. -/
theorem norm_canonicalCorrectionSum_le {N : ℕ} [NeZero N] (hN1 : 1 < N) {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ} (hR : 0 < R) {s : ℂ}
    (hs : ‖s‖ ≤ R / 2) :
    ‖∑ᶠ ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                  ρ :
                ℤ) :
              ℂ) *
            ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
              (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ ≤
      2 * ‖s‖ / R ^ 2 *
        (Real.log
            (max 1 (completedLFunctionBallBound N (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2) := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalyticClosed :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  have hanalyticBall :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) := fun z _ =>
    hdiff.analyticAt z
  set D :=
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) with
    hD_def
  have hfin : (Function.support D).Finite :=
    hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have hDnonneg : ∀ ρ, (0 : ℤ) ≤ D ρ := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalyticBall
  have heqsum :
    (∑ᶠ ρ : ℂ,
        ((D ρ : ℤ) : ℂ) *
          ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
            (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)) =
      ∑ ρ ∈ hfin.toFinset,
        ((D ρ : ℤ) : ℂ) *
          ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
            (starRingEnd ℂ) ρ / (R : ℂ) ^ 2) := by
    apply finsum_eq_sum_of_support_subset
    intro ρ hρ
    simp only [Function.mem_support, ne_eq] at hρ
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hD0
    apply hρ
    rw [hD0]; simp only [Int.cast_zero, zero_mul]
  rw [heqsum]
  have hstep1 :
    ‖∑ ρ ∈ hfin.toFinset,
          ((D ρ : ℤ) : ℂ) *
            ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
              (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ ≤
      ∑ ρ ∈ hfin.toFinset, (D ρ : ℝ) * (2 * ‖s‖ / R ^ 2) := by
    calc
      ‖∑ ρ ∈ hfin.toFinset,
              ((D ρ : ℤ) : ℂ) *
                ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
                  (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ ≤
          ∑ ρ ∈ hfin.toFinset,
            ‖((D ρ : ℤ) : ℂ) *
                ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
                  (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ ρ ∈ hfin.toFinset, (D ρ : ℝ) * (2 * ‖s‖ / R ^ 2) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_mul]
        have hDcast : ‖((D ρ : ℤ) : ℂ)‖ = (D ρ : ℝ) := by
          rw [Complex.norm_intCast, abs_of_nonneg (by exact_mod_cast hDnonneg ρ)]
        rw [hDcast]
        apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hDnonneg ρ)
        rw [Set.Finite.mem_toFinset] at hρ
        have hρball : ρ ∈ Metric.ball (0 : ℂ) R := D.supportWithinDomain hρ
        exact
          General.norm_canonicalCorrection_le (by rwa [Metric.mem_ball, dist_zero_right] at hρball)
            hs
  have hstep2 :
    ∑ ρ ∈ hfin.toFinset, (D ρ : ℝ) * (2 * ‖s‖ / R ^ 2) =
      (2 * ‖s‖ / R ^ 2) * ∑ ρ ∈ hfin.toFinset, (D ρ : ℝ) := by
    rw [← Finset.sum_mul, mul_comm]
  have hfincl :=
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) R)).finiteSupport
      (isCompact_closedBall (x := (0 : ℂ)) (r := R))
  have hcast_eq :
    ((∑ᶠ u : ℂ,
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall (0 : ℂ) R) u :
          ℤ) :
        ℝ) =
      ∑ᶠ u : ℂ,
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R) u :
          ℝ) :=
    (Int.castRingHom ℝ).toAddMonoidHom.map_finsum hfincl
  have hstep3 :
    ∑ ρ ∈ hfin.toFinset, (D ρ : ℝ) ≤
      ((∑ᶠ u : ℂ,
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall (0 : ℂ) R) u :
          ℤ) :
        ℝ) := by
    have heq :
      ∀ ρ ∈ hfin.toFinset,
        (D ρ : ℝ) =
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall (0 : ℂ) R) ρ :
            ℝ) := by
      intro ρ hρ
      rw [Set.Finite.mem_toFinset] at hρ
      have hρball : ρ ∈ Metric.ball (0 : ℂ) R :=
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball (0 : ℂ) R)).supportWithinDomain
          hρ
      exact_mod_cast divisor_ball_eq_divisor_closedBall_of_mem_ball hne hρball
    rw [Finset.sum_congr rfl heq, hcast_eq]
    exact sum_le_finsum_divisor_completedLFunction hne
  have hcastfinsum :
    ((∑ᶠ u : ℂ,
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall (0 : ℂ) R) u :
          ℤ) :
        ℝ) ≤
      Real.log
          (max 1 (completedLFunctionBallBound N (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 :=
    finsum_divisor_completedLFunction_le hN1 hprimitive hne hinv hR
  have hpos : (0 : ℝ) ≤ 2 * ‖s‖ / R ^ 2 := by positivity
  calc
    ‖∑ ρ ∈ hfin.toFinset,
            ((D ρ : ℤ) : ℂ) *
              ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
                (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ ≤
        ∑ ρ ∈ hfin.toFinset, (D ρ : ℝ) * (2 * ‖s‖ / R ^ 2) :=
      hstep1
    _ = (2 * ‖s‖ / R ^ 2) * ∑ ρ ∈ hfin.toFinset, (D ρ : ℝ) := hstep2
    _ ≤
        (2 * ‖s‖ / R ^ 2) *
          ((∑ᶠ u : ℂ,
                MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                  (Metric.closedBall (0 : ℂ) R) u :
              ℤ) :
            ℝ) :=
      mul_le_mul_of_nonneg_left hstep3 hpos
    _ ≤
        (2 * ‖s‖ / R ^ 2) *
          (Real.log
              (max 1 (completedLFunctionBallBound N (2 * R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) :=
      mul_le_mul_of_nonneg_left hcastfinsum hpos

/-! ### the finite-radius estimate: a finite-radius error theorem that hides `g` and
`ECanonicalDecomp`

Combines the factor-variation bound
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_ecanonicalDecomp_sub_le`), the
finite-radius estimate
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ecanonicalDecomp_centered_logDeriv_eq`), the
canonical-factor identity
(`PseudoPrime.AnalyticNumberTheory.General.centered_logDeriv_canonicalFactor`) and the correction
estimate
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_canonicalCorrectionSum_le`) into a
single public bound. `g` and the `ECanonicalDecomp`
are only ever `obtain`ed inside the proof — from here on, downstream statements only refer to
`F`, `R`, `s`, and the truncated genus sum. -/

/-- The genus-one sum, truncated to the zeros of `F` inside `ball 0 R` (with multiplicity). -/
noncomputable def completedLFunctionTruncatedGenusSum {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (R : ℝ) (s : ℂ) : ℂ :=
  ∑ᶠ ρ : ℂ,
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) ρ :
          ℤ) :
        ℂ) *
      (1 / (s - ρ) + 1 / ρ)

/-- For a primitive nontrivial character at level `N > 1`, a zero-free sphere with `R ≥ 1`,
and a nonzero completed value at `‖s‖ ≤ R/2`, the centered logarithmic derivative differs
from the truncated genus-one sum by at most the displayed factor-variation and correction
bounds. Choose a canonical decomposition inside the proof, so no factor is exposed in the type. -/
theorem norm_centeredLogDeriv_sub_truncatedGenus_le {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 1 ≤ R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) {s : ℂ}
    (hs : ‖s‖ ≤ R / 2) (hsne : DirichletCharacter.completedLFunction χ s ≠ 0) :
    ‖(logDeriv (DirichletCharacter.completedLFunction χ) s -
            logDeriv (DirichletCharacter.completedLFunction χ) 0) -
          completedLFunctionTruncatedGenusSum χ R s‖ ≤
      192 * ‖s‖ *
            ((4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
                Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
              1) /
          R ^ 2 +
        2 * ‖s‖ / R ^ 2 *
          (Real.log
              (max 1 (completedLFunctionBallBound N (2 * R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) := by
  have hR0 : 0 < R := by linarith
  obtain ⟨g, D⟩ := exists_ecanonicalDecomp_completedLFunction hne R
  have h0closed : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    simp only [Metric.mem_closedBall, dist_self, hR0.le]
  have hsclosed : s ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]; linarith
  have heq := ecanonicalDecomp_centered_logDeriv_eq hprimitive hne hR0 D hzf hsclosed hsne
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalyticClosed :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  set Dv :=
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) with
    hDv_def
  have hfin : (Function.support Dv).Finite :=
    hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have h0ne : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  have hkey : ∀ u ∈ hfin.toFinset, u ∈ Metric.ball (0 : ℂ) R ∧ u ≠ 0 ∧ s ≠ u := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    refine ⟨Dv.supportWithinDomain hu, ?_, ?_⟩
    · exact ne_of_mem_divisorBallSupport_of_completedLFunction_ne_zero hne hu h0ne
    · exact (ne_of_mem_divisorBallSupport_of_completedLFunction_ne_zero hne hu hsne).symm
  have hsub1 :
    Function.support (fun u : ℂ => ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) s) ⊆
      hfin.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu0; apply hu; rw [hDu0]; simp only [Int.cast_zero, neg_zero, zero_mul]
  have hsub2 :
    Function.support
        (fun u : ℂ => ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) (0 : ℂ)) ⊆
      hfin.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu0; apply hu; rw [hDu0]; simp only [Int.cast_zero, neg_zero, zero_mul]
  have hcombine :
    (∑ᶠ u : ℂ, ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) s) -
        (∑ᶠ u : ℂ, ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) 0) =
      completedLFunctionTruncatedGenusSum χ R s +
        ∑ᶠ u : ℂ,
          ((Dv u : ℤ) : ℂ) *
            ((starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * s) -
              (starRingEnd ℂ) u / (R : ℂ) ^ 2) := by
    rw [finsum_eq_sum_of_support_subset _ hsub1, finsum_eq_sum_of_support_subset _ hsub2, ←
      Finset.sum_sub_distrib]
    have hterm :
      ∀ u ∈ hfin.toFinset,
        ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) s -
            ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) 0 =
          ((Dv u : ℤ) : ℂ) * (1 / (s - u) + 1 / u) +
            ((Dv u : ℤ) : ℂ) *
              ((starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * s) -
                (starRingEnd ℂ) u / (R : ℂ) ^ 2) := by
      intro u hu
      obtain ⟨huball, hune0, hsneu⟩ := hkey u hu
      rw [← mul_sub, General.centered_logDeriv_canonicalFactor huball hsclosed hsneu hune0]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    congr 1
    · exact
        (finsum_eq_sum_of_support_subset _
            (by
              intro u hu
              rw [Function.mem_support] at hu
              rw [Set.Finite.coe_toFinset, Function.mem_support]
              intro hDu0; apply hu; rw [hDu0]; simp only [Int.cast_zero, zero_mul])).symm
    · exact
        (finsum_eq_sum_of_support_subset _
            (by
              intro u hu
              rw [Function.mem_support] at hu
              rw [Set.Finite.coe_toFinset, Function.mem_support]
              intro hDu0; apply hu; rw [hDu0]; simp only [Int.cast_zero, zero_mul])).symm
  rw [hcombine] at heq
  have hfinal :
    (logDeriv (DirichletCharacter.completedLFunction χ) s -
          logDeriv (DirichletCharacter.completedLFunction χ) 0) -
        completedLFunctionTruncatedGenusSum χ R s =
      (∑ᶠ u : ℂ,
          ((Dv u : ℤ) : ℂ) *
            ((starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * s) -
              (starRingEnd ℂ) u / (R : ℂ) ^ 2)) +
        (logDeriv g s - logDeriv g 0) := by
    rw [heq]; ring
  rw [hfinal]
  refine (norm_add_le _ _).trans ?_
  rw [add_comm]
  exact
    add_le_add (norm_logDeriv_ecanonicalDecomp_sub_le hN1 hprimitive hne hinv hR D hzf hs)
      (norm_canonicalCorrectionSum_le hN1 hprimitive hne hinv hR0 hs)

/-! ### the finite-radius estimate: the (untruncated) genus-one term at `s = 1` is absolutely
summable

Uses reciprocal-square weight summability
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.summable_completedLFunctionZeroWeight`) as a
majorant: for `‖ρ‖ ≥ 2` the genus-one
term at `s = 1` is `O(1/‖ρ‖²) = O(weight ρ)`, and the (finitely many) exceptions with `‖ρ‖ < 2`
are absorbed via `Summable.of_norm_bounded_eventually`. -/

/-- The genus-one series `Σ_ρ m_ρ(1/(1-ρ)+1/ρ)` (over the *global* divisor,
`Set.univ`) is absolutely summable. -/
theorem summable_completedLFunctionGenusOneTerm_one {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Summable
      (fun ρ : ℂ =>
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
          (1 / (1 - ρ) + 1 / ρ)) := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hanalyticClosed :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) 2) :=
    fun z _ => hdiff.analyticAt z
  have hfin2 :=
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) 2)).finiteSupport
      (isCompact_closedBall (x := (0 : ℂ)) (r := 2))
  have hmaj := (summable_completedLFunctionZeroWeight hN2 hprimitive hne hinv).mul_left (4 : ℝ)
  apply Summable.of_norm_bounded_eventually hmaj
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset hfin2
  intro ρ hρ
  simp only [Set.mem_ofPred_eq, not_le] at hρ
  by_contra hρ'
  rw [Function.mem_support, not_not] at hρ'
  apply absurd hρ
  rw [not_lt]
  have hanalyticUniv : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => hdiff.analyticAt z
  have hDnn :
    (0 : ℝ) ≤
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalyticUniv ρ
  by_cases hρball : ρ ∈ Metric.closedBall (0 : ℂ) 2
  · -- ρ ∈ closedBall 0 2 and divisor(closedBall) ρ = 0 ⟹ divisor(univ) ρ = 0 ⟹ term = 0
    have hdveq :
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ =
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) 2) ρ :=
      divisor_univ_eq_divisor_closedBall hne hρball
    rw [hdveq, hρ']
    simp only [Int.cast_zero, zero_mul, norm_zero]
    exact mul_nonneg (by norm_num only) (completedLFunctionZeroWeight_nonneg hne ρ)
  · -- ρ ∉ closedBall 0 2, i.e. ‖ρ‖ > 2: use the O(1/‖ρ‖²) bound
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hρball
    have h2ρ : (2 : ℝ) < ‖ρ‖ := hρball
    have hρ1 : ‖ρ‖ / 2 ≤ ‖(1 : ℂ) - ρ‖ := by
      have h1 : ‖ρ‖ - ‖(1 : ℂ)‖ ≤ ‖ρ - 1‖ := norm_sub_norm_le ρ 1
      rw [norm_one] at h1
      rw [show ‖(1 : ℂ) - ρ‖ = ‖ρ - 1‖ from norm_sub_rev 1 ρ]
      linarith
    have hρne0 : ρ ≠ 0 := by
      intro h
      rw [h] at h2ρ
      simp only [norm_zero] at h2ρ
      linarith
    have hρne1 : (1 : ℂ) - ρ ≠ 0 := by
      intro h
      have hρeq1 : ρ = 1 := by linear_combination -h
      rw [hρeq1] at h2ρ
      norm_num only [norm_one] at h2ρ
    have hterm : ‖(1 : ℂ) / (1 - ρ) + 1 / ρ‖ ≤ 2 / ‖ρ‖ ^ 2 := by
      have heq : (1 : ℂ) / (1 - ρ) + 1 / ρ = 1 / (ρ * (1 - ρ)) := by
        field_simp; ring
      rw [heq, norm_div, norm_mul, norm_one]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : ‖ρ‖ * (‖ρ‖ / 2) ≤ ‖ρ‖ * ‖(1 : ℂ) - ρ‖ :=
        mul_le_mul_of_nonneg_left hρ1 (norm_nonneg ρ)
      nlinarith [norm_nonneg ρ, sq_nonneg ‖ρ‖]
    have hDcast :
      ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ)‖ =
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) := by
      rw [Complex.norm_intCast, abs_of_nonneg hDnn]
    rw [norm_mul, hDcast]
    have hratio : (2 : ℝ) / ‖ρ‖ ^ 2 ≤ 4 / (1 + ‖ρ‖ ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h2ρ]
    have hcombine :
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (2 / ‖ρ‖ ^ 2) ≤
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
          (4 / (1 + ‖ρ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hratio hDnn
    calc
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            ‖(1 : ℂ) / (1 - ρ) + 1 / ρ‖ ≤
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (2 / ‖ρ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hterm hDnn
      _ ≤
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℝ) *
            (4 / (1 + ‖ρ‖ ^ 2)) :=
        hcombine
      _ = 4 * completedLFunctionZeroWeight χ ρ := by
        unfold completedLFunctionZeroWeight; ring

/-- A function with finite support has the same `tsum` (topological sum) and `finsum`
(algebraic, choice-based sum) — both reduce to the same `Finset.sum` over the support. -/
theorem tsum_eq_finsum_of_support_finite {f : ℂ → ℂ} (hfin : (Function.support f).Finite) :
    ∑' ρ, f ρ = ∑ᶠ ρ, f ρ := by
  rw [finsum_eq_sum_of_support_subset f (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset])]
  exact
    tsum_eq_sum
      (fun x hx => by
        by_contra hne
        exact hx (hfin.mem_toFinset.mpr (Function.mem_support.mpr hne)))

/-- Along the good-radius sequence, the truncated genus-one sum at one converges to the
full genus-one series. Rewrite the finite divisor sum as a truncated `tsum`, and apply
dominated convergence with the summable majorant `‖mρ * (1/(1-ρ)+1/ρ)‖`.
The radius sequence tends to infinity, so each truncation indicator eventually equals one. -/
theorem tendsto_truncatedGenusSum_one {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Filter.Tendsto
      (fun n : ℕ => completedLFunctionTruncatedGenusSum χ (completedLFunctionGoodRadius hne n) 1)
      Filter.atTop
      (nhds
        (∑' ρ : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
            (1 / (1 - ρ) + 1 / ρ))) := by
  set T : ℂ → ℂ := fun ρ =>
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
      (1 / (1 - ρ) + 1 / ρ) with
    hT_def
  set F : ℕ → ℂ → ℂ := fun n ρ => if ‖ρ‖ < completedLFunctionGoodRadius hne n then T ρ else 0 with
    hF_def
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have heqn :
    ∀ n : ℕ,
      completedLFunctionTruncatedGenusSum χ (completedLFunctionGoodRadius hne n) 1 =
        ∑' ρ : ℂ, F n ρ := by
    intro n
    have hanalyticClosed :
      AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (completedLFunctionGoodRadius hne n)) :=
      fun z _ => hdiff.analyticAt z
    have hfin :
      (Function.support
          (fun ρ : ℂ =>
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                    (Metric.ball (0 : ℂ) (completedLFunctionGoodRadius hne n)) ρ :
                  ℤ) :
                ℂ) *
              (1 / ((1 : ℂ) - ρ) + 1 / ρ))).Finite := by
      apply Set.Finite.subset (hanalyticClosed.meromorphicOn.divisor_ball_support_finite)
      intro ρ hρ
      rw [Function.mem_support] at hρ ⊢
      intro hD0; apply hρ; rw [hD0]; simp only [Int.cast_zero, one_div, zero_mul]
    unfold completedLFunctionTruncatedGenusSum
    rw [← tsum_eq_finsum_of_support_finite hfin]
    apply tsum_congr
    intro ρ
    simp only [hF_def]
    by_cases hρR : ‖ρ‖ < completedLFunctionGoodRadius hne n
    · rw [ite_eq_left hρR, hT_def]
      have hdeq :
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball (0 : ℂ) (completedLFunctionGoodRadius hne n)) ρ =
          MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ := by
        rw [divisor_ball_eq_if_univ hne, ite_eq_left hρR]
      rw [hdeq]
    · rw [ite_eq_right hρR]
      have hd0 :
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball (0 : ℂ) (completedLFunctionGoodRadius hne n)) ρ =
          0 := by
        rw [divisor_ball_eq_if_univ hne, ite_eq_right hρR]
      rw [hd0]; simp only [Int.cast_zero, one_div, zero_mul]
  simp_rw [heqn]
  have hmaj := (summable_completedLFunctionGenusOneTerm_one hN2 hprimitive hne hinv).norm
  have hab : ∀ ρ : ℂ, Filter.Tendsto (fun n => F n ρ) Filter.atTop (nhds (T ρ)) := by
    intro ρ
    have hev : (fun n => F n ρ) =ᶠ[Filter.atTop] (fun _ : ℕ => T ρ) := by
      filter_upwards [(tendsto_completedLFunctionGoodRadius_atTop hne).eventually_gt_atTop ‖ρ‖] with
        n hn
      simp only [hF_def, ite_eq_left hn]
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
  have h_bound : ∀ᶠ n in Filter.atTop, ∀ ρ, ‖F n ρ‖ ≤ ‖T ρ‖ := by
    apply Filter.Eventually.of_forall
    intro n ρ
    simp only [hF_def]
    split_ifs with h
    · exact le_refl _
    · simp only [norm_zero, norm_nonneg (T ρ)]
  exact tendsto_tsum_of_dominated_convergence hmaj hab h_bound

/-! ### Vanishing of the finite-radius error

Use the logarithmic-growth limit directly for the analytic-factor error and after replacing
`R` by `2R` for the Jensen correction involving the doubled ball envelope.
-/

/-- `(2R+3)·log(2R+3)/R² → 0`, obtained from
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.tendsto_add_mul_log_div_sq_atTop` via the
substitution `R ↦ 2R` (so `(2R+3)·log(2R+3)/(2R)² → 0`) and multiplying by `4`. -/
theorem tendsto_two_mul_add_mul_log_div_sq_atTop :
    Filter.Tendsto (fun R : ℝ => (2 * R + 3) * Real.log (2 * R + 3) / R ^ 2) Filter.atTop
      (nhds 0) := by
  have h2R : Filter.Tendsto (fun R : ℝ => 2 * R) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num only : (0 : ℝ) < 2) Filter.tendsto_id
  have hcomp :
    Filter.Tendsto (fun R : ℝ => (2 * R + 3) * Real.log (2 * R + 3) / (2 * R) ^ 2) Filter.atTop
      (nhds 0) :=
    tendsto_add_mul_log_div_sq_atTop.comp h2R
  have h4 :
    Filter.Tendsto (fun R : ℝ => (4 : ℝ) * ((2 * R + 3) * Real.log (2 * R + 3) / (2 * R) ^ 2))
      Filter.atTop (nhds 0) := by
    have := hcomp.const_mul (4 : ℝ)
    simpa only [mul_zero] using this
  refine h4.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
  have hRne : R ≠ 0 := hR.ne'
  field_simp
  ring

/-- The finite-radius error term of
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_centeredLogDeriv_sub_truncatedGenus_le`
(specialized to `s = 1`) vanishes as `R → ∞`. -/
theorem tendsto_h9dError_atTop {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Filter.Tendsto
      (fun R : ℝ =>
        2 * 1 / R ^ 2 *
          (Real.log
              (max 1 (completedLFunctionBallBound N (2 * R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2))
      Filter.atTop (nhds 0) := by
  have hN1 : 1 < N := by omega
  have hF0_pos : (0 : ℝ) < ‖DirichletCharacter.completedLFunction χ 0‖ :=
    norm_pos_iff.mpr (dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne)
  have hupper :
    Filter.Tendsto
      (fun R : ℝ =>
        2 / R ^ 2 *
          (((4 * (N : ℝ) + 3) * (2 * R + 3) * Real.log (2 * R + 3) -
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2))
      Filter.atTop (nhds 0) := by
    have h1 :
      Filter.Tendsto
        (fun R : ℝ =>
          (4 * (N : ℝ) + 3) * ((2 * R + 3) * Real.log (2 * R + 3)) / R ^ 2 -
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖ / R ^ 2 -
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖ / R ^ 2 +
            Real.log ‖DirichletCharacter.completedLFunction χ 0‖ / R ^ 2)
        Filter.atTop (nhds 0) := by
      have ha :
        Filter.Tendsto
          (fun R : ℝ => (4 * (N : ℝ) + 3) * ((2 * R + 3) * Real.log (2 * R + 3)) / R ^ 2)
          Filter.atTop (nhds 0) := by
        have := tendsto_two_mul_add_mul_log_div_sq_atTop.const_mul (4 * (N : ℝ) + 3)
        simpa only [mul_div_assoc, mul_zero] using this
      have hb :
        Filter.Tendsto (fun R : ℝ => Real.log ‖DirichletCharacter.completedLFunction χ 0‖ / R ^ 2)
          Filter.atTop (nhds 0) := by
        have hinv2 : Filter.Tendsto (fun R : ℝ => (R ^ 2)⁻¹) Filter.atTop (nhds 0) := by
          exact tendsto_inv_atTop_zero.comp (Filter.tendsto_pow_atTop (two_ne_zero))
        have := hinv2.const_mul (Real.log ‖DirichletCharacter.completedLFunction χ 0‖)
        simpa only [div_eq_mul_inv, mul_zero] using this
      have := (ha.sub hb).sub hb |>.add hb
      simpa only [sub_add_cancel, sub_self, add_zero] using this
    have h1' :
      Filter.Tendsto
        (fun R : ℝ =>
          ((4 * (N : ℝ) + 3) * ((2 * R + 3) * Real.log (2 * R + 3)) / R ^ 2 -
                Real.log ‖DirichletCharacter.completedLFunction χ 0‖ / R ^ 2 -
                Real.log ‖DirichletCharacter.completedLFunction χ 0‖ / R ^ 2 +
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖ / R ^ 2) *
            2)
        Filter.atTop (nhds 0) := by
      have := h1.mul_const (2 : ℝ)
      simpa only [sub_add_cancel, zero_mul] using this
    have hdiv := h1'.div_const (Real.log 2)
    simp only [zero_div] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    have hRne : R ≠ 0 := hR.ne'
    field_simp
    ring
  have h0le :
    ∀ᶠ R in Filter.atTop,
      (0 : ℝ) ≤
        2 * 1 / R ^ 2 *
          (Real.log
              (max 1 (completedLFunctionBallBound N (2 * R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
    have hR0 : 0 < R := by linarith
    have h0R : ‖(0 : ℂ)‖ ≤ 2 * R := by
      rw [norm_zero]; linarith
    have hboundge :
      ‖DirichletCharacter.completedLFunction χ 0‖ ≤ completedLFunctionBallBound N (2 * R) :=
      norm_completedLFunction_le_completedLFunctionBallBound hN1 hprimitive hne hinv (by linarith)
        h0R
    have hle :
      ‖DirichletCharacter.completedLFunction χ 0‖ ≤ max 1 (completedLFunctionBallBound N (2 * R)) :=
      le_max_of_le_right hboundge
    have hlog_nonneg :
      0 ≤
        Real.log
          (max 1 (completedLFunctionBallBound N (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) :=
      Real.log_nonneg ((one_le_div hF0_pos).mpr hle)
    positivity
  have hle :
    ∀ᶠ R in Filter.atTop,
      2 * 1 / R ^ 2 *
          (Real.log
              (max 1 (completedLFunctionBallBound N (2 * R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) ≤
        2 / R ^ 2 *
          (((4 * (N : ℝ) + 3) * (2 * R + 3) * Real.log (2 * R + 3) -
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
    have hR0 : 0 < R := by linarith
    have h2Rpos : (0 : ℝ) < 2 * R := by linarith
    have h0R : ‖(0 : ℂ)‖ ≤ 2 * R := by
      rw [norm_zero]; linarith
    have hboundge :
      ‖DirichletCharacter.completedLFunction χ 0‖ ≤ completedLFunctionBallBound N (2 * R) :=
      norm_completedLFunction_le_completedLFunctionBallBound hN1 hprimitive hne hinv (by linarith)
        h0R
    have hboundpos : (0 : ℝ) < completedLFunctionBallBound N (2 * R) := hF0_pos.trans_le hboundge
    have hexp0 := completedLFunctionBallBound_le_exp (N := N) hN2 (show (1 : ℝ) ≤ 2 * R by linarith)
    have hexp :
      completedLFunctionBallBound N (2 * R) ≤
        Real.exp ((4 * (N : ℝ) + 3) * (2 * R + 3) * Real.log (2 * R + 3)) := by
      rw [show
          (4 * (N : ℝ) + 3) * (2 * R + 3) * Real.log (2 * R + 3) =
            (4 * (N : ℝ) + 3) * ((2 * R + 3) * Real.log (2 * R + 3))
          from by ring]
      exact hexp0
    have hexp_ge1 :
      (1 : ℝ) ≤ Real.exp ((4 * (N : ℝ) + 3) * (2 * R + 3) * Real.log (2 * R + 3)) := by
      apply Real.one_le_exp
      have hL : (0 : ℝ) ≤ Real.log (2 * R + 3) := Real.log_nonneg (by linarith)
      positivity
    have hmax_le :
      max 1 (completedLFunctionBallBound N (2 * R)) ≤
        Real.exp ((4 * (N : ℝ) + 3) * (2 * R + 3) * Real.log (2 * R + 3)) :=
      max_le hexp_ge1 hexp
    have hlog_le :
      Real.log
          (max 1 (completedLFunctionBallBound N (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) ≤
        (4 * (N : ℝ) + 3) * (2 * R + 3) * Real.log (2 * R + 3) -
          Real.log ‖DirichletCharacter.completedLFunction χ 0‖ := by
      rw [Real.log_div (by positivity) hF0_pos.ne']
      have := Real.log_le_log (by positivity) hmax_le
      rw [Real.log_exp] at this
      linarith
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num only)
    have h1 : 2 * 1 / R ^ 2 ≤ 2 / R ^ 2 := by rw [mul_one]
    have h2 :
      Real.log
            (max 1 (completedLFunctionBallBound N (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 ≤
        ((4 * (N : ℝ) + 3) * (2 * R + 3) * Real.log (2 * R + 3) -
            Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 :=
      div_le_div_of_nonneg_right hlog_le hlog2pos.le
    calc
      2 * 1 / R ^ 2 *
            (Real.log
                (max 1 (completedLFunctionBallBound N (2 * R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) ≤
          2 / R ^ 2 *
            (Real.log
                (max 1 (completedLFunctionBallBound N (2 * R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) :=
        by
        apply mul_le_mul_of_nonneg_right h1
        apply div_nonneg
        · exact Real.log_nonneg ((one_le_div hF0_pos).mpr (le_max_of_le_right hboundge))
        · exact hlog2pos.le
      _ ≤
          2 / R ^ 2 *
            (((4 * (N : ℝ) + 3) * (2 * R + 3) * Real.log (2 * R + 3) -
                Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) :=
        by apply mul_le_mul_of_nonneg_left h2 (by positivity)
  exact squeeze_zero' h0le hle hupper

/-- For a primitive nontrivial character at level `N ≥ 2`, with nontrivial inverse, the
centered logarithmic derivative at one equals the full multiplicity-weighted genus-one series.
Apply the finite-radius estimate along the good-radius sequence; both errors tend to zero,
and `tendsto_truncatedGenusSum_one` gives the series limit. Uniqueness of limits proves equality.
This supplies the completed functional-equation zero-mass identities. -/
theorem completedLFunction_centeredLogDeriv_one_eq_tsum {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    logDeriv (DirichletCharacter.completedLFunction χ) 1 -
        logDeriv (DirichletCharacter.completedLFunction χ) 0 =
      ∑' ρ : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
          (1 / (1 - ρ) + 1 / ρ) := by
  have hN1 : 1 < N := by omega
  have h1ne : DirichletCharacter.completedLFunction χ 1 ≠ 0 :=
    dirichletCompletedLFunction_one_ne_zero_of_ne_one hne
  set centered :=
    logDeriv (DirichletCharacter.completedLFunction χ) 1 -
      logDeriv (DirichletCharacter.completedLFunction χ) 0 with
    hcentered_def
  set R : ℕ → ℝ := completedLFunctionGoodRadius hne with hR_def
  have hbound :
    ∀ n : ℕ,
      ‖centered - completedLFunctionTruncatedGenusSum χ (R n) 1‖ ≤
        192 * (1 : ℝ) *
              ((4 * (N : ℝ) + 3) * (R n + 3) * Real.log (R n + 3) -
                  Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                1) /
            (R n) ^ 2 +
          2 * (1 : ℝ) / (R n) ^ 2 *
            (Real.log
                (max 1 (completedLFunctionBallBound N (2 * R n)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) := by
    intro n
    have hRgt : (n : ℝ) + 2 < R n := completedLFunctionGoodRadius_gt hne n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hR1 : (1 : ℝ) ≤ R n := by linarith
    have hs : ‖(1 : ℂ)‖ ≤ R n / 2 := by
      rw [norm_one]; linarith
    have hb :=
      norm_centeredLogDeriv_sub_truncatedGenus_le hN1 hprimitive hne hinv hR1
        (completedLFunctionGoodRadius_zeroFree hne n) hs h1ne
    simpa only [hcentered_def, mul_one, ge_iff_le, norm_one] using hb
  have herr0 :
    Filter.Tendsto (fun n : ℕ => centered - completedLFunctionTruncatedGenusSum χ (R n) 1)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm hbound
    have h8 :=
      (tendsto_const_mul_add_mul_log_add_const_div_sq_atTop 192 (4 * (N : ℝ) + 3)
            (-Real.log ‖DirichletCharacter.completedLFunction χ 0‖ + 1)).comp
        (tendsto_completedLFunctionGoodRadius_atTop hne)
    have h9d :=
      (tendsto_h9dError_atTop hN2 hprimitive hne hinv).comp
        (tendsto_completedLFunctionGoodRadius_atTop hne)
    have hsum := h8.add h9d
    simp only [zero_add] at hsum
    refine hsum.congr (fun n => ?_)
    simp only [Function.comp]
    ring
  have hto :
    Filter.Tendsto (fun n : ℕ => completedLFunctionTruncatedGenusSum χ (R n) 1) Filter.atTop
      (nhds centered) := by
    have hcs :
      Filter.Tendsto
        (fun n : ℕ => centered - (centered - completedLFunctionTruncatedGenusSum χ (R n) 1))
        Filter.atTop (nhds (centered - 0)) :=
      tendsto_const_nhds.sub herr0
    simpa only [sub_sub_cancel, sub_zero] using hcs
  have htsum := tendsto_truncatedGenusSum_one hN2 hprimitive hne hinv
  exact tendsto_nhds_unique hto htsum

/--
Input/assumptions: none.
Conclusion:
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunctionTruncatedGenusSum χ R 0 = 0`.
Content: each summand `D_ρ * (1/(0-ρ) + 1/ρ)` vanishes pointwise (for `ρ ≠ 0` since
`1/(-ρ) = -(1/ρ)`, and for `ρ = 0` by the `1/0 = 0` convention), so the `finsum` is `0`.
Role: the base point for differentiating the truncated genus sum at `s = 0`.
-/
theorem completedLFunctionTruncatedGenusSum_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (R : ℝ) : completedLFunctionTruncatedGenusSum χ R 0 = 0 := by
  have heq :
    (fun ρ : ℂ =>
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                ρ :
              ℤ) :
            ℂ) *
          (1 / ((0 : ℂ) - ρ) + 1 / ρ)) =
      fun _ => (0 : ℂ) := by
    funext ρ
    by_cases hρ : ρ = 0
    · simp only [hρ, sub_self, div_zero, add_zero, mul_zero]
    · have h1 : (1 : ℂ) / ((0 : ℂ) - ρ) = -(1 / ρ) := by rw [zero_sub, one_div, one_div, inv_neg]
      rw [h1]; ring
  rw [completedLFunctionTruncatedGenusSum, heq, finsum_zero]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
