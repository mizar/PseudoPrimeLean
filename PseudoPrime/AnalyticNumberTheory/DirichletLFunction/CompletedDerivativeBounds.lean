/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedVerticalGrowth
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GrowthBounds
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Uniform derivatives of completed Dirichlet logarithmic derivatives

The Euler half-plane gives a modulus-independent bound on a disk around real 3/2.
Parity separates the gamma factors into two fixed analytic functions. Cauchy estimates
then bound every derivative order uniformly in the nonprincipal character.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The closed radius-one-quarter disk centered at real 3/2 lies in Re z >= 5/4.
Bound the real part of the difference by its norm. This keeps the Cauchy contour inside
the zero-free Euler half-plane for every character. -/
theorem re_ge_of_mem_completed_derivative_disk {z : ℂ}
    (hz : z ∈ Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 4)) : (5 / 4 : ℝ) ≤ z.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h := Complex.re_le_norm (((3 / 2 : ℝ) : ℂ) - z)
  rw [Complex.sub_re, Complex.ofReal_re, norm_sub_rev] at h
  linarith only [h, hz]

/-- The gamma logarithmic derivatives of all Dirichlet characters are bounded by one positive
constant on the closed disk centered at real 3/2 with radius one quarter.
Reduce the two parities to the modulus-one factor at z or z+1 and use compactness and
analytic nonvanishing. The bound is independent of the modulus and character. -/
theorem exists_uniform_norm_gammaFactor_completed_derivative_disk :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (z : ℂ),
          z ∈ Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 4) → ‖logDeriv χ.gammaFactor z‖ ≤ C := by
  let G := (1 : DirichletCharacter ℂ 1).gammaFactor
  have hcont : ContinuousOn (logDeriv G) (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 4)) := by
    intro z hz
    have hr : 0 < z.re := by linarith only [re_ge_of_mem_completed_derivative_disk hz]
    have hf := analyticAt_gammaFactor_of_re_pos (1 : DirichletCharacter ℂ 1) hr
    have ha : AnalyticAt ℂ (logDeriv G) z :=
      hf.deriv.div hf (gammaFactor_ne_zero_of_re_pos (1 : DirichletCharacter ℂ 1) hr)
    exact ha.continuousAt.continuousWithinAt
  have hshift :
    ContinuousOn (fun z : ℂ ↦ logDeriv G (z + 1))
      (Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 4)) := by
    intro z hz
    have hr : 0 < (z + 1).re := by
      rw [Complex.add_re, Complex.one_re]
      linarith only [re_ge_of_mem_completed_derivative_disk hz]
    have hf := analyticAt_gammaFactor_of_re_pos (1 : DirichletCharacter ℂ 1) hr
    have ha : AnalyticAt ℂ (logDeriv G) (z + 1) :=
      hf.deriv.div hf (gammaFactor_ne_zero_of_re_pos (1 : DirichletCharacter ℂ 1) hr)
    exact
      (ha.continuousAt.comp (f := fun w : ℂ ↦ w + 1)
          (continuousAt_id.add_const 1)).continuousWithinAt
  have hc := isCompact_closedBall (((3 / 2 : ℝ) : ℂ)) (1 / 4)
  obtain ⟨M0, hb0⟩ := hc.exists_bound_of_continuousOn hcont
  obtain ⟨M1, hb1⟩ := hc.exists_bound_of_continuousOn hshift
  refine ⟨|M0| + |M1| + 1, by linarith only [abs_nonneg M0, abs_nonneg M1], ?_⟩
  intro q χ z hz
  have hr : 0 < z.re := by linarith only [re_ge_of_mem_completed_derivative_disk hz]
  rcases logDeriv_gammaFactor_eq_one_or_one_shift χ hr with he | he
  · rw [he]
    have hb := hb0 z hz
    change ‖logDeriv G z‖ ≤ _
    linarith only [hb, le_abs_self M0, abs_nonneg M1]
  · rw [he]
    have hb := hb1 z hz
    change ‖logDeriv G (z + 1)‖ ≤ _
    linarith only [hb, le_abs_self M1, abs_nonneg M0]

/-- On the fixed disk centered at real 3/2 with radius one quarter, every character's ordinary
logarithmic derivative is bounded by the untwisted Mangoldt series at real 5/4.
Expand the Euler logarithmic derivative and use the exponent monotonicity of the positive
series. This is the arithmetic part of the modulus-uniform Cauchy bound. -/
theorem norm_ordinary_logDeriv_completed_derivative_disk_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z : ℂ} (hz : z ∈ Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 4)) :
    ‖logDeriv χ.LFunction z‖ ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5 / 4 : ℝ) := by
  have hr := re_ge_of_mem_completed_derivative_disk hz
  have h1 : 1 < z.re := by linarith only [hr]
  have hn := norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ h1 z.im
  rw [Complex.re_add_im] at hn
  have hm :=
    RiemannZeta.tsum_vonMangoldt_div_rpow_antitone (show (1 : ℝ) < 5 / 4 by norm_num only) hr
  simpa only [neg_div, norm_neg, logDeriv_apply, mul_comm] using hn.trans hm

/-- For nonprincipal characters, completed logarithmic derivatives have one positive uniform
bound on the closed disk centered at real 3/2 with radius one quarter, without RH.
Separate the ordinary logarithmic derivative and gamma factor and add their uniform bounds.
This controls all derivatives at the center by the Cauchy estimate. -/
theorem exists_uniform_norm_completed_logDeriv_disk_le :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ ≠ 1 →
            ∀ z : ℂ,
              z ∈ Metric.closedBall ((3 / 2 : ℝ) : ℂ) (1 / 4) →
                ‖logDeriv χ.completedLFunction z‖ ≤ C := by
  obtain ⟨A, hA, hb⟩ := exists_uniform_norm_gammaFactor_completed_derivative_disk
  let M := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5 / 4 : ℝ)
  have hM : 0 ≤ M :=
    tsum_nonneg
      (fun n ↦
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  refine ⟨M + A, add_pos_of_nonneg_of_pos hM hA, ?_⟩
  intro q _ χ hne z hz
  have hr : 1 ≤ z.re := by linarith only [re_ge_of_mem_completed_derivative_disk hz]
  have hp : 0 < z.re := zero_lt_one.trans_le hr
  have he :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hr) (gammaFactor_ne_zero_of_re_pos χ hp)
      (analyticAt_gammaFactor_of_re_pos χ hp).differentiableAt
  have hf :
    logDeriv χ.completedLFunction z = logDeriv χ.LFunction z + logDeriv χ.gammaFactor z := by
    rw [he]
    ring
  rw [hf]
  exact
    (norm_add_le _ _).trans
      (add_le_add (norm_ordinary_logDeriv_completed_derivative_disk_le χ hz) (hb q χ z hz))

/-- For every natural derivative order, a positive bound for the iterated completed logarithmic
derivative at real 3/2 works for all nonprincipal characters and moduli, without RH.
Analytic nonvanishing gives differentiability and boundary continuity on the fixed disk;
the uniform disk bound and Cauchy estimate supply the factorial and radius-power coefficient.
This bounds the inverse-power zero moments used in conductor-normalized distribution limits. -/
theorem exists_uniform_norm_iteratedDeriv_completed_logDeriv_le (n : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ ≠ 1 → ‖iteratedDeriv n (logDeriv χ.completedLFunction) (((3 / 2 : ℝ) : ℂ))‖ ≤ C := by
  obtain ⟨A, hA, hb⟩ := exists_uniform_norm_completed_logDeriv_disk_le
  have hr : (0 : ℝ) < 1 / 4 := by norm_num only
  have hfactor : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  refine ⟨(n.factorial : ℝ) * A / (1 / 4 : ℝ) ^ n, div_pos (mul_pos hfactor hA) (pow_pos hr n), ?_⟩
  intro q _ χ hne
  have ha :
    ∀ z ∈ Metric.closedBall (((3 / 2 : ℝ) : ℂ)) (1 / 4),
      AnalyticAt ℂ (logDeriv χ.completedLFunction) z := by
    intro z hz
    have hrz : 1 ≤ z.re := by linarith only [re_ge_of_mem_completed_derivative_disk hz]
    have hF := (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
    exact hF.deriv.div hF (completedLFunction_ne_zero_of_one_le_re hne hrz)
  have hd :
    DifferentiableOn ℂ (logDeriv χ.completedLFunction)
      (Metric.closedBall (((3 / 2 : ℝ) : ℂ)) (1 / 4)) :=
    fun z hz ↦ (ha z hz).differentiableAt.differentiableWithinAt
  have hc :
    ContinuousOn (logDeriv χ.completedLFunction) (Metric.closedBall (((3 / 2 : ℝ) : ℂ)) (1 / 4)) :=
    fun z hz ↦ (ha z hz).continuousAt.continuousWithinAt
  exact
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
      (DiffContOnCl.mk_ball (hd.mono Metric.ball_subset_closedBall) hc)
      (fun z hz ↦ hb q χ hne z (Metric.sphere_subset_closedBall hz))

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
