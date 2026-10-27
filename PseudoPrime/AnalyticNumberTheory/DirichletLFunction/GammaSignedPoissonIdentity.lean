/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaResolventZeroMass
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonNumericalBounds
public import PseudoPrime.Analysis.GammaSignedEulerSeries

/-! # Exact signed Gamma Poisson decomposition -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character under individual RH, the Poisson
sum to the right of one is exactly the conductor term plus the signed Gamma
and ordinary logarithmic derivatives. No absolute-value estimate is taken.
This node identity is used before combining the signed resolvent coefficients. -/
theorem completed_poissonSum_eq_signed_ordinary {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : 1 < σ) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ((σ - 1 / 2) / Complex.normSq ((σ : ℂ) - ρ))) =
      Real.log q / 2 + (logDeriv χ.gammaFactor (σ : ℂ)).re + (logDeriv χ.LFunction (σ : ℂ)).re := by
  have hr : 0 < (σ : ℂ).re := by simpa only [Complex.ofReal_re] using zero_lt_one.trans hσ
  have hs : 1 / 2 < (σ : ℂ).re := by
    simp only [Complex.ofReal_re]
    linarith only [hσ]
  have he := completed_poissonSum_eq_logDeriv_re hq hRH hp hne hinv hs
  simp only [Complex.ofReal_re] at he
  have hd :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hσ.le) (gammaFactor_ne_zero_of_re_pos χ hr)
      (analyticAt_gammaFactor_of_re_pos χ hr).differentiableAt
  have hf :
    logDeriv χ.completedLFunction (σ : ℂ) =
      logDeriv χ.LFunction (σ : ℂ) + logDeriv χ.gammaFactor (σ : ℂ) := by
    rw [hd]
    ring
  rw [he, hf, Complex.add_re]
  ring

/-- The actual Gamma resolvent zero mass equals the finite signed combination
of exact conductor, Gamma and ordinary derivative terms. The certified nodes
all lie to the right of one after shifting by one half. Apply the node identity
before any bound, retaining negative coefficients in the common combination. -/
theorem gammaResolvent_zeroMass_eq_signed_derivatives {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) =
      (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re +
                (logDeriv χ.LFunction (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re))).sum := by
  rw [gammaResolvent_zeroMass_eq_poissonSum hq hRH hp hne hinv]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  have ha := List.forall_iff_forall_mem.mp Analysis.gammaResolvent_scales_gt_half ab hab
  have har : (1 / 2 : ℝ) < (ab.1 : ℝ) := by
    have h : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) := Rat.cast_lt.mpr ha
    norm_num only at h
    exact h
  have hσ : 1 < (1 / 2 : ℝ) + (ab.1 : ℝ) := by linarith only [har]
  have h := completed_poissonSum_eq_signed_ordinary hq hRH hp hne hinv hσ
  have he : (1 / 2 : ℝ) + (ab.1 : ℝ) - 1 / 2 = (ab.1 : ℝ) := by ring
  rw [he] at h
  simp only [Complex.ofReal_add] at h
  rw [h]

/-- The signed Gamma zero mass separates into its exact conductor coefficient
11783423/25000000, signed Gamma derivatives and signed ordinary derivatives.
Evaluate the certified finite rational coefficients after the exact node
identity, preserving their signs. This is the conductor-normalized Poisson
identity to be matched with the common Euler weight and local budget. -/
theorem gammaResolvent_zeroMass_eq_conductor_signed_derivatives {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) =
      (11783423 / 25000000 : ℝ) * Real.log q +
        (Analysis.gammaResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        (Analysis.gammaResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv χ.LFunction (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum := by
  rw [gammaResolvent_zeroMass_eq_signed_derivatives hq hRH hp hne hinv]
  norm_num only [Analysis.gammaResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
