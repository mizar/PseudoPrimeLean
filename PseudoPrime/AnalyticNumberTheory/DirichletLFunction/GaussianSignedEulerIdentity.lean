/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaSignedEulerIdentity
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GaussianResolventZeroMass
public import PseudoPrime.Analysis.GaussianSignedEulerSeries

/-! # Exact signed Gaussian Poisson and Euler identities -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The actual Gaussian resolvent zero mass equals the finite signed combination
of exact conductor, Gaussian and ordinary derivative terms. The certified nodes
all lie to the right of one after shifting by one half. Apply the node identity
before any bound, retaining negative coefficients in the common combination. -/
theorem gaussianResolvent_zeroMass_eq_signed_derivatives {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gaussianResolventMajorant ρ.im) =
      (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re +
                (logDeriv χ.LFunction (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re))).sum := by
  rw [gaussianResolvent_zeroMass_eq_poissonSum hq hRH hp hne hinv]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  have ha := List.forall_iff_forall_mem.mp Analysis.gaussianResolvent_scales_gt_half ab hab
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

/-- The signed Gaussian zero mass separates into its exact conductor coefficient
11783423/25000000, signed Gaussian derivatives and signed ordinary derivatives.
Evaluate the certified finite rational coefficients after the exact node
identity, preserving their signs. This is the conductor-normalized Poisson
identity to be matched with the common Euler weight and local budget. -/
theorem gaussianResolvent_zeroMass_eq_conductor_signed_derivatives {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gaussianResolventMajorant ρ.im) =
      (20115621 / 50000000 : ℝ) * Real.log q +
        (Analysis.gaussianResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        (Analysis.gaussianResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv χ.LFunction (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum := by
  rw [gaussianResolvent_zeroMass_eq_signed_derivatives hq hRH hp hne hinv]
  norm_num only [Analysis.gaussianResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  ring

/-- The finite signed ordinary-derivative combination equals the single
character Euler series weighted by the actual common Gaussian Mangoldt weight.
Absolute convergence permits interchanging the finite coefficient list and
the infinite series. Coefficient signs are retained before estimating prefixes. -/
theorem gaussianResolvent_signed_ordinary_eq_euler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦ (ab.2 : ℝ) * (logDeriv χ.LFunction (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum =
      ∑' n : ℕ, -(χ n).re * Analysis.gaussianResolventMangoldtWeight n := by
  let f := fun (ab : ℚ × ℚ) (n : ℕ) ↦
    (ab.2 : ℝ) *
      (-((χ n).re * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ ((1 / 2 : ℝ) + (ab.1 : ℝ))))
  have hσ (ab : ℚ × ℚ) (hab : ab ∈ Analysis.gaussianResolventCoefficients) :
    1 < (1 / 2 : ℝ) + (ab.1 : ℝ) := by
    have ha := List.forall_iff_forall_mem.mp Analysis.gaussianResolvent_scales_gt_half ab hab
    have h : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) := Rat.cast_lt.mpr ha
    norm_num only at h
    linarith only [h]
  have hs (ab : ℚ × ℚ) (hab : ab ∈ Analysis.gaussianResolventCoefficients) : Summable (f ab) :=
    ((summable_real_twistedMangoldt χ (hσ ab hab)).neg).mul_left (ab.2 : ℝ)
  have he (n : ℕ) :
    -(χ n).re * Analysis.gaussianResolventMangoldtWeight n =
      (Analysis.gaussianResolventCoefficients.map (fun ab ↦ f ab n)).sum := by
    dsimp only [f, Analysis.gaussianResolventMangoldtWeight, Analysis.gaussianResolventEulerWeight]
    norm_num only [Analysis.gaussianResolventCoefficients, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    simp only [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    ring
  rw [tsum_congr he, Analysis.tsum_list_sum Analysis.gaussianResolventCoefficients f hs]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  dsimp only [f]
  rw [← Complex.ofReal_add, re_logDeriv_eq_signed_Mangoldt_tsum χ (hσ ab hab), tsum_mul_left,
    tsum_neg]

/-- Under individual RH and primitive nonprincipal conductor data, the actual
Gaussian resolvent zero mass equals its exact conductor contribution, signed
Gaussian-node contribution and the common-weight Euler series. Both the Poisson
and Euler identities are discharged. This is the exact signed comparison
used before absorbing the local nonunit correction. -/
theorem gaussianResolvent_zeroMass_eq_signed_euler {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gaussianResolventMajorant ρ.im) =
      (20115621 / 50000000 : ℝ) * Real.log q +
        (Analysis.gaussianResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        ∑' n : ℕ, -(χ n).re * Analysis.gaussianResolventMangoldtWeight n := by
  rw [gaussianResolvent_zeroMass_eq_conductor_signed_derivatives hq hRH hp hne hinv,
    gaussianResolvent_signed_ordinary_eq_euler χ]

/-- The actual Gaussian zero mass obeys the signed prefix upper bound under
individual RH and primitive nonprincipal conductor data. The common Euler
weight gives twice the prefix gain, and its nonunit correction is retained
exactly. This is the zero-side interface for the joint local conductor budget. -/
theorem gaussianResolvent_zeroMass_le_signed_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (B : Finset ℕ) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gaussianResolventMajorant ρ.im) ≤
      (20115621 / 50000000 : ℝ) * Real.log q +
            (Analysis.gaussianResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' n : ℕ, Analysis.gaussianResolventMangoldtWeight n) -
          2 * (∑ n ∈ B, Analysis.gaussianResolventMangoldtWeight n) +
        ∑ n ∈ B, (1 - (χ n).re) * Analysis.gaussianResolventMangoldtWeight n := by
  rw [gaussianResolvent_zeroMass_eq_signed_euler hq hRH hp hne hinv]
  have h := Analysis.gaussian_character_signed_euler_prefix_le χ B
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
