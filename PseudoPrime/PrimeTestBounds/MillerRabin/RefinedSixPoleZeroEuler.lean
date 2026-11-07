/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerReal

/-! # Exact refined sixth-pole zero mass with signed Euler correction -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For complex functions analytic on the shifted real half-line, the first
and second derivatives of their real-part sum split into the sums of the
corresponding derivatives. Pointwise analyticity supplies a neighborhood of
differentiability for the first derivatives. This separates Gamma and Euler
contributions in the sixth-pole zero formula. -/
theorem real_shift_sum_derivs (f g : ℂ → ℂ) {a : ℝ} (ha : 1 / 2 < a)
    (hf : ∀ u : ℝ, 1 / 2 < u → AnalyticAt ℂ f (((1 / 2 : ℝ) + u : ℝ) : ℂ))
    (hg : ∀ u : ℝ, 1 / 2 < u → AnalyticAt ℂ g (((1 / 2 : ℝ) + u : ℝ) : ℂ)) :
    let F : ℝ → ℝ := fun u ↦ (f (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
    let G : ℝ → ℝ := fun u ↦ (g (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
    deriv (fun u ↦ F u + G u) a = deriv F a + deriv G a ∧
      deriv (deriv (fun u ↦ F u + G u)) a = deriv (deriv F) a + deriv (deriv G) a := by
  let F : ℝ → ℝ := fun u ↦ (f (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
  let G : ℝ → ℝ := fun u ↦ (g (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
  have hd (h : ℂ → ℂ) (hh : ∀ u : ℝ, 1 / 2 < u → AnalyticAt ℂ h (((1 / 2 : ℝ) + u : ℝ) : ℂ)) (u : ℝ)
    (hu : 1 / 2 < u) :
    HasDerivAt (fun v : ℝ ↦ (h (((1 / 2 : ℝ) + v : ℝ) : ℂ)).re)
      (deriv h (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re u := by
    have H := (hh u hu).differentiableAt.hasDerivAt.real_of_complex
    have H' := H.comp u ((hasDerivAt_id u).const_add (1 / 2 : ℝ))
    simpa only [mul_one, Function.comp_def] using H'
  have hF (u : ℝ) (hu : 1 / 2 < u) : DifferentiableAt ℝ F u := (hd f hf u hu).differentiableAt
  have hG (u : ℝ) (hu : 1 / 2 < u) : DifferentiableAt ℝ G u := (hd g hg u hu).differentiableAt
  have he : deriv (fun u ↦ F u + G u) =ᶠ[nhds a] fun u ↦ deriv F u + deriv G u := by
    filter_upwards [Ioi_mem_nhds ha] with u hu
    exact deriv_add (hF u hu) (hG u hu)
  have hdF : DifferentiableAt ℝ (deriv F) a := by
    have h := (hf a ha).deriv.differentiableAt.hasDerivAt.real_of_complex
    have h' := h.comp a ((hasDerivAt_id a).const_add (1 / 2 : ℝ))
    have heF : deriv F =ᶠ[nhds a] fun u : ℝ ↦ (deriv f (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re := by
      filter_upwards [Ioi_mem_nhds ha] with u hu
      exact (hd f hf u hu).deriv
    exact
      (heF.differentiableAt_iff).mpr
        (by simpa only [mul_one, Function.comp_def] using h'.differentiableAt)
  have hdG : DifferentiableAt ℝ (deriv G) a := by
    have h := (hg a ha).deriv.differentiableAt.hasDerivAt.real_of_complex
    have h' := h.comp a ((hasDerivAt_id a).const_add (1 / 2 : ℝ))
    have heG : deriv G =ᶠ[nhds a] fun u : ℝ ↦ (deriv g (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re := by
      filter_upwards [Ioi_mem_nhds ha] with u hu
      exact (hd g hg u hu).deriv
    exact
      (heG.differentiableAt_iff).mpr
        (by simpa only [mul_one, Function.comp_def] using h'.differentiableAt)
  constructor
  · exact deriv_add (hF a ha) (hG a ha)
  · rw [he.deriv_eq]
    exact deriv_add hdF hdG

/-- Under individual RH, the normalized sixth-pole zero mass equals its
conductor term and the explicit Gamma differential expression minus the
signed refined Euler series. The Poisson formula, analytic derivative
splitting, and the Euler identity retain the signs needed for the subsequent
three-character prefix estimate. -/
theorem refined_six_pole_formula_euler {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) :
    let G : ℝ → ℝ := fun u ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
    8 *
        (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖refinedSixPoleKernel.function (Complex.I * ρ.im)‖) =
      (3 / 2 : ℝ) * Real.log q + 3 * G (27 / 25) - (81 / 25 : ℝ) * deriv G (27 / 25) +
          (729 / 625 : ℝ) * deriv (deriv G) (27 / 25) -
        8 * ∑' n : ℕ, (χ n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) := by
  have hf (u : ℝ) (hu : 1 / 2 < u) :
    AnalyticAt ℂ (logDeriv χ.gammaFactor) (((1 / 2 : ℝ) + u : ℝ) : ℂ) := by
    have hs : 0 < ((((1 / 2 : ℝ) + u : ℝ) : ℂ)).re := by
      simp only [Complex.ofReal_re]
      linarith only [hu]
    have h := AnalyticNumberTheory.DirichletLFunction.analyticAt_gammaFactor_of_re_pos χ hs
    exact h.deriv.div h (AnalyticNumberTheory.DirichletLFunction.gammaFactor_ne_zero_of_re_pos χ hs)
  have hg (u : ℝ) (hu : 1 / 2 < u) :
    AnalyticAt ℂ (logDeriv χ.LFunction) (((1 / 2 : ℝ) + u : ℝ) : ℂ) := by
    have ha := (χ.differentiable_LFunction hne).analyticAt (((1 / 2 : ℝ) + u : ℝ) : ℂ)
    have hn : χ.LFunction (((1 / 2 : ℝ) + u : ℝ) : ℂ) ≠ 0 := by
      apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne)
      simp only [Complex.ofReal_re]
      linarith only [hu]
    exact ha.deriv.div ha hn
  have ha : (1 / 2 : ℝ) < 27 / 25 := by norm_num only
  have hd := real_shift_sum_derivs (logDeriv χ.gammaFactor) (logDeriv χ.LFunction) ha hf hg
  have h := refined_six_pole_conductor_formula hq hRH hp hne hinv
  have he := refined_six_real_euler_operator χ hne
  change _ = _ at he
  change _ = _ at h
  unfold refinedPoissonRemainder at h
  rw [hd.1, hd.2] at h
  norm_num only at h
  linarith only [h, he]

end PseudoPrime.PrimeTestBounds.MillerRabin
