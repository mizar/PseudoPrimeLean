/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerIdentity

/-! # Real-variable differential form of the refined Euler identity -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a complex analytic function along the shifted real half-line, the
second derivative of its real part is the real part of its second complex
derivative. Differentiate pointwise on a neighborhood and transfer the
first derivative by eventual equality. This connects the zero-mass operator
to the complex Euler derivatives. -/
theorem real_shift_derivs (f : ℂ → ℂ) {a : ℝ} (ha : 1 / 2 < a)
    (hf : ∀ u : ℝ, 1 / 2 < u → AnalyticAt ℂ f (((1 / 2 : ℝ) + u : ℝ) : ℂ)) :
    deriv (deriv (fun u : ℝ ↦ (f (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re)) a =
      (deriv (deriv f) (((1 / 2 : ℝ) + a : ℝ) : ℂ)).re := by
  have hd (u : ℝ) (hu : 1 / 2 < u) :
    HasDerivAt (fun v : ℝ ↦ (f (((1 / 2 : ℝ) + v : ℝ) : ℂ)).re)
      (deriv f (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re u := by
    have h := (hf u hu).differentiableAt.hasDerivAt.real_of_complex
    have h' := h.comp u ((hasDerivAt_id u).const_add (1 / 2 : ℝ))
    simpa only [mul_one, Function.comp_def] using h'
  have he :
    deriv (fun u : ℝ ↦ (f (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re) =ᶠ[nhds a] fun u : ℝ ↦
      (deriv f (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re := by
    filter_upwards [Ioi_mem_nhds ha] with u hu
    exact (hd u hu).deriv
  rw [he.deriv_eq]
  have h := (hf a ha).deriv.differentiableAt.hasDerivAt.real_of_complex
  have h' := h.comp a ((hasDerivAt_id a).const_add (1 / 2 : ℝ))
  simpa only [mul_one, Function.comp_def] using h'.deriv

/-- For a nonprincipal character, the real-variable differential operator
on the ordinary logarithmic L-derivative equals the signed refined Euler
series. Analyticity on the half-line converts real derivatives to complex
derivatives, to which the exact Euler identity applies. -/
theorem refined_six_real_euler_operator {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) :
    let f : ℝ → ℝ := fun u ↦ (logDeriv χ.LFunction (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
    3 * f (27 / 25) - (81 / 25 : ℝ) * deriv f (27 / 25) +
        (729 / 625 : ℝ) * deriv (deriv f) (27 / 25) =
      -8 * ∑' n : ℕ, (χ n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) := by
  have hf (u : ℝ) (hu : 1 / 2 < u) :
    AnalyticAt ℂ (logDeriv χ.LFunction) (((1 / 2 : ℝ) + u : ℝ) : ℂ) := by
    have ha := (χ.differentiable_LFunction hne).analyticAt (((1 / 2 : ℝ) + u : ℝ) : ℂ)
    have hn : χ.LFunction (((1 / 2 : ℝ) + u : ℝ) : ℂ) ≠ 0 := by
      apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne)
      simp only [Complex.ofReal_re]
      linarith only [hu]
    exact ha.deriv.div ha hn
  have ha : (1 / 2 : ℝ) < 27 / 25 := by norm_num only
  have hc : (((1 / 2 : ℝ) + 27 / 25 : ℝ) : ℂ) = (79 / 50 : ℂ) := by
    norm_num only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hd := (hf (27 / 25) ha).differentiableAt.hasDerivAt.real_of_complex
  have hd' := hd.comp (27 / 25 : ℝ) ((hasDerivAt_id (27 / 25 : ℝ)).const_add (1 / 2 : ℝ))
  have hd1 :
    deriv (fun u : ℝ ↦ (logDeriv χ.LFunction (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re) (27 / 25) =
      (deriv (logDeriv χ.LFunction) (79 / 50 : ℂ)).re := by
    simpa only [mul_one, Function.comp_def, hc] using hd'.deriv
  have hd2 := real_shift_derivs (logDeriv χ.LFunction) ha hf
  rw [hc] at hd2
  change 3 * (logDeriv χ.LFunction (((1 / 2 : ℝ) + 27 / 25 : ℝ) : ℂ)).re - _ + _ = _
  rw [hc, hd1, hd2]
  exact refined_six_euler_operator_eq χ

end PseudoPrime.PrimeTestBounds.MillerRabin
