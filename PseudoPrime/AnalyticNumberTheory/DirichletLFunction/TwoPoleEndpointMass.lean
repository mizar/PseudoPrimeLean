/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TwoPoleZeroBounds

/-! # Two-pole zero sums controlled directly by the endpoint mass -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For primitive nonprincipal individual-RH data at q>=2, any two-pole kernel
with a*b>=1/4 and unit-bounded phases has summable actual zero terms and norm at most
twice the centered completed derivative at one. Use Poisson width exactly one half,
rather than an Euler point to the right of one. This retains the endpoint zero mass. -/
theorem twoPole_zeroSum_le_centered_endpoint {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b : ℝ} (hab : (1 / 4 : ℝ) ≤ a * b) (phase : ℂ → ℂ)
    (hphase : ∀ ρ, ‖phase ρ‖ ≤ 1) :
    Summable (twoPoleCompletedZeroTerm χ a b phase) ∧
      ‖∑' ρ : ℂ, twoPoleCompletedZeroTerm χ a b phase ρ‖ ≤
        2 * ((logDeriv χ.completedLFunction 1).re + Real.log q / 2) := by
  have hs :=
    summable_completed_resolvent_terms hq hRH hp hne hinv (by norm_num only : (0 : ℝ) < 1 / 2)
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hm (ρ : ℂ) : (0 : ℝ) ≤ MeromorphicOn.divisor χ.completedLFunction Set.univ ρ := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  have h :=
    Analysis.twoPole_sum_bound
      (fun ρ : ℂ ↦ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ)) (fun ρ : ℂ ↦ ρ.im)
      phase hm hphase (by norm_num only : (0 : ℝ) < 1 / 2)
      (by
        norm_num only at hab ⊢; exact hab)
      hs
  have he :=
    completed_poissonSum_eq_logDeriv_re hq hRH hp hne hinv (s := 1)
      (by norm_num only [Complex.one_re])
  have ht :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ((1 / 2 : ℝ) / ((1 / 2 : ℝ) ^ 2 + ρ.im ^ 2))) =
      (logDeriv χ.completedLFunction 1).re + Real.log q / 2 := by
    rw [← he]
    apply tsum_congr
    intro ρ
    have hk := completed_resolventTerm_eq_poisson hRH hp hne hinv (1 / 2) ρ
    norm_num only [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num only, Complex.ofReal_one,
      Complex.one_re] at hk ⊢
    have hc : ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) = 1 := by
      norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    rw [hc] at hk
    exact hk
  rw [ht] at h
  norm_num only at h
  exact h

/-- Under global GRH, the preceding endpoint norm bound equals twice the absolute
Hadamard real constant of the primitive character. Use the existing completed
functional-equation endpoint identity. No Euler-series endpoint or positive offset
is needed, making this bound uniform as reciprocal-kernel pole gaps approach zero. -/
theorem twoPole_zeroSum_le_abs_BRe {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {a b : ℝ} (hab : (1 / 4 : ℝ) ≤ a * b) (phase : ℂ → ℂ) (hphase : ∀ ρ, ‖phase ρ‖ ≤ 1) :
    Summable (twoPoleCompletedZeroTerm χ a b phase) ∧
      ‖∑' ρ : ℂ, twoPoleCompletedZeroTerm χ a b phase ρ‖ ≤ 2 * |primitiveBRe χ| := by
  have hz := twoPole_zeroSum_le_centered_endpoint hq (hGRH q χ hp) hp hne hinv hab phase hphase
  have he := completedLFunction_logDeriv_one_re_eq_abs_BRe_sub_half_log hq hGRH hp hne hinv
  have hv : (logDeriv χ.completedLFunction 1).re + Real.log q / 2 = |primitiveBRe χ| := by
    rw [he]
    ring
  rw [hv] at hz
  exact hz

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
