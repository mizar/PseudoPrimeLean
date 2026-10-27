/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TwoPoleResolventBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaSignedPoissonIdentity
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PositiveEulerPrefix

/-! # Actual two-pole zero sums with retained positive Euler prefixes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The completed zero multiplicity times the two-pole height kernel and an
arbitrary complex phase. Inputs include real pole distances and the zero point.
This represents the actual oscillatory zero contribution once individual RH
places contributing zeros on the central line. -/
noncomputable def twoPoleCompletedZeroTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b : ℝ)
    (phase : ℂ → ℂ) (ρ : ℂ) : ℂ :=
  ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) : ℂ) *
    Analysis.twoPoleFunction a b (Complex.I * ρ.im) *
    phase ρ

/-- For primitive nonprincipal individual-RH data, a Poisson width c>1/2 with
c^2<=a*b and unit-bounded phases gives a summable actual zero series and the
stated real-axis logarithmic-derivative bound. Use nonnegative multiplicities,
the general two-pole majorant and the signed Poisson identity. -/
theorem twoPole_zeroSum_le_real_axis {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {a b c : ℝ} (hc : (1 / 2 : ℝ) < c) (hab : c ^ 2 ≤ a * b) (phase : ℂ → ℂ)
    (hphase : ∀ ρ, ‖phase ρ‖ ≤ 1) :
    Summable (twoPoleCompletedZeroTerm χ a b phase) ∧
      ‖∑' ρ : ℂ, twoPoleCompletedZeroTerm χ a b phase ρ‖ ≤
        (1 / c) *
          (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
            (logDeriv χ.LFunction (((1 / 2 : ℝ) + c) : ℂ)).re) := by
  have hc0 : 0 < c := lt_trans (by norm_num only) hc
  have hs := summable_completed_resolvent_terms hq hRH hp hne hinv hc0
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hm (ρ : ℂ) : (0 : ℝ) ≤ MeromorphicOn.divisor χ.completedLFunction Set.univ ρ := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  have h :=
    Analysis.twoPole_sum_bound
      (fun ρ : ℂ ↦ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ)) (fun ρ : ℂ ↦ ρ.im)
      phase hm hphase hc0 hab hs
  have he :=
    completed_poissonSum_eq_signed_ordinary hq hRH hp hne hinv
      (show (1 : ℝ) < 1 / 2 + c by linarith only [hc])
  simp only [add_sub_cancel_left, Complex.ofReal_add] at he
  have ht :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (c / (c ^ 2 + ρ.im ^ 2))) =
      Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
        (logDeriv χ.LFunction (((1 / 2 : ℝ) + c) : ℂ)).re := by
    rw [← he]
    apply tsum_congr
    intro ρ
    simpa only [Complex.ofReal_add] using completed_resolventTerm_eq_poisson hRH hp hne hinv c ρ
  rw [ht] at h
  unfold twoPoleCompletedZeroTerm
  exact h

/-- Under the same analytic and majorant assumptions, subtract any finite
nonnegative Euler prefix from the real-axis budget. Apply the signed ordinary
logarithmic-derivative bound. This retains actual prime-power savings in the
adjustable rational-kernel zero estimate. -/
theorem twoPole_zeroSum_le_positive_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b c : ℝ} (hc : (1 / 2 : ℝ) < c) (hab : c ^ 2 ≤ a * b)
    (phase : ℂ → ℂ) (hphase : ∀ ρ, ‖phase ρ‖ ≤ 1) (B : Finset ℕ) :
    ‖∑' ρ : ℂ, twoPoleCompletedZeroTerm χ a b phase ρ‖ ≤
      (1 / c) *
        (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
            (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
          ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) := by
  have h := (twoPole_zeroSum_le_real_axis hq hRH hp hne hinv hc hab phase hphase).2
  have hE :=
    re_logDeriv_le_principal_sub_positive_prefix χ (show (1 : ℝ) < 1 / 2 + c by linarith only [hc])
      B
  simp only [Complex.ofReal_add] at hE
  have hm :=
    mul_le_mul_of_nonneg_left
      (add_le_add_left hE (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re))
      (one_div_nonneg.mpr (show (0 : ℝ) ≤ c by linarith only [hc]))
  exact h.trans (by linarith only [hm])

/-- At any positive real base, a purely imaginary Mellin power has norm one.
Evaluate the complex-power norm at real part zero.
This verifies the actual oscillatory phases without an extra hypothesis. -/
theorem norm_real_mellin_phase {x t : ℝ} (hx : 0 < x) : ‖(x : ℂ) ^ (Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_self, Real.rpow_zero]

/-- Under primitive individual RH, positive scale and the two-pole majorant,
the actual Mellin-oscillating zero series converges and satisfies the positive
Euler-prefix budget. Insert the norm-one phase into both preceding theorems.
This connects the adjustable poles to an actual zero sum, not just a formal kernel. -/
theorem twoPole_oscillating_zeroSum_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b c x : ℝ} (hc : (1 / 2 : ℝ) < c) (hab : c ^ 2 ≤ a * b)
    (hx : 0 < x) (B : Finset ℕ) :
    Summable (twoPoleCompletedZeroTerm χ a b (fun ρ ↦ (x : ℂ) ^ (Complex.I * ρ.im))) ∧
      ‖∑' ρ : ℂ, twoPoleCompletedZeroTerm χ a b (fun z ↦ (x : ℂ) ^ (Complex.I * z.im)) ρ‖ ≤
        (1 / c) *
          (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
              (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
            ∑ n ∈ B,
              (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) := by
  have hphase (ρ : ℂ) : ‖(x : ℂ) ^ (Complex.I * ρ.im)‖ ≤ 1 := (norm_real_mellin_phase hx).le
  exact
    ⟨(twoPole_zeroSum_le_real_axis hq hRH hp hne hinv hc hab _ hphase).1,
      twoPole_zeroSum_le_positive_prefix hq hRH hp hne hinv hc hab _ hphase B⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
