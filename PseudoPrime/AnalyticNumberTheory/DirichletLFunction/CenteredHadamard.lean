/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
public import PseudoPrime.AnalyticNumberTheory.General.ShiftedZeroBounds
public import PseudoPrime.AnalyticNumberTheory.General.EntireHadamard
public import PseudoPrime.AnalyticNumberTheory.General.EntireOrder

/-!
# Completed Dirichlet logarithmic derivatives away from the critical line

Individual RH and the inverse-square zero mass give convergent genus-one expansions.
Subtracting the expansions at two points cancels the central constant and produces the
zero-resolvent difference used to study conductor-normalized zero distributions.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character satisfying individual RH and Re s > 1/2,
the divisor-weighted genus term is bounded by an explicit multiple of inverse-square zero mass.
A nonzero divisor identifies a critical-line zero, and analyticity makes its multiplicity
nonnegative. The horizontal separation estimate supplies absolute convergence. -/
theorem norm_completed_genusTerm_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {s : ℂ} (hs : 1 / 2 < s.re) (ρ : ℂ) :
    ‖(MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℂ) *
          (1 / (s - ρ) + 1 / ρ)‖ ≤
      (‖s‖ * (1 + ‖s‖ / (s.re - 1 / 2))) *
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℝ) /
          Complex.normSq ρ) := by
  let D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ
  by_cases hD : D = 0
  · change ‖(D : ℂ) * _‖ ≤ _ * ((D : ℝ) / _)
    simp only [hD, Int.cast_zero, zero_mul, norm_zero, zero_div, mul_zero, le_refl]
  · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
    have hr := completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv hz
    have ha : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ ↦
      (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
    have hn : (0 : ℝ) ≤ D := by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
    change ‖(D : ℂ) * _‖ ≤ _ * ((D : ℝ) / _)
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hn]
    have hb := mul_le_mul_of_nonneg_left (General.norm_genusTerm_le_inverseSquare hr hs) hn
    rw [← Complex.normSq_eq_norm_sq] at hb
    exact hb.trans_eq (by ring)

/-- For modulus at least two, a primitive nonprincipal character with nonprincipal inverse
and individual RH has an absolutely convergent genus-one zero series at every Re s > 1/2.
Compare its norm with the summable inverse-square divisor mass using the pointwise bound.
This extends the endpoint convergence to the half-plane needed for logarithmic derivatives. -/
theorem summable_completed_genus_terms {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℂ) *
          (1 / (s - ρ) + 1 / ρ)) := by
  exact
    Summable.of_norm_bounded
      ((summable_divisor_div_normSq_of_dirichletRH hq hRH hp hne hinv).mul_left
        (‖s‖ * (1 + ‖s‖ / (s.re - 1 / 2))))
      (norm_completed_genusTerm_le hRH hp hne hinv hs)

/-- Under the same primitive-character and individual RH assumptions, the zero-resolvent
difference at two points with real parts above one half is absolutely summable.
Subtract the two convergent genus-one series; the reciprocal-zero terms cancel.
This justifies taking real parts and later integrating the centered zero sum. -/
theorem summable_completed_resolvent_difference {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s t : ℂ} (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℂ) *
          (1 / (s - ρ) - 1 / (t - ρ))) := by
  exact
    ((summable_completed_genus_terms hq hRH hp hne hinv hs).sub
          (summable_completed_genus_terms hq hRH hp hne hinv ht)).congr
      (fun ρ ↦ by ring)

/-- For a primitive nonprincipal character of modulus at least two and nonprincipal inverse,
the raw completed L-function has order at most one, without RH.
Its ball bound supplies a logarithmic exponential envelope; the general real-power comparison
converts this envelope into the order condition used by the entire Hadamard theorem. -/
theorem completed_hasOrderAtMostOne {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    General.HasOrderAtMostOne (DirichletCharacter.completedLFunction χ) := by
  apply
    General.hasOrderAtMostOne_of_exp_norm_mul_log_bound (DirichletCharacter.completedLFunction χ)
      (show 0 < 4 * (q : ℝ) + 3 by nlinarith only [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
  intro s hs
  exact
    (norm_completedLFunction_le_completedLFunctionBallBound
          (Nat.lt_of_lt_of_le (by norm_num only : 1 < 2) hq) hp hne hinv (zero_le_one.trans hs)
          le_rfl).trans
      (completedLFunctionBallBound_le_exp hq hs)

/-- For a nonprincipal character, the completed L-function is entire, so its global divisor
at each point equals the natural analytic multiplicity cast to an integer.
Apply the analytic divisor formula and identify the finite and infinite analytic-order cases.
This reconciles the divisor-weighted Dirichlet series with the entire Hadamard API. -/
theorem completed_divisor_eq_analyticOrderNatAt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) (ρ : ℂ) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ =
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℤ) := by
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha (Set.mem_univ ρ)]
  unfold analyticOrderNatAt
  induction analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ using ENat.recTopCoe <;> rfl

/-- For a primitive nonprincipal character of modulus at least two with nonprincipal inverse,
individual RH gives the centered completed logarithmic derivative at every Re s > 1/2
as its full divisor-weighted genus-one zero sum. RH supplies nonvanishing at zero and s;
order-one growth and absolute convergence discharge the entire Hadamard theorem.
This is the analytic identity behind conductor-normalized zero distribution estimates. -/
theorem completed_centered_logDeriv_eq_genusSum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    logDeriv (DirichletCharacter.completedLFunction χ) s -
        logDeriv (DirichletCharacter.completedLFunction χ) 0 =
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℂ) *
          (1 / (s - ρ) + 1 / ρ) := by
  have hF := DirichletCharacter.differentiable_completedLFunction hne
  have h0 : DirichletCharacter.completedLFunction χ 0 ≠ 0 := fun hz ↦ by
    have hr := completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv hz
    norm_num only [Complex.zero_re] at hr
  have hns : DirichletCharacter.completedLFunction χ s ≠ 0 := fun hz ↦
    hs.ne' (completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv hz)
  have he :
    ∀ ρ : ℂ,
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℂ) =
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ) :=
    fun ρ ↦ by rw [completed_divisor_eq_analyticOrderNatAt hne ρ, Int.cast_natCast]
  obtain ⟨C, hC, hg⟩ :=
    General.exists_global_exponential_bound_of_orderAtMostOne hF.continuous
      (completed_hasOrderAtMostOne hq hp hne hinv) (show (1 : ℝ) < 3 / 2 by norm_num only)
  have hsum :=
    (summable_completed_genus_terms hq hRH hp hne hinv hs).congr
      (fun ρ ↦ congrArg (fun m : ℂ ↦ m * (1 / (s - ρ) + 1 / ρ)) (he ρ))
  rw [General.centered_logDeriv_eq_genusSum hF h0 hC (show (0 : ℝ) ≤ 3 / 2 by norm_num only)
      (show (3 / 2 : ℝ) < 2 by norm_num only) hg hns hsum]
  exact tsum_congr (fun ρ ↦ congrArg (fun m : ℂ ↦ m * (1 / (s - ρ) + 1 / ρ)) (he ρ).symm)

/-- For a primitive nonprincipal character satisfying individual RH, subtracting completed
logarithmic derivatives at two points to the right of the critical line equals the convergent
multiplicity-weighted difference of zero resolvents. Subtract the centered Hadamard identities
and cancel reciprocal-zero terms inside the absolutely convergent sum.
This removes the unknown central constant from zero-distribution calculations. -/
theorem completed_logDeriv_sub_eq_resolventSum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s t : ℂ} (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re) :
    logDeriv (DirichletCharacter.completedLFunction χ) s -
        logDeriv (DirichletCharacter.completedLFunction χ) t =
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℂ) *
          (1 / (s - ρ) - 1 / (t - ρ)) := by
  have he :
    logDeriv (DirichletCharacter.completedLFunction χ) s -
        logDeriv (DirichletCharacter.completedLFunction χ) t =
      (logDeriv (DirichletCharacter.completedLFunction χ) s -
          logDeriv (DirichletCharacter.completedLFunction χ) 0) -
        (logDeriv (DirichletCharacter.completedLFunction χ) t -
          logDeriv (DirichletCharacter.completedLFunction χ) 0) := by
    ring
  rw [he, completed_centered_logDeriv_eq_genusSum hq hRH hp hne hinv hs,
    completed_centered_logDeriv_eq_genusSum hq hRH hp hne hinv ht, ←
    (summable_completed_genus_terms hq hRH hp hne hinv hs).tsum_sub
      (summable_completed_genus_terms hq hRH hp hne hinv ht)]
  exact tsum_congr (fun ρ ↦ by ring)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
