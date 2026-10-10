/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedZeroDeriv
public import PseudoPrime.AnalyticNumberTheory.General.InversePowerSeries

/-!
# Higher inverse-power moments of completed Dirichlet zeros

The local Hadamard expansion identifies every nonconstant logarithmic-derivative moment.
Uniform Cauchy estimates make these complex moments small after division by log q.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character of modulus at least two, with nonprincipal
inverse and individual RH, the completed logarithmic derivative at real sigma >= 1 has
derivative of order n+1 equal to (-1)^(n+1) (n+1)! times the inverse-power zero sum of
degree n+2. Differentiate the locally centered Hadamard expansion repeatedly and remove
the constant and translation. This identifies the higher complex zero moments. -/
theorem iteratedDeriv_completed_logDeriv_real_eq_zeroSeries {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : 1 ≤ σ) (n : ℕ) :
    iteratedDeriv (n + 1) (logDeriv χ.completedLFunction) (σ : ℂ) =
      (-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ) *
        (∑' ρ : CompletedZero χ,
          (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) /
            ((σ : ℂ) - (ρ : ℂ)) ^ (n + 2)) := by
  have hz : (0 : ℂ) ∈ Metric.ball 0 (1 / 4) := by
    rw [Metric.mem_ball, dist_self]
    norm_num only
  have h :=
    General.iteratedDeriv_eq_inversePowerSeries_of_hasDerivAt
      (fun ρ : CompletedZero χ => (ρ : ℂ) - (σ : ℂ))
      (fun ρ : CompletedZero χ => analyticOrderNatAt χ.completedLFunction (ρ : ℂ))
      (norm_completedZero_sub_real_ge_half hRH hp hinv hσ)
      (summable_completedZero_shifted_inverseSquare hq hRH hp hne hinv hσ)
      (fun z : ℂ =>
        logDeriv χ.completedLFunction ((σ : ℂ) + z) - logDeriv χ.completedLFunction (σ : ℂ))
      (fun z hz => hasDerivAt_completed_logDeriv_translate hq hRH hp hne hinv hσ hz) n hz
  rw [show
      (fun z : ℂ =>
          logDeriv χ.completedLFunction ((σ : ℂ) + z) - logDeriv χ.completedLFunction (σ : ℂ)) =
        (fun z : ℂ =>
          -logDeriv χ.completedLFunction (σ : ℂ) + logDeriv χ.completedLFunction ((σ : ℂ) + z))
      by
      funext z; ring,
    iteratedDeriv_const_add (Nat.succ_pos n), iteratedDeriv_comp_const_add] at h
  simpa only [add_zero, zero_sub, neg_sub] using h

/-- For each degree n+2, the norm of the complex inverse-power completed-zero sum
centered at real 3/2 has a positive bound uniform over moduli and primitive nonprincipal
characters with nonprincipal inverse satisfying individual RH. Identify the sum with
the corresponding derivative and divide the uniform Cauchy bound by its factorial.
Cancellation in the complex sum is essential; this does not bound the sum of term norms. -/
theorem exists_uniform_norm_completedZero_inversePowerSum_le (n : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ‖∑' ρ : CompletedZero χ,
                      (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) /
                        ((((3 / 2 : ℝ) : ℂ)) - (ρ : ℂ)) ^ (n + 2)‖ ≤
                  C := by
  obtain ⟨A, hA, hb⟩ := exists_uniform_norm_iteratedDeriv_completed_logDeriv_le (n + 1)
  have hp : (0 : ℝ) < ((n + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  refine ⟨A / ((n + 1).factorial : ℝ), div_pos hA hp, ?_⟩
  intro q _ hq χ hRH hprim hne hinv
  have h := hb q χ hne
  rw [iteratedDeriv_completed_logDeriv_real_eq_zeroSeries hq hRH hprim hne hinv
      (show (1 : ℝ) ≤ 3 / 2 by norm_num only)] at h
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast, one_mul] at h
  apply (le_div_iff₀ hp).mpr
  simpa only [mul_comm] using h

/-- For primitive nonprincipal characters of modulus at least two with nonprincipal
inverse and individual RH, every inverse-power completed-zero sum of degree n+2 centered
at real sigma >= 1 is absolutely convergent. Apply the separated-pole series majorant
at zero and rewrite its translated denominator. This permits finite linear combinations
of the moments in zero-distribution approximations. -/
theorem summable_completedZero_inversePower {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : 1 ≤ σ) (n : ℕ) :
    Summable
      (fun ρ : CompletedZero χ =>
        (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) / ((σ : ℂ) - (ρ : ℂ)) ^ (n + 2)) := by
  have hz : (0 : ℂ) ∈ Metric.ball 0 (1 / 4) := by
    rw [Metric.mem_ball, dist_self]
    norm_num only
  simpa only [zero_sub, neg_sub] using
    General.summable_inversePowerSeries (fun ρ : CompletedZero χ => (ρ : ℂ) - (σ : ℂ))
      (fun ρ : CompletedZero χ => analyticOrderNatAt χ.completedLFunction (ρ : ℂ))
      (norm_completedZero_sub_real_ge_half hRH hp hinv hσ)
      (summable_completedZero_shifted_inverseSquare hq hRH hp hne hinv hσ) n hz

/-- For every degree n+2 and epsilon > 0, sufficiently large moduli make the norm of
the complex inverse-power completed-zero sum centered at real 3/2 at most epsilon log q,
uniformly over primitive nonprincipal characters with nonprincipal inverse satisfying
individual RH. Absorb the modulus-independent moment bound into the growing logarithm.
These vanishing normalized moments are used in the approximation of weighted zero measures. -/
theorem exists_uniform_completedZero_inversePowerSum_le_log (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      2 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ‖∑' ρ : CompletedZero χ,
                      (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) /
                        ((((3 / 2 : ℝ) : ℂ)) - (ρ : ℂ)) ^ (n + 2)‖ ≤
                  ε * Real.log q := by
  obtain ⟨C, _, hb⟩ := exists_uniform_norm_completedZero_inversePowerSum_le n
  have hl :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (C / ε)
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.mp hl
  refine ⟨max 2 Q, Nat.le_max_left _ _, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  have hq2 := (Nat.le_max_left 2 Q).trans hq
  have hlarge := (div_le_iff₀ hε).mp (hQ q ((Nat.le_max_right 2 Q).trans hq))
  simp only [Function.comp_apply] at hlarge
  exact (hb q hq2 χ hRH hp hne hinv).trans (by nlinarith only [hlarge])

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
