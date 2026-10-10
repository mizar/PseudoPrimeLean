/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedZeroMoments
public import PseudoPrime.Analysis.CayleyMoments

/-!
# Poisson-weighted Cayley moments of completed Dirichlet zeros

Positive Cayley moments are finite combinations of higher inverse-power zero sums.
Their conductor-normalized values vanish uniformly for primitive characters under individual RH.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a character, a natural degree, and an actual completed zero, let z = 3/2-rho.
The term is its natural multiplicity times (z - 2) / z to that degree, divided by normSq z.
Under individual RH the quotient lies on the unit circle and the denominator is the
Poisson weight denominator. These terms define the weighted zero-distribution moments. -/
noncomputable def completedZeroCayleyTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ)
    (ρ : CompletedZero χ) : ℂ :=
  let z := (((3 / 2 : ℝ) : ℂ)) - (ρ : ℂ)
  (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) / (Complex.normSq z : ℂ) * ((z - 2) / z) ^ n

/-- For a primitive character with nonprincipal inverse and individual RH, each weighted
Cayley zero term of degree n+1 is the binomial combination of inverse powers of degrees
two through n+2. The shifted zero has real part one, so apply the weighted Cayley identity.
This permits the already bounded complex inverse-power moments to control circle moments. -/
theorem completedZeroCayleyTerm_eq_inversePowerSum {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) (n : ℕ)
    (ρ : CompletedZero χ) :
    completedZeroCayleyTerm χ (n + 1) ρ =
      ∑ j ∈ Finset.range (n + 1),
        -(n.choose j : ℂ) * (-2 : ℂ) ^ j *
          ((analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) /
            ((((3 / 2 : ℝ) : ℂ)) - (ρ : ℂ)) ^ (j + 2)) := by
  apply PseudoPrime.Analysis.cayley_weighted_power_expansion
  rw [Complex.sub_re, Complex.ofReal_re,
    completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv ρ.property]
  norm_num only

/-- For primitive nonprincipal characters of modulus at least two, with nonprincipal
inverse and individual RH, the Cayley zero sum of degree n+1 equals a finite binomial
combination of inverse-power zero sums. Each inverse-power series is absolutely convergent;
interchange the finite sum with the zero series and factor out its coefficients.
This transfers the uniform moment estimates without taking absolute values termwise. -/
theorem completedZeroCayleySum_eq_inversePowerSums {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (n : ℕ) :
    (∑' ρ : CompletedZero χ, completedZeroCayleyTerm χ (n + 1) ρ) =
      ∑ j ∈ Finset.range (n + 1),
        -(n.choose j : ℂ) * (-2 : ℂ) ^ j *
          (∑' ρ : CompletedZero χ,
            (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) /
              ((((3 / 2 : ℝ) : ℂ)) - (ρ : ℂ)) ^ (j + 2)) := by
  rw [tsum_congr (completedZeroCayleyTerm_eq_inversePowerSum hRH hp hinv n)]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    exact tsum_mul_left
  · intro j hj
    exact
      (summable_completedZero_inversePower hq hRH hp hne hinv
            (show (1 : ℝ) ≤ 3 / 2 by norm_num only) j).mul_left
        _

/-- Under individual RH for a primitive nonprincipal character of modulus at least two
with nonprincipal inverse, every positive-degree Cayley zero series is absolutely convergent.
Express its terms as a finite sum of constant multiples of summable inverse-power terms.
This supplies the convergence needed for circle-polynomial approximation. -/
theorem summable_completedZeroCayleyTerm {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (n : ℕ) : Summable (completedZeroCayleyTerm χ (n + 1)) := by
  have h :=
    summable_sum (s := Finset.range (n + 1))
      (fun j _ =>
        (summable_completedZero_inversePower hq hRH hp hne hinv
              (show (1 : ℝ) ≤ 3 / 2 by norm_num only) j).mul_left
          (-(n.choose j : ℂ) * (-2 : ℂ) ^ j))
  exact h.congr (fun ρ => (completedZeroCayleyTerm_eq_inversePowerSum hRH hp hinv n ρ).symm)

/-- For each positive degree n+1, the norm of the Poisson-weighted Cayley zero sum has
a positive bound independent of the modulus and primitive nonprincipal character, assuming
individual RH and a nonprincipal inverse. Apply the finite moment identity and the uniform
bounds for its inverse-power sums. These are bounds on the complex sum, preserving cancellation. -/
theorem exists_uniform_norm_completedZeroCayleySum_le (n : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 → ‖∑' ρ : CompletedZero χ, completedZeroCayleyTerm χ (n + 1) ρ‖ ≤ C := by
  choose B hB hb using exists_uniform_norm_completedZero_inversePowerSum_le
  let C : ℝ := ∑ j ∈ Finset.range (n + 1), ‖-(n.choose j : ℂ) * (-2 : ℂ) ^ j‖ * B j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hB j).le)
  refine ⟨C + 1, by linarith only [hC], ?_⟩
  intro q _ hq χ hRH hp hne hinv
  rw [completedZeroCayleySum_eq_inversePowerSums hq hRH hp hne hinv]
  apply (norm_sum_le _ _).trans
  apply le_trans (Finset.sum_le_sum (fun j hj => ?_)) (show C ≤ C + 1 by linarith only)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb j q hq χ hRH hp hne hinv) (norm_nonneg _)

/-- For each positive degree n+1 and epsilon > 0, sufficiently large moduli make the
norm of the weighted Cayley zero sum at most epsilon log q, uniformly over primitive
nonprincipal characters satisfying individual RH with nonprincipal inverse.
Absorb the fixed-degree bound into the growing logarithm. This proves vanishing positive
moments for the conductor-normalized weighted zero distribution. -/
theorem exists_uniform_completedZeroCayleySum_le_log (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      2 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ‖∑' ρ : CompletedZero χ, completedZeroCayleyTerm χ (n + 1) ρ‖ ≤ ε * Real.log q := by
  obtain ⟨C, _, hb⟩ := exists_uniform_norm_completedZeroCayleySum_le n
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
