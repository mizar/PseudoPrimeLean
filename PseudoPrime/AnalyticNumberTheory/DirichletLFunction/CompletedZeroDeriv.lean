/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CenteredHadamard
public import PseudoPrime.AnalyticNumberTheory.General.CenteredResolventDerivative
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedDerivativeBounds

/-!
# Differentiation of completed Dirichlet zero resolvents

Individual RH separates completed zeros from real points at least one.
The inverse-square mass gives local termwise differentiation of the Hadamard expansion.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The subtype of complex zeros of a character's completed L-function.
Its elements carry the zero equality used by individual RH to locate their real part.
This is the index type for shifted inverse-power sums and logarithmic-derivative identities. -/
abbrev CompletedZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :=
  { ρ : ℂ // χ.completedLFunction ρ = 0 }

/-- Under individual RH for a primitive character with nonprincipal inverse, every completed
zero has distance at least one half from any real sigma >= 1.
Compare the difference norm with its real part using Re rho = 1/2.
This separation supplies the common neighborhood for differentiating zero resolvents. -/
theorem norm_completedZero_sub_real_ge_half {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {σ : ℝ}
    (hσ : 1 ≤ σ) (ρ : CompletedZero χ) : (1 / 2 : ℝ) ≤ ‖(ρ : ℂ) - (σ : ℂ)‖ := by
  have h := Complex.re_le_norm ((σ : ℂ) - (ρ : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re,
    completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv ρ.property, norm_sub_rev] at h
  linarith only [h, hσ]

/-- For a primitive nonprincipal character of modulus at least two with nonprincipal inverse
and individual RH, its natural zero multiplicities divided by squared distance to any real
sigma >= 1 form a summable series. Restrict the inverse-square divisor mass to actual zeros;
the critical-line denominator comparison can only decrease each term after shifting.
This is the local uniform majorant for termwise differentiation. -/
theorem summable_completedZero_shifted_inverseSquare {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : 1 ≤ σ) :
    Summable
      (fun ρ : CompletedZero χ ↦
        (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - (σ : ℂ)‖ ^ 2) := by
  have hb :=
    (summable_divisor_div_normSq_of_dirichletRH hq hRH hp hne hinv).subtype
      {ρ : ℂ | χ.completedLFunction ρ = 0}
  have he :
    ∀ ρ : CompletedZero χ,
      (MeromorphicOn.divisor χ.completedLFunction Set.univ (ρ : ℂ) : ℝ) / Complex.normSq (ρ : ℂ) =
        (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2 :=
    fun ρ ↦ by
    rw [completed_divisor_eq_analyticOrderNatAt hne, Int.cast_natCast, Complex.normSq_eq_norm_sq]
  have hm := hb.congr he
  apply
    Summable.of_nonneg_of_le (fun ρ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (fun ρ ↦ ?_) hm
  have hr := completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv ρ.property
  have hpos : 0 < ‖ρ.1‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (General.zero_ne_of_re_half hr))
  exact
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos
      (General.norm_sq_le_norm_sq_sub_real_of_half hr hσ)

/-- For a primitive nonprincipal character satisfying individual RH, the difference of
completed logarithmic derivatives at two points to the right of the critical line equals
the multiplicity-weighted reciprocal difference sum over actual completed zeros.
Convert the divisor to natural analytic order and discard nonzeros, whose order is zero.
This aligns the Hadamard expansion with shifted pole-series differentiation. -/
theorem completed_logDeriv_sub_eq_zeroSubtypeSeries {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s t : ℂ} (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re) :
    logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction t =
      ∑' ρ : CompletedZero χ,
        (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) *
          (1 / (s - (ρ : ℂ)) - 1 / (t - (ρ : ℂ))) := by
  rw [completed_logDeriv_sub_eq_resolventSum hq hRH hp hne hinv hs ht]
  have he :
    ∀ ρ : ℂ,
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) =
        (analyticOrderNatAt χ.completedLFunction ρ : ℂ) :=
    fun ρ ↦ by rw [completed_divisor_eq_analyticOrderNatAt hne, Int.cast_natCast]
  rw [tsum_congr (fun ρ ↦ congrArg (fun m : ℂ ↦ m * (1 / (s - ρ) - 1 / (t - ρ))) (he ρ))]
  symm
  apply
    tsum_subtype_eq_of_support_subset (s := {ρ : ℂ | χ.completedLFunction ρ = 0}) (f := fun ρ : ℂ ↦
      (analyticOrderNatAt χ.completedLFunction ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ)))
  intro ρ hρ
  by_contra hn
  have ho : analyticOrderNatAt χ.completedLFunction ρ = 0 := by
    rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hn), ENat.toNat_zero]
  exact hρ (by simp only [ho, Nat.cast_zero, zero_mul])

/-- Under individual RH for a primitive nonprincipal character, the translated centered
completed logarithmic derivative is differentiable at every point of the radius-one-quarter
ball around zero, for real sigma >= 1. Its derivative is the translated inverse-square
zero series. Apply the local pole-series derivative and the Hadamard identity throughout
the same ball. This neighborhood formula supports higher zero-moment differentiation. -/
theorem hasDerivAt_completed_logDeriv_translate {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : 1 ≤ σ) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Metric.ball 0 (1 / 4)) :
    HasDerivAt
      (fun z : ℂ ↦
        logDeriv χ.completedLFunction ((σ : ℂ) + z) - logDeriv χ.completedLFunction (σ : ℂ))
      (∑' ρ : CompletedZero χ,
        -(analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) / (z₀ - ((ρ : ℂ) - (σ : ℂ))) ^ 2)
      z₀ := by
  have hh :=
    General.hasDerivAt_centeredResolventSum_of_mem_ball
      (fun ρ : CompletedZero χ ↦ (ρ : ℂ) - (σ : ℂ))
      (fun ρ : CompletedZero χ ↦ analyticOrderNatAt χ.completedLFunction (ρ : ℂ))
      (norm_completedZero_sub_real_ge_half hRH hp hinv hσ)
      (summable_completedZero_shifted_inverseSquare hq hRH hp hne hinv hσ) hz₀
  have he :
    (fun z : ℂ ↦
        logDeriv χ.completedLFunction ((σ : ℂ) + z) -
          logDeriv χ.completedLFunction (σ : ℂ)) =ᶠ[nhds z₀]
      (fun z : ℂ ↦
        ∑' ρ : CompletedZero χ,
          (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) *
            (1 / (z - ((ρ : ℂ) - (σ : ℂ))) + 1 / ((ρ : ℂ) - (σ : ℂ)))) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz₀] with z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hr := Complex.re_le_norm (-z)
    rw [Complex.neg_re, norm_neg] at hr
    have hs : 1 / 2 < ((σ : ℂ) + z).re := by
      rw [Complex.add_re, Complex.ofReal_re]
      linarith only [hr, hz, hσ]
    have ht : 1 / 2 < (σ : ℂ).re := by
      rw [Complex.ofReal_re]
      linarith only [hσ]
    rw [completed_logDeriv_sub_eq_zeroSubtypeSeries hq hRH hp hne hinv hs ht]
    apply tsum_congr
    intro ρ
    rw [show (σ : ℂ) + z - (ρ : ℂ) = z - ((ρ : ℂ) - (σ : ℂ)) by ring,
      show (σ : ℂ) - (ρ : ℂ) = -((ρ : ℂ) - (σ : ℂ)) by ring]
    simp only [one_div, inv_neg, sub_neg_eq_add]
  exact hh.congr_of_eventuallyEq he

/-- For a primitive nonprincipal character of modulus at least two with nonprincipal inverse
and individual RH, the derivative of the completed logarithmic derivative at real sigma >= 1
equals the negative inverse-square completed-zero series. The shifted mass and pole separation
justify differentiating the locally centered expansion; analytic nonvanishing identifies
the derivative by uniqueness. This provides the first nonconstant zero-distribution moment. -/
theorem deriv_completed_logDeriv_real_eq_zeroSeries {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : 1 ≤ σ) :
    deriv (logDeriv χ.completedLFunction) (σ : ℂ) =
      ∑' ρ : CompletedZero χ,
        -(analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) / ((ρ : ℂ) - (σ : ℂ)) ^ 2 := by
  have hz : (0 : ℂ) ∈ Metric.ball 0 (1 / 4) := by
    rw [Metric.mem_ball, dist_self]
    norm_num only
  have hd := hasDerivAt_completed_logDeriv_translate hq hRH hp hne hinv hσ hz
  simp only [zero_sub, neg_sq] at hd
  have hF := (DirichletCharacter.differentiable_completedLFunction hne).analyticAt (σ : ℂ)
  have hn : χ.completedLFunction (σ : ℂ) ≠ 0 := fun hz ↦ by
    have hr := completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv hz
    rw [Complex.ofReal_re] at hr
    linarith only [hr, hσ]
  have hDa : AnalyticAt ℂ (logDeriv χ.completedLFunction) (σ : ℂ) := hF.deriv.div hF hn
  have hD := hDa.differentiableAt.hasDerivAt
  have hD' :
    HasDerivAt (logDeriv χ.completedLFunction) (deriv (logDeriv χ.completedLFunction) (σ : ℂ))
      ((fun z : ℂ ↦ (σ : ℂ) + z) 0) := by
    simpa only [add_zero] using hD
  have ht :=
    (hD'.comp 0 ((hasDerivAt_id (0 : ℂ)).const_add (σ : ℂ))).sub_const
      (logDeriv χ.completedLFunction (σ : ℂ))
  simp only [Function.comp_def, mul_one] at ht
  exact ht.unique hd

/-- For primitive nonprincipal characters of modulus at least two with nonprincipal inverse
and individual RH, the complex inverse-square completed-zero sum centered at real 3/2 has
a positive bound independent of the modulus and character. Identify it with the derivative
of the completed logarithmic derivative and apply the uniform Cauchy estimate of order one.
The bound is for the norm of the complex sum, not the sum of term norms; cancellation is
essential for the conductor-normalized nonconstant zero moment. -/
theorem exists_uniform_norm_completedZero_inverseSquareSum_le :
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
                      -(analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) /
                        ((ρ : ℂ) - (((3 / 2 : ℝ) : ℂ))) ^ 2‖ ≤
                  C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_norm_iteratedDeriv_completed_logDeriv_le 1
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  have h := hb q χ hne
  rw [iteratedDeriv_one,
    deriv_completed_logDeriv_real_eq_zeroSeries hq hRH hp hne hinv
      (show (1 : ℝ) ≤ 3 / 2 by norm_num only)] at h
  exact h

/-- For every epsilon > 0, sufficiently large moduli make the norm of the complex
inverse-square completed-zero sum at real 3/2 at most epsilon log q, uniformly over
primitive nonprincipal characters satisfying individual RH. Absorb the modulus-independent
bound into the growing logarithm. This is the first vanishing nonconstant moment in the
conductor-normalized zero distribution; it does not bound the absolute zero mass. -/
theorem exists_uniform_completedZero_inverseSquareSum_le_log {ε : ℝ} (hε : 0 < ε) :
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
                      -(analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℂ) /
                        ((ρ : ℂ) - (((3 / 2 : ℝ) : ℂ))) ^ 2‖ ≤
                  ε * Real.log q := by
  obtain ⟨C, _, hb⟩ := exists_uniform_norm_completedZero_inverseSquareSum_le
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
