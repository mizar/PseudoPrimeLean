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

/-- For a primitive nonprincipal character and a point to the right of the zero-free line,
the divisor-weighted genus-one series is absolutely summable without RH. Compare its terms
with the already summable series at `1` outside a compact disk; the remaining divisor support
is finite. -/
theorem summable_completed_genus_terms_right {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 2 ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) := by
  let D : ℂ → ℤ := fun ρ ↦ MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  let base : ℂ → ℂ := fun ρ ↦ (D ρ : ℂ) * (1 / ((1 : ℂ) - ρ) + 1 / ρ)
  let target : ℂ → ℂ := fun ρ ↦ (D ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
  have hbase : Summable base := by
    exact (summable_completedLFunctionGenusOneTerm_one hq hp hne hinv).congr (fun ρ ↦ by rfl)
  let R : ℝ := max 2 (2 * ‖s‖)
  have hR2 : 2 ≤ R := le_max_left _ _
  have hRs : 2 * ‖s‖ ≤ R := le_max_right _ _
  let B : Set ℂ := Metric.closedBall (0 : ℂ) R
  have hfinite :
    (Function.support (fun ρ : ℂ ↦ MeromorphicOn.divisor χ.completedLFunction B ρ)).Finite :=
    (MeromorphicOn.divisor χ.completedLFunction B).finiteSupport
      (isCompact_closedBall (x := (0 : ℂ)) (r := R))
  apply Summable.of_norm_bounded_eventually ((hbase.norm).mul_left (3 * ‖s‖))
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset hfinite
  intro ρ hρ
  change ¬‖target ρ‖ ≤ (3 * ‖s‖) * ‖base ρ‖ at hρ
  by_cases hball : ρ ∈ B
  · have hDne : D ρ ≠ 0 := by
      by_contra hD
      apply hρ
      change
        ‖(D ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ ≤ (3 * ‖s‖) * ‖(D ρ : ℂ) * (1 / ((1 : ℂ) - ρ) + 1 / ρ)‖
      rw [hD]
      simp only [Int.cast_zero, zero_mul, norm_zero, mul_zero, le_rfl]
    have heq := divisor_univ_eq_divisor_closedBall hne (by simpa only [B] using hball)
    have hDball : MeromorphicOn.divisor χ.completedLFunction B ρ ≠ 0 := by
      rw [← heq]
      exact hDne
    simpa only [Function.mem_support, ne_eq] using hDball
  · have hdist : ¬‖ρ‖ ≤ R := by simpa only [B, Metric.mem_closedBall, dist_zero_right] using hball
    have hnorm : R ≤ ‖ρ‖ := le_of_not_ge hdist
    have hρ2 : 2 ≤ ‖ρ‖ := hR2.trans hnorm
    have hρs : 2 * ‖s‖ ≤ ‖ρ‖ := hRs.trans hnorm
    have hρ0 : ρ ≠ 0 := by
      intro heq
      rw [heq, norm_zero] at hρ2
      norm_num only at hρ2
    have hρone : (1 : ℂ) - ρ ≠ 0 := by
      intro heq
      have hρeq : ρ = 1 := by linear_combination -heq
      rw [hρeq, norm_one] at hρ2
      norm_num only at hρ2
    have hDne : D ρ ≠ 0 := by
      by_contra hD
      apply hρ
      change
        ‖(D ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ ≤ (3 * ‖s‖) * ‖(D ρ : ℂ) * (1 / ((1 : ℂ) - ρ) + 1 / ρ)‖
      rw [hD]
      simp only [Int.cast_zero, zero_mul, norm_zero, mul_zero, le_rfl]
    have hzero : χ.completedLFunction ρ = 0 :=
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hDne
    have hρlt : ρ.re < 1 := completedLFunction_zero_re_lt_one hne hzero
    have hsρ : s - ρ ≠ 0 := by
      intro heq
      have hsEq : s.re = ρ.re := by
        apply sub_eq_zero.mp
        simpa only [Complex.sub_re, Complex.zero_re] using congrArg Complex.re heq
      linarith only [hs, hρlt, hsEq]
    have hnormrho : ‖s‖ ≤ ‖ρ‖ / 2 := by nlinarith only [hρs]
    have hdist' : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
      have h := norm_sub_norm_le ρ s
      have h' : ‖ρ‖ - ‖s‖ ≤ ‖s - ρ‖ := by simpa only [norm_sub_rev] using h
      nlinarith only [h', hnormrho]
    have honeDist : ‖ρ‖ / 2 ≤ ‖(1 : ℂ) - ρ‖ := by
      have h := norm_sub_norm_le ρ 1
      have h' : ‖ρ‖ - 1 ≤ ‖(1 : ℂ) - ρ‖ := by simpa only [norm_one, norm_sub_rev] using h
      nlinarith only [h', hρ2]
    have honeUpper : ‖(1 : ℂ) - ρ‖ ≤ 3 * ‖ρ‖ / 2 := by
      calc
        _ ≤ 1 + ‖ρ‖ := by simpa only [norm_one] using norm_sub_le (1 : ℂ) ρ
        _ ≤ 3 * ‖ρ‖ / 2 := by nlinarith only [hρ2]
    have hratio : ‖s * ((1 : ℂ) - ρ) / (s - ρ)‖ ≤ 3 * ‖s‖ := by
      rw [norm_div, norm_mul]
      apply (div_le_iff₀ (norm_pos_iff.mpr hsρ)).2
      calc
        ‖s‖ * ‖(1 : ℂ) - ρ‖ ≤ ‖s‖ * (3 * ‖ρ‖ / 2) :=
          mul_le_mul_of_nonneg_left honeUpper (norm_nonneg _)
        _ = (3 * ‖s‖) * (‖ρ‖ / 2) := by ring
        _ ≤ (3 * ‖s‖) * ‖s - ρ‖ := mul_le_mul_of_nonneg_left hdist' (by positivity)
    have heq : target ρ = base ρ * (s * ((1 : ℂ) - ρ) / (s - ρ)) := by
      dsimp only [target, base, D]
      field_simp [hρ0, hρone, hsρ]
      ring_nf
    have hbound : ‖target ρ‖ ≤ (3 * ‖s‖) * ‖base ρ‖ := by
      rw [heq, norm_mul]
      calc
        ‖base ρ‖ * ‖s * ((1 : ℂ) - ρ) / (s - ρ)‖ = ‖s * ((1 : ℂ) - ρ) / (s - ρ)‖ * ‖base ρ‖ := by
          ring
        _ ≤ (3 * ‖s‖) * ‖base ρ‖ := mul_le_mul_of_nonneg_right hratio (norm_nonneg (base ρ))
    exact False.elim (hρ hbound)

/-- For a primitive nonprincipal character, the completed logarithmic derivative has an
unconditional genus-one expansion when `Re s > 1`. The order-one growth bound and the summable
genus series give the identity through the general centered Hadamard theorem. -/
theorem completed_centered_logDeriv_eq_genusSum_right {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) :
    logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction 0 =
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  have hF := DirichletCharacter.differentiable_completedLFunction hne
  have h0 : χ.completedLFunction 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive hp hne
  have hsn : χ.completedLFunction s ≠ 0 := completedLFunction_ne_zero_of_one_le_re hne hs.le
  have hsum :
    Summable
      (fun ρ : ℂ ↦ (analyticOrderNatAt χ.completedLFunction ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) := by
    apply (summable_completed_genus_terms_right hq hp hne hinv hs).congr
    intro ρ
    rw [completed_divisor_eq_analyticOrderNatAt hne ρ, Int.cast_natCast]
  obtain ⟨C, hC, hg⟩ :=
    General.exists_global_exponential_bound_of_orderAtMostOne hF.continuous
      (completed_hasOrderAtMostOne hq hp hne hinv) (show (1 : ℝ) < 3 / 2 by norm_num only)
  have hformula :=
    General.centered_logDeriv_eq_genusSum hF h0 hC (show (0 : ℝ) ≤ 3 / 2 by norm_num only)
      (show (3 / 2 : ℝ) < 2 by norm_num only) hg hsn hsum
  calc
    _ = ∑' ρ : ℂ, (analyticOrderNatAt χ.completedLFunction ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) :=
      hformula
    _ =
        ∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) :=
      tsum_congr (fun ρ ↦ by rw [completed_divisor_eq_analyticOrderNatAt hne ρ, Int.cast_natCast])

/-- For a zero with nonnegative real part, the two reciprocal factors centered at `1` satisfy
`‖1 - ρ‖ ≤ ‖1 + ρ‖`. Expand their squared norms and use `0 ≤ Re ρ`. -/
private theorem norm_one_sub_le_norm_one_add_of_re_nonneg {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    ‖(1 : ℂ) - ρ‖ ≤ ‖(1 : ℂ) + ρ‖ := by
  have hsq : Complex.normSq ((1 : ℂ) + ρ) - Complex.normSq ((1 : ℂ) - ρ) = 4 * ρ.re := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im]
    ring_nf
  have hsq' : ‖(1 : ℂ) - ρ‖ ^ 2 ≤ ‖(1 : ℂ) + ρ‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith only [hsq, hρ]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq'

/-- For a zero in the critical strip, the reciprocal correction caused by moving the
Hadamard center from `0` to `-1` is dominated by the genus-one term at `1`. -/
private theorem norm_reciprocal_correction_le_genus_one {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖1 / (ρ * (1 + ρ))‖ ≤ ‖1 / (ρ * (1 - ρ))‖ := by
  have hden : ‖ρ * (1 - ρ)‖ ≤ ‖ρ * (1 + ρ)‖ := by
    rw [norm_mul, norm_mul]
    exact
      mul_le_mul_of_nonneg_left (norm_one_sub_le_norm_one_add_of_re_nonneg hρ0.le) (norm_nonneg _)
  have hρne : ρ ≠ 0 := by
    intro hz
    rw [hz] at hρ0
    norm_num at hρ0
  have hminus : (1 : ℂ) - ρ ≠ 0 := by
    intro hz
    have hr : ρ.re = 1 := by
      have hh := congrArg Complex.re hz
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hh
      linarith only [hρ1, hh]
    exact (ne_of_lt hρ1) hr
  have hplus : (1 : ℂ) + ρ ≠ 0 := by
    intro hz
    have hr : ρ.re = -1 := by
      have hh := congrArg Complex.re hz
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
      linarith only [hh]
    linarith only [hρ0, hr]
  have hpos1 : 0 < ‖ρ * (1 - ρ)‖ := norm_pos_iff.mpr (mul_ne_zero hρne hminus)
  have hpos2 : 0 < ‖ρ * (1 + ρ)‖ := norm_pos_iff.mpr (mul_ne_zero hρne hplus)
  rw [norm_div, norm_div]
  simp only [norm_one]
  exact one_div_le_one_div_of_le hpos1 hden

/-- For primitive nonprincipal characters, the unconditional Hadamard expansion can be centered
at `-1`, where the completed function is nonzero by the functional equation. Each zero then
contributes the positive kernels `Re(1 / (s - ρ))` and `Re(1 / (1 + ρ))`; this removes the
uncontrolled logarithmic derivative at zero from local zero-count estimates. -/
theorem completed_centered_logDeriv_eq_genusSum_minus_one {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) :
    logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction (-1) =
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
          (1 / (s - ρ) + 1 / (1 + ρ)) := by
  let F : ℂ → ℂ := χ.completedLFunction
  let G : ℂ → ℂ := fun z ↦ F (z - 1)
  have hF := DirichletCharacter.differentiable_completedLFunction hne
  have hFminus : F (-1) ≠ 0 := by
    have hFE := dirichletCompletedLFunction_one_sub_of_isPrimitive hp (2 : ℂ)
    have hpow : (q : ℂ) ^ ((2 : ℂ) - 1 / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast NeZero.ne q))
    have hroot := dirichletCharacter_rootNumber_ne_zero_of_isPrimitive hp
    have hinv2 := dirichletCompletedLFunction_two_ne_zero (χ := χ⁻¹) hinv
    have hEq :
      F (-1) =
        (q : ℂ) ^ ((2 : ℂ) - 1 / 2) * DirichletCharacter.rootNumber χ *
          DirichletCharacter.completedLFunction χ⁻¹ 2 := by
      simpa only [F, show (1 : ℂ) - (2 : ℂ) = (-1 : ℂ) by norm_num only] using hFE
    rw [hEq]
    exact mul_ne_zero (mul_ne_zero hpow hroot) hinv2
  have hG : Differentiable ℂ G := by
    intro z
    exact (hF (z - 1)).comp z (by fun_prop)
  have hG0 : G 0 ≠ 0 := by simpa only [G, F, zero_sub] using hFminus
  obtain ⟨C, hC, hgrowth⟩ :=
    PseudoPrime.AnalyticNumberTheory.General.exists_global_exponential_bound_of_orderAtMostOne
      hF.continuous (completed_hasOrderAtMostOne hq hp hne hinv)
      (show (1 : ℝ) < 3 / 2 by norm_num only)
  let C' : ℝ := C * (2 : ℝ) ^ (3 / 2 : ℝ)
  have hC' : 0 < C' := by
    dsimp only [C']
    positivity
  have hGgrowth : ∀ z : ℂ, ‖G z‖ ≤ Real.exp (C' * (‖z‖ + 1) ^ (3 / 2 : ℝ)) := by
    intro z
    have hnorm : ‖z - 1‖ + 1 ≤ 2 * (‖z‖ + 1) := by
      have h := norm_sub_le z (1 : ℂ)
      have h' : ‖z - 1‖ ≤ ‖z‖ + 1 := by simpa only [norm_one] using h
      nlinarith only [h', norm_nonneg z]
    calc
      ‖G z‖ ≤ Real.exp (C * (‖z - 1‖ + 1) ^ (3 / 2 : ℝ)) := hgrowth (z - 1)
      _ ≤ Real.exp (C * (2 * (‖z‖ + 1)) ^ (3 / 2 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact Real.rpow_le_rpow (by positivity) hnorm (by norm_num only)
      _ = Real.exp (C' * (‖z‖ + 1) ^ (3 / 2 : ℝ)) := by
        congr 1
        dsimp only [C']
        rw [Real.mul_rpow (by norm_num only) (by positivity : 0 ≤ ‖z‖ + 1)]
        ring
  let D : ℂ → ℤ := fun ρ ↦ MeromorphicOn.divisor F Set.univ ρ
  let baseS : ℂ → ℂ := fun ρ ↦ (D ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
  let baseOne : ℂ → ℂ := fun ρ ↦ (D ρ : ℂ) * (1 / ((1 : ℂ) - ρ) + 1 / ρ)
  let correction : ℂ → ℂ := fun ρ ↦ (D ρ : ℂ) * (1 / (1 + ρ) - 1 / ρ)
  let target : ℂ → ℂ := fun ρ ↦ (D ρ : ℂ) * (1 / (s - ρ) + 1 / (1 + ρ))
  have hbaseS : Summable baseS := by
    simpa only [baseS, D, F] using summable_completed_genus_terms_right hq hp hne hinv hs
  have hbaseOne : Summable baseOne := by
    simpa only [baseOne, D, F] using summable_completedLFunctionGenusOneTerm_one hq hp hne hinv
  have hcorrection : Summable correction := by
    apply Summable.of_norm_bounded hbaseOne.norm
    intro ρ
    by_cases hD : D ρ = 0
    · simp only [correction, baseOne, D, hD, Int.cast_zero, zero_mul, norm_zero, le_refl]
    · have hzero : F ρ = 0 := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
      have hre0 := completedLFunction_zero_re_pos hp hinv hzero
      have hre1 := completedLFunction_zero_re_lt_one hne hzero
      have hρ0 : ρ ≠ 0 := by
        intro hz
        rw [hz] at hre0
        norm_num at hre0
      have hρm : (1 : ℂ) - ρ ≠ 0 := by
        intro hz
        have hh := congrArg Complex.re hz
        simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hh
        linarith only [hre1, hh]
      have hρp : (1 : ℂ) + ρ ≠ 0 := by
        intro hz
        have hh := congrArg Complex.re hz
        simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
        linarith only [hre0, hh]
      have hcor : 1 / (1 + ρ) - 1 / ρ = -(1 / (ρ * (1 + ρ))) := by
        field_simp [hρ0, hρp]
        ring
      have hbase : 1 / (1 - ρ) + 1 / ρ = 1 / (ρ * (1 - ρ)) := by
        field_simp [hρ0, hρm]
        ring
      change ‖(D ρ : ℂ) * (1 / (1 + ρ) - 1 / ρ)‖ ≤ ‖(D ρ : ℂ) * (1 / (1 - ρ) + 1 / ρ)‖
      rw [hcor, hbase, norm_mul, norm_mul, norm_neg]
      exact
        mul_le_mul_of_nonneg_left (norm_reciprocal_correction_le_genus_one hre0 hre1)
          (norm_nonneg (D ρ : ℂ))
  have htarget : Summable target := by
    have hadd := hbaseS.add hcorrection
    apply hadd.congr
    intro ρ
    by_cases hD : D ρ = 0
    · simp only [baseS, correction, target, D, hD, Int.cast_zero, zero_mul, add_zero]
    · have hzero : F ρ = 0 := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
      have hre0 := completedLFunction_zero_re_pos hp hinv hzero
      have hre1 := completedLFunction_zero_re_lt_one hne hzero
      have hρ0 : ρ ≠ 0 := by
        intro hz
        rw [hz] at hre0
        norm_num at hre0
      have hρm : (1 : ℂ) - ρ ≠ 0 := by
        intro hz
        have hh := congrArg Complex.re hz
        simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hh
        linarith only [hre1, hh]
      have hρp : (1 : ℂ) + ρ ≠ 0 := by
        intro hz
        have hh := congrArg Complex.re hz
        simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
        linarith only [hre0, hh]
      have hsρ : s - ρ ≠ 0 := by
        intro hz
        have hh := congrArg Complex.re hz
        simp only [Complex.sub_re, Complex.zero_re] at hh
        linarith only [hs, hre1, hh]
      change
        (D ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) + (D ρ : ℂ) * (1 / (1 + ρ) - 1 / ρ) =
          (D ρ : ℂ) * (1 / (s - ρ) + 1 / (1 + ρ))
      rw [← mul_add]
      congr 1
      field_simp [hρ0, hρm, hρp, hsρ]
      ring
  have horder (ρ : ℂ) : analyticOrderNatAt G (ρ + 1) = analyticOrderNatAt F ρ := by
    rw [analyticOrderNatAt, analyticOrderNatAt]
    have hg : AnalyticAt ℂ (fun z : ℂ ↦ z - 1) (ρ + 1) := by fun_prop
    have hg' : deriv (fun z : ℂ ↦ z - 1) (ρ + 1) ≠ 0 := by norm_num
    have hcomp :=
      analyticOrderAt_comp_of_deriv_ne_zero (f := F) (g := fun z : ℂ ↦ z - 1) (z₀ := ρ + 1) hg hg'
    have hcompNat := congrArg ENat.toNat hcomp
    simpa only [G, Function.comp_def, add_sub_cancel_right] using hcompNat
  have hGseries :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt G ρ : ℂ) * (1 / (s + 1 - ρ) + 1 / ρ)) := by
    let e : ℂ ≃ ℂ := Equiv.addRight (1 : ℂ)
    have hcongr :
      (fun ρ : ℂ ↦ (analyticOrderNatAt G (e ρ) : ℂ) * (1 / (s + 1 - e ρ) + 1 / e ρ)) = target := by
      funext ρ
      rw [show e ρ = ρ + 1 by rfl, horder ρ]
      have hD : (D ρ : ℂ) = (analyticOrderNatAt F ρ : ℂ) := by
        dsimp only [D]
        rw [completed_divisor_eq_analyticOrderNatAt hne ρ, Int.cast_natCast]
      rw [← hD]
      change (D ρ : ℂ) * _ = (D ρ : ℂ) * _
      ring
    exact e.summable_iff.mp (htarget.congr (fun ρ ↦ congrFun hcongr.symm ρ))
  have hsG : G (s + 1) ≠ 0 := by
    have hsRe : 1 ≤ s.re := by linarith only [hs]
    have hFs : F s ≠ 0 := completedLFunction_ne_zero_of_one_le_re hne hsRe
    simpa only [G, add_sub_cancel_right] using hFs
  have hformula :=
    PseudoPrime.AnalyticNumberTheory.General.centered_logDeriv_eq_genusSum hG hG0 hC'
      (by norm_num only) (by norm_num only) hGgrowth hsG hGseries
  have hlogG (z : ℂ) : logDeriv G (z + 1) = logDeriv F z := by
    have hg : HasDerivAt (fun w : ℂ ↦ w - 1) 1 (z + 1) := by
      simpa only [id_eq, add_sub_cancel_right] using (hasDerivAt_id (z + 1)).sub_const (1 : ℂ)
    have hcomp :=
      logDeriv_comp (f := F) (g := fun w : ℂ ↦ w - 1) (x := z + 1) hF.differentiableAt
        hg.differentiableAt
    have hcompEq : F ∘ (fun w : ℂ ↦ w - 1) = G := by
      funext w
      rfl
    rw [hcompEq, hg.deriv] at hcomp
    simpa only [add_sub_cancel_right, mul_one] using hcomp
  have hlogGneg : logDeriv G 0 = logDeriv F (-1) := by simpa only [neg_add_cancel] using hlogG (-1)
  have hleft : logDeriv G (s + 1) - logDeriv G 0 = logDeriv F s - logDeriv F (-1) := by
    rw [hlogG s, hlogGneg]
  rw [← hleft, hformula]
  have hReindex :
    (∑' ρ : ℂ, (analyticOrderNatAt G ρ : ℂ) * (1 / (s + 1 - ρ) + 1 / ρ)) =
      ∑' ρ : ℂ, (analyticOrderNatAt G (ρ + 1) : ℂ) * (1 / (s + 1 - (ρ + 1)) + 1 / (ρ + 1)) :=
    ((Equiv.addRight (1 : ℂ)).tsum_eq _).symm
  rw [hReindex]
  apply tsum_congr
  intro ρ
  rw [horder ρ]
  have hD : (D ρ : ℂ) = (analyticOrderNatAt F ρ : ℂ) := by
    dsimp only [D]
    rw [completed_divisor_eq_analyticOrderNatAt hne ρ, Int.cast_natCast]
  rw [← hD]
  change (D ρ : ℂ) * _ = (D ρ : ℂ) * _
  ring

theorem summable_completed_genus_terms_minus_one {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
          (1 / (s - ρ) + 1 / (1 + ρ))) := by
  let F : ℂ → ℂ := χ.completedLFunction
  let D : ℂ → ℤ := fun ρ ↦ MeromorphicOn.divisor F Set.univ ρ
  let baseS : ℂ → ℂ := fun ρ ↦ (D ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
  let baseOne : ℂ → ℂ := fun ρ ↦ (D ρ : ℂ) * (1 / ((1 : ℂ) - ρ) + 1 / ρ)
  let correction : ℂ → ℂ := fun ρ ↦ (D ρ : ℂ) * (1 / (1 + ρ) - 1 / ρ)
  let target : ℂ → ℂ := fun ρ ↦ (D ρ : ℂ) * (1 / (s - ρ) + 1 / (1 + ρ))
  have hbaseS : Summable baseS := by
    simpa only [baseS, D, F] using summable_completed_genus_terms_right hq hp hne hinv hs
  have hbaseOne : Summable baseOne := by
    simpa only [baseOne, D, F] using summable_completedLFunctionGenusOneTerm_one hq hp hne hinv
  have hcorrection : Summable correction := by
    apply Summable.of_norm_bounded hbaseOne.norm
    intro ρ
    by_cases hD : D ρ = 0
    · simp only [correction, baseOne, D, hD, Int.cast_zero, zero_mul, norm_zero, le_refl]
    · have hzero : F ρ = 0 := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
      have hre0 := completedLFunction_zero_re_pos hp hinv hzero
      have hre1 := completedLFunction_zero_re_lt_one hne hzero
      have hρ0 : ρ ≠ 0 := by
        intro hz
        rw [hz] at hre0
        norm_num at hre0
      have hρm : (1 : ℂ) - ρ ≠ 0 := by
        intro hz
        have hh := congrArg Complex.re hz
        simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hh
        linarith only [hre1, hh]
      have hρp : (1 : ℂ) + ρ ≠ 0 := by
        intro hz
        have hh := congrArg Complex.re hz
        simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
        linarith only [hre0, hh]
      have hcor : 1 / (1 + ρ) - 1 / ρ = -(1 / (ρ * (1 + ρ))) := by
        field_simp [hρ0, hρp]
        ring
      have hbase : 1 / (1 - ρ) + 1 / ρ = 1 / (ρ * (1 - ρ)) := by
        field_simp [hρ0, hρm]
        ring
      change ‖(D ρ : ℂ) * (1 / (1 + ρ) - 1 / ρ)‖ ≤ ‖(D ρ : ℂ) * (1 / (1 - ρ) + 1 / ρ)‖
      rw [hcor, hbase, norm_mul, norm_mul, norm_neg]
      exact
        mul_le_mul_of_nonneg_left (norm_reciprocal_correction_le_genus_one hre0 hre1)
          (norm_nonneg (D ρ : ℂ))
  have hadd := hbaseS.add hcorrection
  apply hadd.congr
  intro ρ
  by_cases hD : D ρ = 0
  · change
      (D ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) + (D ρ : ℂ) * (1 / (1 + ρ) - 1 / ρ) =
        (D ρ : ℂ) * (1 / (s - ρ) + 1 / (1 + ρ))
    simp only [hD, Int.cast_zero, zero_mul, add_zero]
  · have hzero : F ρ = 0 := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
    have hre0 := completedLFunction_zero_re_pos hp hinv hzero
    have hre1 := completedLFunction_zero_re_lt_one hne hzero
    have hρ0 : ρ ≠ 0 := by
      intro hz
      rw [hz] at hre0
      norm_num at hre0
    have hρm : (1 : ℂ) - ρ ≠ 0 := by
      intro hz
      have hh := congrArg Complex.re hz
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hh
      linarith only [hre1, hh]
    have hρp : (1 : ℂ) + ρ ≠ 0 := by
      intro hz
      have hh := congrArg Complex.re hz
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
      linarith only [hre0, hh]
    have hsρ : s - ρ ≠ 0 := by
      intro hz
      have hh := congrArg Complex.re hz
      simp only [Complex.sub_re, Complex.zero_re] at hh
      linarith only [hs, hre1, hh]
    change
      (D ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) + (D ρ : ℂ) * (1 / (1 + ρ) - 1 / ρ) =
        (D ρ : ℂ) * (1 / (s - ρ) + 1 / (1 + ρ))
    rw [← mul_add]
    congr 1
    field_simp [hρ0, hρm, hρp, hsρ]
    ring

/-- For two points right of the zero-free line, subtract the unconditional centered expansions
to obtain the divisor-weighted resolvent difference. The `1 / ρ` terms cancel, and both series
are absolutely summable by `summable_completed_genus_terms_right`. -/
theorem completed_logDeriv_sub_eq_resolventSum_right {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s t : ℂ}
    (hs : 1 < s.re) (ht : 1 < t.re) :
    logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction t =
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
          (1 / (s - ρ) - 1 / (t - ρ)) := by
  have he :
    logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction t =
      (logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction 0) -
        (logDeriv χ.completedLFunction t - logDeriv χ.completedLFunction 0) := by
    ring
  rw [he, completed_centered_logDeriv_eq_genusSum_right hq hp hne hinv hs,
    completed_centered_logDeriv_eq_genusSum_right hq hp hne hinv ht, ←
    (summable_completed_genus_terms_right hq hp hne hinv hs).tsum_sub
      (summable_completed_genus_terms_right hq hp hne hinv ht)]
  exact tsum_congr (fun ρ ↦ by ring)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
