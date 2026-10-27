/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalGenusMass

/-! # Unconditional separated-point genus bounds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character, a nonzero evaluation point separated
from the zeros in a ball has truncated genus norm bounded by its norm times the
square roots of the full inverse-square mass and Jensen count, divided by the
separation margin. Apply weighted Cauchy--Schwarz and unconditional mass summability.
This removes RH from the finite-radius horizontal estimate. -/
theorem norm_completedLFunctionTruncatedGenusSum_le_unconditionally {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 0 < R) {s : ℂ} (hsne : DirichletCharacter.completedLFunction χ s ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ‖ρ‖ < R → δ ≤ ‖s - ρ‖) :
    ‖completedLFunctionTruncatedGenusSum χ R s‖ ≤
      ‖s‖ * Real.sqrt (completedLFunctionInverseSquareMass χ) *
          Real.sqrt
            (Real.log
                (max 1 (completedLFunctionBallBound N (2 * R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) /
        δ := by
  have hN1 : 1 < N := by exact Nat.lt_of_succ_le hN2
  set Dv :=
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) with
    hDv_def
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hAnClosed :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  have hAnBall :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) := fun z _ =>
    hdiff.analyticAt z
  have hAnU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := fun z _ =>
    hdiff.analyticAt z
  have h0ne : DirichletCharacter.completedLFunction χ 0 ≠ 0 :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  have hfin : (Function.support Dv).Finite := hAnClosed.meromorphicOn.divisor_ball_support_finite
  set S := hfin.toFinset with hS_def
  have hDv_nonneg : ∀ ρ, (0 : ℤ) ≤ Dv ρ := fun ρ =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnBall ρ
  have hρ_ball : ∀ ρ, Dv ρ ≠ 0 → ρ ∈ Metric.ball (0 : ℂ) R := by
    intro ρ hne'
    by_contra hnot
    exact hne' (Dv.apply_eq_zero_of_notMem hnot)
  have hDv_zero :
    ∀ ρ, ρ ∈ Metric.ball (0 : ℂ) R → Dv ρ ≠ 0 → DirichletCharacter.completedLFunction χ ρ = 0 := by
    intro ρ hρmem hDvne
    by_contra hFne
    apply hDvne
    have hordzero : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ = 0 :=
      (hAnBall ρ hρmem).analyticOrderAt_eq_zero.mpr hFne
    rw [hDv_def, MeromorphicOn.AnalyticOnNhd.divisor_apply hAnBall hρmem, hordzero]
    simp only [ENat.map_zero, CharP.cast_eq_zero, WithTop.coe_zero, WithTop.untop₀_zero]
  -- Step 1: rewrite the genus sum as a Finset sum over S
  have heqsum :
    completedLFunctionTruncatedGenusSum χ R s =
      ∑ ρ ∈ S, ((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
    unfold completedLFunctionTruncatedGenusSum
    apply finsum_eq_finsetSum_of_support_subset
    intro ρ hρ
    rw [hS_def, Set.Finite.coe_toFinset]
    rw [Function.mem_support] at hρ ⊢
    intro hDv0
    apply hρ
    rw [hDv0]
    simp only [Int.cast_zero, one_div, zero_mul]
  -- Step 2: termwise norm computation
  have hterm_eq :
    ∀ ρ ∈ S, ‖((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ = (Dv ρ : ℝ) * ‖s‖ / (‖ρ‖ * ‖s - ρ‖) := by
    intro ρ hρS
    rw [hS_def, Set.Finite.mem_toFinset, Function.mem_support] at hρS
    have hρmem := hρ_ball ρ hρS
    have hFzero := hDv_zero ρ hρmem hρS
    have hρ0 : ρ ≠ 0 := fun h0 => h0ne (h0 ▸ hFzero)
    have hsρ : s ≠ ρ := fun heq => hsne (heq ▸ hFzero)
    have hid : (1 : ℂ) / (s - ρ) + 1 / ρ = s / (ρ * (s - ρ)) := by
      rw [one_div_add_one_div (sub_ne_zero.mpr hsρ) hρ0]
      congr 1 <;> ring
    rw [hid, norm_mul, norm_div, norm_mul, Complex.norm_intCast,
      abs_of_nonneg (show (0 : ℝ) ≤ (Dv ρ : ℝ) by exact_mod_cast hDv_nonneg ρ)]
    ring
  -- Step 3: triangle inequality
  have hnorm_le :
    ‖completedLFunctionTruncatedGenusSum χ R s‖ ≤ ‖s‖ * ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) := by
    rw [heqsum]
    calc
      ‖∑ ρ ∈ S, ((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ ≤
          ∑ ρ ∈ S, ‖((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ :=
        norm_sum_le S _
      _ = ∑ ρ ∈ S, (Dv ρ : ℝ) * ‖s‖ / (‖ρ‖ * ‖s - ρ‖) := Finset.sum_congr rfl hterm_eq
      _ = ‖s‖ * ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ρ _ => by ring)
  -- Step 4: weighted Cauchy–Schwarz
  have hCS :
    (∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖)) ^ 2 ≤
      (∑ ρ ∈ S, (Dv ρ : ℝ) / ‖ρ‖ ^ 2) * (∑ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2) := by
    have hkey :=
      Finset.sum_mul_sq_le_sq_mul_sq S (fun ρ => Real.sqrt (Dv ρ) / ‖ρ‖)
        (fun ρ => Real.sqrt (Dv ρ) / ‖s - ρ‖)
    have heq1 :
      ∀ ρ ∈ S,
        (Real.sqrt (Dv ρ) / ‖ρ‖) * (Real.sqrt (Dv ρ) / ‖s - ρ‖) = (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) :=
      fun ρ _ => by rw [div_mul_div_comm, Real.mul_self_sqrt (by exact_mod_cast hDv_nonneg ρ)]
    have heq2 : ∀ ρ ∈ S, (Real.sqrt (Dv ρ) / ‖ρ‖) ^ 2 = (Dv ρ : ℝ) / ‖ρ‖ ^ 2 := fun ρ _ => by
      rw [div_pow, Real.sq_sqrt (by exact_mod_cast hDv_nonneg ρ)]
    have heq3 : ∀ ρ ∈ S, (Real.sqrt (Dv ρ) / ‖s - ρ‖) ^ 2 = (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 := fun ρ _ =>
      by rw [div_pow, Real.sq_sqrt (by exact_mod_cast hDv_nonneg ρ)]
    rwa [Finset.sum_congr rfl heq1, Finset.sum_congr rfl heq2, Finset.sum_congr rfl heq3] at hkey
  -- Step 5a: bound the first Cauchy–Schwarz factor via the zero mass
  have hfactorA : ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖ρ‖ ^ 2 ≤ completedLFunctionInverseSquareMass χ :=
    sum_divisor_ball_div_normSq_le_inverseSquareMass hN2 hprimitive hne hinv R S
  -- Step 5b: bound the second Cauchy–Schwarz factor via the good-height margin
  have hfactorB :
    ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 ≤
      (Real.log
            (max 1 (completedLFunctionBallBound N (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2) /
        δ ^ 2 := by
    have hterm_le : ∀ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 ≤ (Dv ρ : ℝ) / δ ^ 2 := by
      intro ρ hρS
      rw [hS_def, Set.Finite.mem_toFinset, Function.mem_support] at hρS
      have hρmem := hρ_ball ρ hρS
      have hFzero := hDv_zero ρ hρmem hρS
      have hρnorm : ‖ρ‖ < R := by
        rw [Metric.mem_ball, dist_zero_right] at hρmem
        exact hρmem
      have hsep' : δ ≤ ‖s - ρ‖ := hsep ρ hFzero hρnorm
      have hδsq : δ ^ 2 ≤ ‖s - ρ‖ ^ 2 := pow_le_pow_left₀ hδ.le hsep' 2
      have hDvρnonneg : (0 : ℝ) ≤ (Dv ρ : ℝ) := by exact_mod_cast hDv_nonneg ρ
      exact div_le_div_of_nonneg_left hDvρnonneg (sq_pos_of_pos hδ) hδsq
    have hSsum :
      (∑ ρ ∈ S, (Dv ρ : ℝ)) ≤
        Real.log
            (max 1 (completedLFunctionBallBound N (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 := by
      have hSsumZ : (∑ ρ ∈ S, Dv ρ : ℤ) = ∑ᶠ ρ, Dv ρ := by
        symm
        apply finsum_eq_finsetSum_of_support_subset
        rw [hS_def, Set.Finite.coe_toFinset]
      have : ((∑ ρ ∈ S, Dv ρ : ℤ) : ℝ) = ∑ ρ ∈ S, (Dv ρ : ℝ) := by
        push_cast
        ring
      rw [← this, hSsumZ]
      exact finsum_divisor_ball_completedLFunction_le hN1 hprimitive hne hinv hR
    calc
      ∑ ρ ∈ S, (Dv ρ : ℝ) / ‖s - ρ‖ ^ 2 ≤ ∑ ρ ∈ S, (Dv ρ : ℝ) / δ ^ 2 := Finset.sum_le_sum hterm_le
      _ = (∑ ρ ∈ S, (Dv ρ : ℝ)) / δ ^ 2 := by rw [Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right hSsum (sq_nonneg δ)
  -- Step 6: combine
  have hH2nonneg :
    (0 : ℝ) ≤
      Real.log
          (max 1 (completedLFunctionBallBound N (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 := by
    have hfinsum_nonneg :
      (0 : ℤ) ≤
        ∑ᶠ u,
          MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R) u := by
      apply finsum_nonneg
      intro u
      exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnClosed u
    exact
      le_trans (by exact_mod_cast hfinsum_nonneg)
        (finsum_divisor_completedLFunction_le hN1 hprimitive hne hinv hR)
  have hCSfull :
    (∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖)) ^ 2 ≤
      completedLFunctionInverseSquareMass χ *
        (Real.log
            (max 1 (completedLFunctionBallBound N (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 /
          δ ^ 2) :=
    hCS.trans
      (mul_le_mul hfactorA hfactorB
        (Finset.sum_nonneg (fun ρ _ => div_nonneg (by exact_mod_cast hDv_nonneg ρ) (sq_nonneg _)))
        (completedLFunctionInverseSquareMass_nonneg hne))
  have hsum_nonneg : 0 ≤ ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) :=
    Finset.sum_nonneg
      (fun ρ _ =>
        div_nonneg (by exact_mod_cast hDv_nonneg ρ) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hrw :
    completedLFunctionInverseSquareMass χ *
        (Real.log
            (max 1 (completedLFunctionBallBound N (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 /
          δ ^ 2) =
      (Real.sqrt (completedLFunctionInverseSquareMass χ) *
            Real.sqrt
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ) ^
        2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (completedLFunctionInverseSquareMass_nonneg hne),
      Real.sq_sqrt hH2nonneg]
    ring
  rw [hrw] at hCSfull
  have hsum_le :
    ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) ≤
      Real.sqrt (completedLFunctionInverseSquareMass χ) *
          Real.sqrt
            (Real.log
                (max 1 (completedLFunctionBallBound N (2 * R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) /
        δ := by
    have hrhs_nonneg :
      (0 : ℝ) ≤
        Real.sqrt (completedLFunctionInverseSquareMass χ) *
            Real.sqrt
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ := by
      exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hδ.le
    nlinarith only [hCSfull, hsum_nonneg, hrhs_nonneg]
  calc
    ‖completedLFunctionTruncatedGenusSum χ R s‖ ≤ ‖s‖ * ∑ ρ ∈ S, (Dv ρ : ℝ) / (‖ρ‖ * ‖s - ρ‖) :=
      hnorm_le
    _ ≤
        ‖s‖ *
          (Real.sqrt (completedLFunctionInverseSquareMass χ) *
              Real.sqrt
                (Real.log
                    (max 1 (completedLFunctionBallBound N (2 * R)) /
                      ‖DirichletCharacter.completedLFunction χ 0‖) /
                  Real.log 2) /
            δ) :=
      mul_le_mul_of_nonneg_left hsum_le (norm_nonneg s)
    _ =
        ‖s‖ * Real.sqrt (completedLFunctionInverseSquareMass χ) *
            Real.sqrt
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ :=
      by ring

/-- For a primitive nonprincipal character, a zero-free sphere and an interior
evaluation point separated from every zero give an unconditional bound for the
centered logarithmic derivative. Add the finite-radius Hadamard remainder to the
mass-based truncated-genus bound. This supplies both signed horizontal contour bounds. -/
theorem norm_centeredLogDeriv_le_of_separation_unconditionally {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 1 ≤ R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) {s : ℂ}
    (hs : ‖s‖ ≤ R / 2) (hsne : DirichletCharacter.completedLFunction χ s ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ‖ρ‖ < R → δ ≤ ‖s - ρ‖) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
          logDeriv (DirichletCharacter.completedLFunction χ) 0‖ ≤
      192 * ‖s‖ *
            ((4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
                Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
              1) /
          R ^ 2 +
        2 * ‖s‖ / R ^ 2 *
          (Real.log
              (max 1 (completedLFunctionBallBound N (2 * R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) +
        ‖s‖ * Real.sqrt (completedLFunctionInverseSquareMass χ) *
            Real.sqrt
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          δ := by
  have hN1 : 1 < N := by exact Nat.lt_of_succ_le hN2
  have hH9e := norm_centeredLogDeriv_sub_truncatedGenus_le hN1 hprimitive hne hinv hR hzf hs hsne
  have hGenus :=
    norm_completedLFunctionTruncatedGenusSum_le_unconditionally hN2 hprimitive hne hinv
      (show (0 : ℝ) < R by exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hR) hsne hδ hsep
  calc
    ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
            logDeriv (DirichletCharacter.completedLFunction χ) 0‖ =
        ‖((logDeriv (DirichletCharacter.completedLFunction χ) s -
                logDeriv (DirichletCharacter.completedLFunction χ) 0) -
              completedLFunctionTruncatedGenusSum χ R s) +
            completedLFunctionTruncatedGenusSum χ R s‖ :=
      by ring_nf
    _ ≤
        ‖(logDeriv (DirichletCharacter.completedLFunction χ) s -
                logDeriv (DirichletCharacter.completedLFunction χ) 0) -
              completedLFunctionTruncatedGenusSum χ R s‖ +
          ‖completedLFunctionTruncatedGenusSum χ R s‖ :=
      norm_add_le _ _
    _ ≤ _ := add_le_add hH9e hGenus

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
