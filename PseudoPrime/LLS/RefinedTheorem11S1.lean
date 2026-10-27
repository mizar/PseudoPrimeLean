/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RefinedLogWeightedBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogTrivialSupport
public import PseudoPrime.LLS.RiemannWeightedBounds
public import PseudoPrime.Analysis.LogarithmicRatios
public import PseudoPrime.Analysis.RefinedPart1Separation
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds

/-! # Improved Part 1 radius and logarithmic upper bound -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The refined reciprocal saving A*(q), with constant 32873/20800.
It is nonnegative and supplies the saving in the improved Part 1 comparison. -/
noncomputable def refinedAuxiliaryTerm (q : ℕ) : ℝ :=
  max 0
    (2 * Real.log (Real.log q) - 32873 / 20800 -
      AnalyticNumberTheory.Arithmetic.primeFactorLogSum q)

/-- The refined nonnegative correction B*(q), with additive constant two.
Its prime-factor term controls the original-level loss in Part 1. -/
noncomputable def refinedCorrectionTerm (q : ℕ) : ℝ :=
  max 0
    (2 * Real.log (Real.log q) + 2 +
        2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
      2 * refinedAuxiliaryTerm q)

/-- The root log(q)+B*(q) of the improved Part 1 search radius.
Its square is the actual cutoff in the no-witness comparison. -/
noncomputable def refinedRadiusRoot (q : ℕ) : ℝ :=
  Real.log q + refinedCorrectionTerm q

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For q≥3000, GRH and prime triviality up to the improved radius give the
logarithmic upper bound with reciprocal saving A*(q) and zero-mass constant 9/50.
The root is at least log(q), so monotonicity of log transfers the cutoff saving to A*(q).
This connects the arbitrary-cutoff analytic estimate to the refined search radius. -/
theorem characterLogWeightedSum_re_le_refinedRadius {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hq : 3000 ≤ q) (hN : 2 ≤ χ.conductor) (hne : χ.primitiveCharacter ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (refinedRadiusRoot q) ^ 2 → χ p = 1) :
    (characterLogWeightedSum ((refinedRadiusRoot q) ^ 2) χ).re ≤
      (2 * refinedRadiusRoot q + 2 + Real.log ((refinedRadiusRoot q) ^ 2)) *
            (Real.log q / 2 + 9 / 50 - refinedAuxiliaryTerm q) +
          (1 / 2 : ℝ) * (Real.log q - Real.log Real.pi) * Real.log ((refinedRadiusRoot q) ^ 2) -
        11 / 4 := by
  have hL := Analysis.eight_lt_log_level hq
  have hroot : Real.log q ≤ refinedRadiusRoot q := le_add_of_nonneg_right (le_max_left _ _)
  have hy : 0 < refinedRadiusRoot q :=
    lt_of_lt_of_le (lt_trans (by norm_num only : (0 : ℝ) < 8) hL) hroot
  have hx : (64 : ℝ) ≤ (refinedRadiusRoot q) ^ 2 := by nlinarith only [hL, hroot]
  have hs : Real.sqrt ((refinedRadiusRoot q) ^ 2) = refinedRadiusRoot q := Real.sqrt_sq hy.le
  have h :=
    characterLogWeightedSum_re_le_refined_fullLevel χ hN hne hGRH hx hL
      (by
        rw [hs]; exact hroot)
      htrivial
  rw [hs] at h
  have hlog : 2 * Real.log (Real.log q) ≤ Real.log ((refinedRadiusRoot q) ^ 2) := by
    rw [Real.log_pow]
    exact
      mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith only [hL]) hroot) (by norm_num only)
  have hA :
    refinedAuxiliaryTerm q ≤
      max 0 (Real.log ((refinedRadiusRoot q) ^ 2) - 32873 / 20800 - primeFactorLogSum q) :=
    max_le_max (le_refl _) (by linarith only [hlog])
  have hc : 0 ≤ 2 * refinedRadiusRoot q + 2 + Real.log ((refinedRadiusRoot q) ^ 2) :=
    add_nonneg (add_nonneg (mul_nonneg (by norm_num only) hy.le) (by norm_num only))
      (Real.log_nonneg (le_trans (by norm_num only) hx))
  have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_left hA (Real.log q / 2 + 9 / 50)) hc
  linarith only [h, hmul]

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- Under RH and prime triviality up to x>1, the original-level logarithmic sum
is bounded below by the Riemann main term minus its zero-mass error and the common-factor cost.
Use the exact arbitrary-cutoff support identity and the uniform common-factor estimate.
This is the lower analytic input for the refined-radius comparison. -/
theorem characterLogWeightedSum_re_ge_riemann_of_prime_trivial {q : ℕ} [NeZero q] (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 1 < x) (hRH : RiemannHypothesis)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    x - Real.log (2 * Real.pi) * Real.log x - 1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt x + 1) -
        (1 / 2 : ℝ) * q.primeFactors.card * (Real.log x) ^ 2 ≤
      (characterLogWeightedSum x χ).re := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hr := llsRiemannWeightedLowerBound_of_riemannHypothesis hRH x hx
  have hc := commonFactorLogWeightedSum_le (NeZero.ne q) hx0
  rw [characterLogWeightedSum_re_eq_sub_common_of_prime_trivial x χ hx0 htrivial]
  linarith only [hr, hc]

/-- For q≥3000, the squared cutoff logarithm is at most
4y(log(log(q)))²/log(q), where y is the refined radius root.
Use the decreasing squared-log ratio on [8,∞). This bounds the common-factor loss. -/
theorem log_sq_refinedRadius_le_level_ratio {q : ℕ} (hq : 3000 ≤ q) :
    (Real.log ((refinedRadiusRoot q) ^ 2)) ^ 2 ≤
      4 * refinedRadiusRoot q * (Real.log (Real.log q)) ^ 2 / Real.log q := by
  have hL := Analysis.eight_lt_log_level hq
  have hroot : Real.log q ≤ refinedRadiusRoot q := le_add_of_nonneg_right (le_max_left _ _)
  have hy : 0 < refinedRadiusRoot q :=
    lt_of_lt_of_le (lt_trans (by norm_num only : (0 : ℝ) < 8) hL) hroot
  have h := Analysis.strictAntiOn_logSquareRatio.antitoneOn hL.le (hL.le.trans hroot) hroot
  change
    (Real.log (refinedRadiusRoot q)) ^ 2 / refinedRadiusRoot q ≤
      (Real.log (Real.log q)) ^ 2 / Real.log q at h
  have hh := (div_le_iff₀ hy).mp h
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat] at ⊢
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith only [hh]

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- Under GRH and prime triviality up to the refined radius for q≥3000,
the logarithmic sum has the Riemann lower bound with common-factor cost
2yω(q)(log(log(q)))²/log(q). Monotonicity of the squared-log ratio controls the cost.
This matches the prime-factor term in the refined correction B*(q). -/
theorem characterLogWeightedSum_re_ge_refinedRadius {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (refinedRadiusRoot q) ^ 2 → χ p = 1) :
    (refinedRadiusRoot q) ^ 2 -
        refinedRadiusRoot q *
          (2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass +
            2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q) -
        Real.log (2 * Real.pi) * Real.log ((refinedRadiusRoot q) ^ 2) -
        1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤
      (characterLogWeightedSum ((refinedRadiusRoot q) ^ 2) χ).re := by
  have hL := Analysis.eight_lt_log_level hq
  have hroot : Real.log q ≤ refinedRadiusRoot q := le_add_of_nonneg_right (le_max_left _ _)
  have hy : 0 < refinedRadiusRoot q :=
    lt_of_lt_of_le (lt_trans (by norm_num only : (0 : ℝ) < 8) hL) hroot
  have hx : (1 : ℝ) < (refinedRadiusRoot q) ^ 2 := by nlinarith only [hL, hroot]
  have h :=
    characterLogWeightedSum_re_ge_riemann_of_prime_trivial ((refinedRadiusRoot q) ^ 2) χ hx
      hGRH.riemann htrivial
  rw [Real.sqrt_sq hy.le] at h
  have hloss := log_sq_refinedRadius_le_level_ratio hq
  have hw : (0 : ℝ) ≤ (1 / 2 : ℝ) * q.primeFactors.card :=
    mul_nonneg (by norm_num only) (Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hloss hw
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [h, hm]

/-- Under GRH, every nonprincipal complex character of level q≥3000 has a prime
not dividing q with character value different from one below the refined radius squared.
A counterexample gives prime triviality at that radius; the refined logarithmic
upper and lower bounds are incompatible by the explicit real-variable separation.
This is the improved Part 1 character witness theorem with additive correction two. -/
theorem exists_prime_character_ne_one_le_refinedRadius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ (refinedRadiusRoot q) ^ 2 := by
  by_contra hn
  have htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (refinedRadiusRoot q) ^ 2 → χ p = 1 := by
    intro p hp hd hb
    by_contra hv
    exact hn ⟨p, hp, hd, hv, hb⟩
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim : χ.primitiveCharacter ≠ 1 := by
    intro hp
    have hc := χ.changeLevel_primitiveCharacter
    rw [hp, DirichletCharacter.changeLevel_one] at hc
    exact hne hc.symm
  have hN : 2 ≤ χ.conductor :=
    Nat.succ_le_iff.mpr
      (Nat.lt_of_le_of_ne (NeZero.pos χ.conductor)
        (Ne.symm
          (AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one
            hprim)))
  have hu := characterLogWeightedSum_re_le_refinedRadius χ hq hN hprim hGRH htrivial
  have hl := characterLogWeightedSum_re_ge_refinedRadius χ hq hGRH htrivial
  have hP : (57 / 50 : ℝ) ≤ Real.log Real.pi := by
    have hp := Analysis.log_two_mul_pi_gt
    rw [Real.log_mul (by norm_num only) Real.pi_ne_zero] at hp
    linarith only [hp, Real.log_two_lt_d9]
  have hB :
    2 * Real.log (Real.log q) + 2 +
          2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
        2 * refinedAuxiliaryTerm q ≤
      refinedRadiusRoot q - Real.log q := by
    change _ ≤ (Real.log q + refinedCorrectionTerm q) - Real.log q
    rw [add_sub_cancel_left]
    exact le_max_right _ _
  exact
    Analysis.refinedPart1_bounds_incompatible (Analysis.eight_lt_log_level hq)
      (le_add_of_nonneg_right (le_max_left _ _)) (le_max_left _ _)
      AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth hP
      Analysis.log_two_mul_pi_lt.le hB hu hl

end PseudoPrime.LLS
