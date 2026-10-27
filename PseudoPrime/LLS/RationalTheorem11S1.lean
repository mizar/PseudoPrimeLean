/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RefinedTheorem11S1
public import PseudoPrime.Analysis.RationalPart1Separation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorSplitBounds

/-! # Rational Part 1 radius and universal logarithmic profile -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The rational nonnegative Part 1 correction uses constant 499/250,
the distinct-prime loss and the existing reciprocal saving.
Its value is the positive part of 2 log log q+499/250+w(q)-2A*(q).
This defines the improved radius while retaining the exact factorization correction. -/
noncomputable def rationalCorrectionTerm (q : ℕ) : ℝ :=
  max 0
    (2 * Real.log (Real.log q) + 499 / 250 +
        2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
      2 * refinedAuxiliaryTerm q)

/-- The rational Part 1 radius root is log q plus its nonnegative correction.
Its square is the search cutoff. This is the factorization-sensitive pointwise expression. -/
noncomputable def rationalRadiusRoot (q : ℕ) : ℝ :=
  Real.log q + rationalCorrectionTerm q

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH, q ≥ 3000 and prime triviality through the rational radius,
the full-level logarithmic sum satisfies the displayed upper bound.
Use the arbitrary-cutoff estimate and monotonicity of the reciprocal saving.
This is the upper side of the rational Part 1 contradiction. -/
theorem characterLogWeightedSum_re_le_rationalRadius {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hq : 3000 ≤ q) (hN : 2 ≤ χ.conductor) (hne : χ.primitiveCharacter ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (rationalRadiusRoot q) ^ 2 → χ p = 1) :
    (characterLogWeightedSum ((rationalRadiusRoot q) ^ 2) χ).re ≤
      (2 * rationalRadiusRoot q + 2 + Real.log ((rationalRadiusRoot q) ^ 2)) *
            (Real.log q / 2 + 9 / 50 - refinedAuxiliaryTerm q) +
          (1 / 2 : ℝ) * (Real.log q - Real.log Real.pi) * Real.log ((rationalRadiusRoot q) ^ 2) -
        11 / 4 := by
  have hL := Analysis.eight_lt_log_level hq
  have hroot : Real.log q ≤ rationalRadiusRoot q := le_add_of_nonneg_right (le_max_left _ _)
  have hy : 0 < rationalRadiusRoot q :=
    lt_of_lt_of_le (lt_trans (by norm_num only : (0 : ℝ) < 8) hL) hroot
  have hx : (64 : ℝ) ≤ (rationalRadiusRoot q) ^ 2 := by nlinarith only [hL, hroot]
  have hs : Real.sqrt ((rationalRadiusRoot q) ^ 2) = rationalRadiusRoot q := Real.sqrt_sq hy.le
  have h :=
    characterLogWeightedSum_re_le_refined_fullLevel χ hN hne hGRH hx hL
      (by
        rw [hs]; exact hroot)
      htrivial
  rw [hs] at h
  have hlog : 2 * Real.log (Real.log q) ≤ Real.log ((rationalRadiusRoot q) ^ 2) := by
    rw [Real.log_pow]
    exact
      mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith only [hL]) hroot) (by norm_num only)
  have hA :
    refinedAuxiliaryTerm q ≤
      max 0 (Real.log ((rationalRadiusRoot q) ^ 2) - 32873 / 20800 - primeFactorLogSum q) :=
    max_le_max (le_refl _) (by linarith only [hlog])
  have hc : 0 ≤ 2 * rationalRadiusRoot q + 2 + Real.log ((rationalRadiusRoot q) ^ 2) :=
    add_nonneg (add_nonneg (mul_nonneg (by norm_num only) hy.le) (by norm_num only))
      (Real.log_nonneg (le_trans (by norm_num only) hx))
  have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_left hA (Real.log q / 2 + 9 / 50)) hc
  linarith only [h, hmul]

/-- For q ≥ 3000, the squared logarithm of the rational cutoff is bounded
by the ambient squared-log ratio. Apply its monotonicity on the half-line from eight.
This controls the exact common-factor loss at the smaller radius. -/
theorem log_sq_rationalRadius_le_level_ratio {q : ℕ} (hq : 3000 ≤ q) :
    (Real.log ((rationalRadiusRoot q) ^ 2)) ^ 2 ≤
      4 * rationalRadiusRoot q * (Real.log (Real.log q)) ^ 2 / Real.log q := by
  have hL := Analysis.eight_lt_log_level hq
  have hroot : Real.log q ≤ rationalRadiusRoot q := le_add_of_nonneg_right (le_max_left _ _)
  have hy : 0 < rationalRadiusRoot q :=
    lt_of_lt_of_le (lt_trans (by norm_num only : (0 : ℝ) < 8) hL) hroot
  have h := Analysis.strictAntiOn_logSquareRatio.antitoneOn hL.le (hL.le.trans hroot) hroot
  change
    (Real.log (rationalRadiusRoot q)) ^ 2 / rationalRadiusRoot q ≤
      (Real.log (Real.log q)) ^ 2 / Real.log q at h
  have hh := (div_le_iff₀ hy).mp h
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat] at ⊢
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith only [hh]

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- Under GRH, q ≥ 3000 and prime triviality through the rational radius,
the original-level logarithmic sum has the displayed Riemann lower bound and local loss.
Apply the generic support identity and squared-log ratio comparison.
This supplies the lower side for the rational correction. -/
theorem characterLogWeightedSum_re_ge_rationalRadius {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (rationalRadiusRoot q) ^ 2 → χ p = 1) :
    (rationalRadiusRoot q) ^ 2 -
        rationalRadiusRoot q *
          (2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass +
            2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q) -
        Real.log (2 * Real.pi) * Real.log ((rationalRadiusRoot q) ^ 2) -
        1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤
      (characterLogWeightedSum ((rationalRadiusRoot q) ^ 2) χ).re := by
  have hL := Analysis.eight_lt_log_level hq
  have hroot : Real.log q ≤ rationalRadiusRoot q := le_add_of_nonneg_right (le_max_left _ _)
  have hy : 0 < rationalRadiusRoot q :=
    lt_of_lt_of_le (lt_trans (by norm_num only : (0 : ℝ) < 8) hL) hroot
  have hx : (1 : ℝ) < (rationalRadiusRoot q) ^ 2 := by nlinarith only [hL, hroot]
  have h :=
    characterLogWeightedSum_re_ge_riemann_of_prime_trivial ((rationalRadiusRoot q) ^ 2) χ hx
      hGRH.riemann htrivial
  rw [Real.sqrt_sq hy.le] at h
  have hloss := log_sq_rationalRadius_le_level_ratio hq
  have hw : (0 : ℝ) ≤ (1 / 2 : ℝ) * q.primeFactors.card :=
    mul_nonneg (by norm_num only) (Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hloss hw
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [h, hm]

/-- Under GRH, a nonprincipal character at q ≥ 3000 has a coprime prime
with non-one value through the rational Part 1 radius squared.
A contrary prime-triviality condition contradicts the rational upper and lower bounds.
This improves the pointwise correction from two to 499/250. -/
theorem exists_prime_character_ne_one_le_rationalRadius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ (rationalRadiusRoot q) ^ 2 := by
  by_contra hn
  have htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (rationalRadiusRoot q) ^ 2 → χ p = 1 := by
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
  have hu := characterLogWeightedSum_re_le_rationalRadius χ hq hN hprim hGRH htrivial
  have hl := characterLogWeightedSum_re_ge_rationalRadius χ hq hGRH htrivial
  have hP : (57 / 50 : ℝ) ≤ Real.log Real.pi := by
    have hp := Analysis.log_two_mul_pi_gt
    rw [Real.log_mul (by norm_num only) Real.pi_ne_zero] at hp
    linarith only [hp, Real.log_two_lt_d9]
  have hB :
    2 * Real.log (Real.log q) + 499 / 250 +
          2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
        2 * refinedAuxiliaryTerm q ≤
      rationalRadiusRoot q - Real.log q := by
    change _ ≤ (Real.log q + rationalCorrectionTerm q) - Real.log q
    rw [add_sub_cancel_left]
    exact le_max_right _ _
  exact
    Analysis.refinedPart1_bounds_incompatible_fourNinetyNine_twoFiftieths
      (Analysis.eight_lt_log_level hq) (le_add_of_nonneg_right (le_max_left _ _)) (le_max_left _ _)
      AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth hP
      Analysis.log_two_mul_pi_lt.le hB hu hl

end PseudoPrime.LLS

namespace PseudoPrime.Analysis

/-- For L > 0, log L/L^(3/8) ≤ 491/500. Apply the logarithm tangent at
1359/500 to L^(3/8) and use the certified exponential lower bound at one.
This supplies the rational factor-support parameter for exponent 5/8. -/
theorem log_div_rpow_three_eighths_le {L : ℝ} (hL : 0 < L) :
    Real.log L / L ^ (3 / 8 : ℝ) ≤ 491 / 500 := by
  have hu0 := Real.rpow_pos_of_pos hL (3 / 8 : ℝ)
  have ht := Real.log_le_sub_one_of_pos (div_pos hu0 (by norm_num only : (0 : ℝ) < 1359 / 500))
  rw [Real.log_div hu0.ne' (by norm_num only : (1359 / 500 : ℝ) ≠ 0), Real.log_rpow hL] at ht
  have ha : Real.log (1359 / 500 : ℝ) < 1 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num only : (0 : ℝ) < 1359 / 500)).mpr
    exact (by norm_num only : (1359 / 500 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
  rw [div_le_iff₀ hu0]
  linarith only [ht, ha, hu0]

end PseudoPrime.Analysis

namespace PseudoPrime.LLS

/-- For q ≥ 3000, the factor-sensitive rational radius is at most
log q+(1791/250)log log q+499/250. Split the prime support at (log q)^(5/8),
use the global logarithmic-power ratio and discard the nonnegative reciprocal saving.
This converts Part 1 to a single rational-coefficient expression. -/
theorem rationalRadiusRoot_le_logarithmic_shift {q : ℕ} [NeZero q] (hq : 3000 ≤ q) :
    rationalRadiusRoot q ≤ Real.log q + (1791 / 250 : ℝ) * Real.log (Real.log q) + 499 / 250 := by
  let L := Real.log q
  let z := Real.log L
  let u := L ^ (3 / 8 : ℝ)
  have hL8 := Analysis.eight_lt_log_level hq
  have hL : 1 < L := by linarith only [hL8]
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hz0 : 0 < z := Real.log_pos hL
  have hu0 := Real.rpow_pos_of_pos hL0 (3 / 8 : ℝ)
  have hratio := Analysis.log_div_rpow_three_eighths_le hL0
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_log_power (NeZero.ne q) hL
      (by norm_num only : (0 : ℝ) < 5 / 8)
  have hpow : L ^ (5 / 8 : ℝ) = L / u := by
    apply (eq_div_iff hu0.ne').mpr
    rw [← Real.rpow_add hL0]
    norm_num only [Real.rpow_one]
  have hcan : L / ((5 / 8 : ℝ) * z) = (8 / 5 : ℝ) * L / z := by
    rw [div_mul_eq_div_div]
    ring
  change (q.primeFactors.card : ℝ) ≤ L ^ (5 / 8 : ℝ) + L / ((5 / 8 : ℝ) * z) at hcard
  rw [hpow, hcan] at hcard
  have hm := mul_le_mul_of_nonneg_right hcard (div_nonneg hz0.le hL0.le)
  have he : (L / u + (8 / 5 : ℝ) * L / z) * (z / L) = z / u + 8 / 5 := by
    calc
      _ = (z / u) * (L / L) + (8 / 5 : ℝ) * ((L / z) * z / L) := by ring
      _ = z / u + 8 / 5 := by
        rw [div_self hL0.ne', div_mul_cancel₀ _ hz0.ne', div_self hL0.ne', mul_one, mul_one]
  rw [he] at hm
  have hstep : (q.primeFactors.card : ℝ) * (z / L) ≤ 491 / 500 + 8 / 5 := by
    linarith only [hm, hratio]
  have hw := mul_le_mul_of_nonneg_left hstep (show 0 ≤ 2 * z by linarith only [hz0])
  have hwe :
    2 * z * ((q.primeFactors.card : ℝ) * (z / L)) = 2 * (q.primeFactors.card : ℝ) * z ^ 2 / L := by
    ring
  rw [hwe] at hw
  have hA : 0 ≤ refinedAuxiliaryTerm q := le_max_left _ _
  have hB : rationalCorrectionTerm q ≤ (1791 / 250 : ℝ) * z + 499 / 250 := by
    unfold rationalCorrectionTerm
    apply max_le (by linarith only [hz0])
    change
      2 * z + 499 / 250 + 2 * (q.primeFactors.card : ℝ) * z ^ 2 / L - 2 * refinedAuxiliaryTerm q ≤
        (1791 / 250 : ℝ) * z + 499 / 250
    linarith only [hw, hA]
  unfold rationalRadiusRoot
  linarith only [hB]

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Under GRH, every nonprincipal character at q ≥ 3000 has a coprime prime
with non-one value through (log q+(1791/250)log log q+499/250)².
Compare the nonnegative rational radius roots and transfer the existing witness.
This realizes the rational triple (1,1791/250,499/250) at starting value 3000. -/
theorem exists_prime_character_ne_one_le_rationalProfile3000 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 3000 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        χ p ≠ 1 ∧
        (p : ℝ) ≤ (Real.log q + (1791 / 250 : ℝ) * Real.log (Real.log q) + 499 / 250) ^ 2 := by
  have hq0 : q ≠ 0 := Nat.ne_zero_of_lt ((by decide : (0 : ℕ) < 3000).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  obtain ⟨p, hp, hd, hv, hb⟩ := exists_prime_character_ne_one_le_rationalRadius χ hq hne hGRH
  have hR := rationalRadiusRoot_le_logarithmic_shift hq
  have hR0 : 0 ≤ rationalRadiusRoot q := by
    unfold rationalRadiusRoot
    have hL := Analysis.eight_lt_log_level hq
    have hB : 0 ≤ rationalCorrectionTerm q := le_max_left _ _
    linarith only [hL, hB]
  exact ⟨p, hp, hd, hv, hb.trans ((sq_le_sq₀ hR0 (hR0.trans hR)).mpr hR)⟩

end PseudoPrime.LLS
