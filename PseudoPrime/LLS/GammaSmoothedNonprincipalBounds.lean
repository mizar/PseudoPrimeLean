/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaCharacterUpperBounds
public import PseudoPrime.LLS.GammaLeftMomentBounds

/-! # Smoothed nonprincipal Gamma bounds

The zero mass and improved completed remainder retain the primitive conductor.
These bounds supply the upper arithmetic input for the ramp witness comparison.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For L≥46000, sqrt(x)≥9L/16 and Q≤L+2, the affine pole budget is at most
21/10. Clear the positive square-root denominator and certify the rational gap.
This is the endpoint contribution in the smoothed Gamma remainder. -/
theorem gamma_pole_budget_le_twenty_one_tenths {L x Q : ℝ} (hL : 46000 ≤ L)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hQ : Q ≤ L + 2) :
    ((7 / 6 : ℝ) * Q + 4) / Real.sqrt x ≤ 21 / 10 := by
  have hs : 0 < Real.sqrt x := by linarith only [hL, hroot]
  rw [div_le_iff₀ hs]
  nlinarith only [hL, hroot, hQ]

/-- Under GRH with primitive nonprincipal conductor 3≤m≤q and q≥20000,
the Gamma sum plus its zero sum has norm at most 64/9+21/10+2.
The stated scale and logarithm conditions control the archimedean, pole and left terms.
Small primitive conductors remain included in the actual completed formula. -/
theorem norm_gamma_primitive_remainder_le_smoothed {q m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L x : ℝ} (hL : 46000 ≤ L)
    (hx : (3 : ℝ) ^ 16 ≤ x) (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hlogq : Real.log q ≤ L + 2) :
    ‖(∑' n : ℕ, gammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ)‖ ≤
      64 / 9 + 21 / 10 + 2 := by
  let S := ∑' n : ℕ, gammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ
  let P :=
    MellinKernel.weightedResidue gammaMellinKernel (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x
      (-1 / 2)
  let J :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))
  have hx1 : 1 ≤ x := by
    norm_num only at hx
    linarith only [hx]
  have hr : ‖S - (P - Z + J)‖ ≤ 64 / 9 :=
    norm_gamma_completed_remainder_le_sixty_four_ninths (by linarith only [hm]) hGRH hp hne hinv
      (a := -9 / 16) (b := 9 / 16) (by norm_num only)
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) hx1 (by norm_num only) (by norm_num only)
  have hP0 := gamma_poleResidue_le_ambient hq hm hmq hp hne hGRH (zero_lt_one.trans_le hx1)
  have hP : ‖P‖ ≤ 21 / 10 := hP0.trans (gamma_pole_budget_le_twenty_one_tenths hL hroot hlogq)
  have hmqR : (m : ℝ) ≤ q := by exact_mod_cast hmq
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by linarith only [hm] : 0 < m)
  have hlogm := (Real.log_le_log hmpos hmqR).trans hlogq
  have hJ : ‖J‖ ≤ 2 := norm_gamma_left_integral_le_two_of_moments hp hne hinv hL hx hroot hlogm
  have he : S + Z = (S - (P - Z + J)) + P + J := by ring
  change ‖S + Z‖ ≤ _
  rw [he]
  have hn1 := norm_add_le (S - (P - Z + J)) P
  have hn2 := norm_add_le ((S - (P - Z + J)) + P) J
  linarith only [hr, hP, hJ, hn1, hn2]

/-- Under the ambient, primitive GRH and large-scale conditions, the real Gamma
arithmetic sum is at most Mlog(m)+24+64/9+21/10+2, with M=11783423/25000000.
Combine the actual oscillatory zero sum with the improved completed remainder.
The conductor is retained for later signed local corrections. -/
theorem gamma_primitive_sum_re_le_smoothed {q m : ℕ} [NeZero m] (hq : 20000 ≤ q) (hm : 3 ≤ m)
    (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {L x : ℝ} (hL : 46000 ≤ L) (hx : (3 : ℝ) ^ 16 ≤ x)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hlogq : Real.log q ≤ L + 2) :
    (∑' n : ℕ, gammaMellinKernel.summand χ x n).re ≤
      (11783423 / 25000000 : ℝ) * Real.log m + 24 + 64 / 9 + 21 / 10 + 2 := by
  let S := ∑' n : ℕ, gammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ
  have hxpos : 0 < x := (pow_pos (by norm_num only : (0 : ℝ) < 3) 16).trans_le hx
  have hz := norm_gamma_oscillatingZeroSum_lt (by linarith only [hm]) hGRH hp hne hinv hxpos
  have hr := norm_gamma_primitive_remainder_le_smoothed hq hm hmq hp hne hinv hGRH hL hx hroot hlogq
  have hn : ‖S‖ ≤ ‖S + Z‖ + ‖Z‖ := by
    have h := norm_sub_le (S + Z) Z
    rw [add_sub_cancel_right] at h
    exact h
  have hre := Complex.re_le_norm S
  change S.re ≤ _
  linarith only [hz.le, hr, hn, hre]

/-- For a nonprincipal character of level q≥20000, the primitive Gamma sum obeys
the smoothed upper bound with leading term Mlog(conductor).
The scale and log(q) conditions bound the remainder uniformly, including small conductors.
Pass to the nonprincipal primitive source and its inverse. -/
theorem gamma_primitiveCharacter_sum_re_le_smoothed {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L x : ℝ} (hL : 46000 ≤ L)
    (hx : (3 : ℝ) ^ 16 ≤ x) (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hlogq : Real.log q ≤ L + 2) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' n : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + 24 + 64 / 9 + 21 / 10 + 2 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    gamma_primitive_sum_re_le_smoothed hq hm hmq hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hnp (inv_ne_one.mpr hnp) hL hx hroot
      hlogq

/-- For nonprincipal level q≥20000, L≥46000 and log(q)≤L+2, the actual primitive
Gamma sum at x=(32/99)L² is bounded by Mlog(conductor)+24+64/9+21/10+2.
The fixed-scale gates follow from the proved square and square-root bounds.
This is the nonprincipal upper contract for the smoothed witness comparison. -/
theorem gamma_primitiveCharacter_sum_re_le_smoothed_at_ramp_scale {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 46000 ≤ L)
    (hlogq : Real.log q ≤ L + 2) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' n : ℕ, gammaMellinKernel.summand χ.primitiveCharacter ((32 / 99 : ℝ) * L ^ 2) n).re ≤
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + 24 + 64 / 9 + 21 / 10 + 2 := by
  exact
    gamma_primitiveCharacter_sum_re_le_smoothed hq χ hne hGRH hL (ramp_scale_ge_three_sixteenth hL)
      (Analysis.ramp_scale_sqrt_lower (by linarith only [hL])) hlogq

end PseudoPrime.LLS.PaperStatements
