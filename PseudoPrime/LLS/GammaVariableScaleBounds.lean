/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSmoothedNonprincipalBounds

/-! # Variable-scale Gamma budgets

Retain the explicit pole and left-moment errors at every scale at least one.
No logarithmic threshold or artificial large-scale decay gate is needed.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal conductor 3≤m≤q, q≥20000 and scale x≥1 under GRH,
 bound the completed Gamma remainder by the archimedean constant and explicit pole and
 left-moment expressions. Combine the completed formula with the actual moment integral.
 This removes the fixed logarithm 46000 and scale 3^16 gates from the remainder API. -/
theorem norm_gamma_primitive_remainder_le_variable_scale {q m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖(∑' n : ℕ, gammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ)‖ ≤
      64 / 9 + ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log m + 283) + 5 / 3) := by
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
  have hx1 : 1 ≤ x := hx
  have hr : ‖S - (P - Z + J)‖ ≤ 64 / 9 :=
    norm_gamma_completed_remainder_le_sixty_four_ninths (by linarith only [hm]) hGRH hp hne hinv
      (a := -9 / 16) (b := 9 / 16) (by norm_num only)
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) hx1 (by norm_num only) (by norm_num only)
  have hP0 := gamma_poleResidue_le_ambient hq hm hmq hp hne hGRH (zero_lt_one.trans_le hx1)
  have hP : ‖P‖ ≤ ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x := hP0
  have hJ : ‖J‖ ≤ x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log m + 283) + 5 / 3) :=
    norm_gamma_left_integral_le_moments hp hne hinv (zero_lt_one.trans_le hx)
  have he : S + Z = (S - (P - Z + J)) + P + J := by ring
  change ‖S + Z‖ ≤ _
  rw [he]
  have hn1 := norm_add_le (S - (P - Z + J)) P
  have hn2 := norm_add_le ((S - (P - Z + J)) + P) J
  linarith only [hr, hP, hJ, hn1, hn2]

/-- For the same primitive data and arbitrary scale x≥1, the real Gamma sum is at most
 Mlog(m)+24 plus the variable-scale remainder. Add the oscillatory zero-sum norm bound
 to the completed remainder. This retains the conductor and each scale-dependent error. -/
theorem gamma_primitive_sum_re_le_variable_scale {q m : ℕ} [NeZero m] (hq : 20000 ≤ q) (hm : 3 ≤ m)
    (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, gammaMellinKernel.summand χ x n).re ≤
      (11783423 / 25000000 : ℝ) * Real.log m + 24 + 64 / 9 +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log m + 283) + 5 / 3) := by
  let S := ∑' n : ℕ, gammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hz := norm_gamma_oscillatingZeroSum_lt (by linarith only [hm]) hGRH hp hne hinv hxpos
  have hr := norm_gamma_primitive_remainder_le_variable_scale hq hm hmq hp hne hinv hGRH hx
  have hn : ‖S‖ ≤ ‖S + Z‖ + ‖Z‖ := by
    have h := norm_sub_le (S + Z) Z
    rw [add_sub_cancel_right] at h
    exact h
  have hre := Complex.re_le_norm S
  change S.re ≤ _
  linarith only [hz.le, hr, hn, hre]

/-- For a nonprincipal character at level q≥20000 and scale x≥1 under GRH, bound its
 primitive Gamma sum with the actual conductor, ambient pole logarithm and explicit left error.
 Transfer to the primitive source and its inverse. This supplies the variable-scale upper input
 for coefficient-preserving non-one witness threshold optimization. -/
theorem gamma_primitiveCharacter_sum_re_le_variable_scale {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' n : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + 24 + 64 / 9 +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log χ.conductor + 283) + 5 / 3) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    gamma_primitive_sum_re_le_variable_scale hq hm hmq hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hnp (inv_ne_one.mpr hnp) hx

end PseudoPrime.LLS.PaperStatements
