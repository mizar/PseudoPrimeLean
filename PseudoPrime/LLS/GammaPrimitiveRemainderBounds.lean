/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaLeftIntegralBounds
public import PseudoPrime.LLS.GammaPoleBounds
public import PseudoPrime.LLS.GammaArchimedeanBounds

/-! # Explicit primitive Gamma remainder

The fixed-contour completed formula combines numerical archimedean, pole and
left-integral bounds. The resulting contract includes small primitive conductors.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For ambient q≥20000, primitive nonprincipal conductor 3≤m≤q,
nonprincipal inverse and GRH, the Gamma arithmetic sum plus its oscillatory
zero sum has norm at most 15+(10002log(q)+10004)/sqrt(x), at x≥1.
Fix the lines -9/16 and 9/16, then combine the completed formula,
explicit archimedean integral, pole and left integral bounds.
This retains small primitive conductors in the numerical remainder. -/
theorem norm_gamma_primitive_remainder_le_explicit {q m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    ‖(∑' n : ℕ, gammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ)‖ ≤
      15 + (10002 * Real.log q + 10004) / Real.sqrt x := by
  let S := ∑' n : ℕ, gammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ
  let P :=
    MellinKernel.weightedResidue gammaMellinKernel (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x
      (-1 / 2)
  let L :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))
  have hr : ‖S - (P - Z + L)‖ ≤ 15 :=
    norm_gamma_completed_remainder_le_fifteen (by linarith only [hm]) hGRH hp hne hinv (a :=
      -9 / 16) (b := 9 / 16) (by norm_num only)
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) hx (by norm_num only) (by norm_num only)
  have hP := gamma_poleResidue_le_ambient hq hm hmq hp hne hGRH (zero_lt_one.trans_le hx)
  have hL := norm_gamma_left_integral_le_div_sqrt hp hne hinv hx
  have hmqR : (m : ℝ) ≤ q := by exact_mod_cast hmq
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by linarith only [hm] : 0 < m)
  have hlog := Real.log_le_log hmpos hmqR
  have hnum :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by norm_num only : (0 : ℝ) ≤ 10000))
      (Real.sqrt_nonneg x)
  have he : S + Z = (S - (P - Z + L)) + P + L := by ring
  change ‖S + Z‖ ≤ _
  rw [he]
  have hn1 := norm_add_le (S - (P - Z + L)) P
  have hn2 := norm_add_le ((S - (P - Z + L)) + P) L
  have hlognonneg : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast (by linarith only [hq] : 1 ≤ q))
  have hgap :=
    div_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 5 / 6) hlognonneg) (Real.sqrt_nonneg x)
  have hscalar :
    ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x + 10000 * (Real.log m + 1) / Real.sqrt x ≤
      (10002 * Real.log q + 10004) / Real.sqrt x := by
    simp only [div_eq_mul_inv] at hnum hgap ⊢
    nlinarith only [hnum, hgap]
  change ‖P‖ ≤ ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x at hP
  change ‖L‖ ≤ 10000 * (Real.log m + 1) / Real.sqrt x at hL
  linarith only [hr, hP, hL, hn1, hn2, hscalar]

/-- Under the same ambient and primitive GRH conditions, at x≥4 the full
Gamma remainder is bounded by 20006(1+log(q)log(x)/sqrt(x)).
Absorb its explicit affine conductor error using log(q),log(x)≥1.
This supplies a numerical fixed-kernel remainder contract with explicit
application ranges, without including zero mass or local Euler corrections. -/
theorem norm_gamma_primitive_remainder_le_contract {q m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 4 ≤ x) :
    ‖(∑' n : ℕ, gammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ)‖ ≤
      20006 * (1 + Real.log q * Real.log x / Real.sqrt x) := by
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only
    linarith only [Real.log_two_gt_d9]
  have hlogx : 1 ≤ Real.log x := hlog4.trans (Real.log_le_log (by norm_num only) hx)
  have hq4 : (4 : ℝ) ≤ q := by exact_mod_cast (by linarith only [hq] : 4 ≤ q)
  have hlogq : 1 ≤ Real.log q := hlog4.trans (Real.log_le_log (by norm_num only) hq4)
  have hnum : 10002 * Real.log q + 10004 ≤ 20006 * Real.log q := by linarith only [hlogq]
  have hd1 := div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg x)
  have hmux := mul_le_mul_of_nonneg_left hlogx (by nlinarith only [hlogq] : 0 ≤ 20006 * Real.log q)
  rw [mul_one] at hmux
  have hd2 := div_le_div_of_nonneg_right hmux (Real.sqrt_nonneg x)
  calc
    _ ≤ 15 + (10002 * Real.log q + 10004) / Real.sqrt x :=
      norm_gamma_primitive_remainder_le_explicit hq hm hmq hp hne hinv hGRH (by linarith only [hx])
    _ ≤ 20006 + (20006 * Real.log q * Real.log x) / Real.sqrt x := by linarith only [hd1, hd2]
    _ = _ := by ring

end PseudoPrime.LLS.PaperStatements
