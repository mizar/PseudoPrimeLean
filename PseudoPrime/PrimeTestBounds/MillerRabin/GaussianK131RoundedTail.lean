/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EndpointTails
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EndpointTails
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131CoeffCheck
import Mathlib.Tactic.FinCases

/-! # Shared rounded coefficient bounds for the raw K131 cells -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def rounded19 : Fin 20 → ℤ :=
  ![-143394280365386868428363, 184523734894847338005573, -115945873234613485935918,
    46149043126595044401252, -12912730073927996664836, 2759142158490784648635,
    -489403589347016495220, 76798230458379180535, -10730466455067483787, 1302465954767897041,
    -136805067860074688, 13045208318221160, -1203319918333142, 107247697889936, -8490197712414,
    547630798688, -27149370339, 980442702, -23068716, 267767]

private def rounded27 : Fin 20 → ℤ :=
  ![-213997594295942946647687, 330639599516494550907150, -262410337979460861832008,
    139829517144107148994559, -55127723494371109973136, 16910231348666755188993,
    -4019744759459288665434, 740593232134580507707, -105846636341646124084, 12095918950104416779,
    -1169626694838941808, 105890625029472833, -9622428454886734, 858298973829658, -67898969452279,
    4382439069295, -217125789921, 7846133692, -184485133, 2142920]

private def roundedCoeff (table : Fin 20 → ℤ) (j : Fin 20) : ℚ :=
  (table j : ℚ) / 1000000000000000000

set_option maxHeartbeats 1000000 in
-- Check all twenty rational coefficient bounds once for every cell.
private theorem rounded19_check (j : Fin 20) :
    poly19LinearUpper {j.val} id (fun _ ↦ -1) ≤ roundedCoeff rounded19 j := by
  fin_cases j <;> decide +kernel

set_option maxHeartbeats 1000000 in
-- Check all twenty rational coefficient bounds once for every cell.
private theorem rounded27_check (j : Fin 20) :
    tailPoly27LinearUpper {j.val} id (fun _ ↦ -1) ≤ roundedCoeff rounded27 j := by
  fin_cases j <;> decide +kernel

private theorem rounded19_sound (j : Fin 20) :
    -gaussianK131Poly19.coeff j.val ≤ (roundedCoeff rounded19 j : ℝ) := by
  have h := (poly19_linear_le {j.val} id (fun _ ↦ -1)).trans (Rat.cast_le.mpr (rounded19_check j))
  simpa only [Finset.sum_singleton, id_eq, Rat.cast_neg, Rat.cast_one, neg_one_mul] using h

private theorem rounded27_sound (j : Fin 20) :
    -gaussianK131TailPoly27.coeff j.val ≤ (roundedCoeff rounded27 j : ℝ) := by
  have h :=
    (tail_poly27_linear_le {j.val} id (fun _ ↦ -1)).trans (Rat.cast_le.mpr (rounded27_check j))
  simpa only [Finset.sum_singleton, id_eq, Rat.cast_neg, Rat.cast_one, neg_one_mul] using h

private def roundedShift (table : Fin 20 → ℤ) (a : ℚ) (j : ℕ) : ℚ :=
  ∑ k : Fin 20, roundedCoeff table k * (a ^ (k.val - j) * (k.val.choose j : ℚ))

private theorem rounded_shift_sound {P : Polynomial ℝ} (hP : P.natDegree < 20) {table : Fin 20 → ℤ}
    (h : ∀ k : Fin 20, -P.coeff k.val ≤ (roundedCoeff table k : ℝ)) {a : ℚ} (ha : 0 ≤ a) (j : ℕ) :
    -((shiftPoly P (a : ℝ)).coeff j) ≤ (roundedShift table a j : ℝ) := by
  rw [shifted_coeff_neg_eq hP, ← Fin.sum_univ_eq_sum_range]
  simp only [roundedShift, Rat.cast_sum]
  apply Finset.sum_le_sum
  intro k _
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, shiftedNegWeight, Rat.cast_neg]
  have hw :=
    mul_le_mul_of_nonneg_right (h k)
      (mul_nonneg (pow_nonneg (Rat.cast_nonneg.mpr ha) (k.val - j))
        (Nat.cast_nonneg (α := ℝ) (k.val.choose j)))
  exact (le_of_eq (by ring)).trans hw

/-- The two K131 main-term costs, using the same rounded coefficient
bounds on every log cell. -/
public def k131RoundedTailCap (a b r : ℚ) : ℚ :=
  rawTailPowerCap (shiftedEvalCap (roundedShift rounded19 a) (b - a))
    (shiftedEvalCap (roundedShift rounded27 a) (b - a)) r

/-- The common coefficient bounds give a rational lower bound on both
K131 main terms on every certified log cell. -/
public theorem k131_rounded_tail_cap_sound {y : ℝ} {a b r : ℚ} (hy : 0 ≤ y) (ha : 0 ≤ a)
    (hr : 0 < r) (hroot : (r : ℝ) ≤ y ^ (1 / 8 : ℝ))
    (hx : 2 * Real.log y ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    -(k131RoundedTailCap a b r : ℝ) ≤
      logPowerPoly (-(19 / 8 : ℝ)) gaussianK131Poly19 y +
        logPowerPoly (-(27 / 8 : ℝ)) gaussianK131TailPoly27 y := by
  exact
    raw_tail_power_cap_sound hy hr hroot
      (shifted_eval_cap_sound gaussian_k131_poly19_degree hx
        (rounded_shift_sound (Nat.lt_succ_of_le gaussian_k131_poly19_degree) rounded19_sound ha))
      (shifted_eval_cap_sound tail_poly27_degree hx
        (rounded_shift_sound (Nat.lt_succ_of_le tail_poly27_degree) rounded27_sound ha))

end PseudoPrime.PrimeTestBounds.MillerRabin
