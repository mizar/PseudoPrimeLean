/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Profile
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxReflection656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxReflection656

/-! # Joint reflection of the six K197 auxiliary shifts -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed degree-five polynomial that occurs in both the K197
conductor term and the joint reflection, with the common displacements. -/
@[expose]
noncomputable def gaussianJoint197 (v : ℝ) : ℝ :=
  -(∑ i,
      (gaussianCoeff197 i : ℝ) * Real.exp ((11 / 10 : ℝ) * quarterShift663 i) *
        (v - quarterShift663 i) ^ 5)

/-- Interchange the six shifts with the absolutely convergent Mangoldt
series to combine all reflected terms into one signed polynomial. -/
theorem gaussian_joint_reflection_eq_197 {r : ℝ} (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4) :
    (∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ)) =
      -((11 / 10 : ℝ) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ)) *
        ∑' n : ℕ,
          α n * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)) *
            gaussianJoint197 (2 * Real.log r + Real.log n) := by
  let C : ℝ := (11 / 10) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ)
  let c := fun i : Fin 6 ↦ (gaussianCoeff197 i : ℝ) * Real.exp ((11 / 10 : ℝ) * quarterShift663 i)
  let z := fun i : Fin 6 ↦ 2 * Real.log r - (quarterShift663 i : ℝ)
  let g := fun n : ℕ ↦ α n * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ))
  let w := fun (i : Fin 6) (n : ℕ) ↦ c i * (g n * (z i + Real.log n) ^ 5)
  have hs (i : Fin 6) : Summable (w i) := (reflection_summable α hα (z i)).mul_left (c i)
  have hrow (i : Fin 6) :
    (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) =
      C * ∑' n, w i n := by
    dsimp only [quarterAuxReflection656, w, c, z, g, C]
    rw [tsum_mul_left]
    ring
  simp only [hrow, ← Finset.mul_sum, ← Summable.tsum_finsetSum (fun i _ ↦ hs i)]
  rw [← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  have harg (i : Fin 6) :
    z i + Real.log n = (2 * Real.log r + Real.log n) - (quarterShift663 i : ℝ) := by
    dsimp only [z]
    ring
  simp only [w, c, harg, gaussianJoint197]
  simp only [mul_neg, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [C, g]
  ring

/-- A nonnegative bound for the joint polynomial on the unknown support
bounds the six shifts together, with only one factor of four. -/
theorem gaussian_joint_reflection_lower_197 {r : ℝ} (hr : 0 < r) (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0)
    (E : ℝ → ℝ) (hE : ∀ t : ℝ, 0 ≤ t → 0 ≤ E t ∧ gaussianJoint197 (4 * Real.log r + t) ≤ E t)
    (hs :
      Summable
        (fun n : ℕ ↦
          if r ^ 2 < (n : ℝ) then
            (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)) *
              E (Real.log n - 2 * Real.log r)
          else 0)) :
    -4 * ((11 / 10 : ℝ) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ)) *
        (∑' n : ℕ,
          if r ^ 2 < (n : ℝ) then
            (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)) *
              E (Real.log n - 2 * Real.log r)
          else 0) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  let A := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)
  let f := fun n : ℕ ↦ α n * A n * gaussianJoint197 (2 * Real.log r + Real.log n)
  let g := fun n : ℕ ↦ if r ^ 2 < (n : ℝ) then A n * E (Real.log n - 2 * Real.log r) else 0
  have hf : Summable f := by
    have h :=
      (summable_sum (s := Finset.univ)
          (fun i : Fin 6 ↦ fun _ ↦
            (reflection_summable α hα (2 * Real.log r - quarterShift663 i)).mul_left
              ((gaussianCoeff197 i : ℝ) * Real.exp ((11 / 10 : ℝ) * quarterShift663 i)))).neg
    apply h.congr
    intro n
    dsimp only [f, A, Pi.neg_apply, gaussianJoint197]
    simp only [mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hterm (n : ℕ) : f n ≤ 4 * g n := by
    by_cases hn : r ^ 2 < (n : ℝ)
    · have ht : 0 ≤ Real.log n - 2 * Real.log r := by
        have h := Real.log_le_log (sq_pos_of_pos hr) hn.le
        rw [Real.log_pow, Nat.cast_ofNat] at h
        linarith only [h]
      have he := hE _ ht
      have he' :
        gaussianJoint197 (2 * Real.log r + Real.log n) ≤ E (Real.log n - 2 * Real.log r) := by
        convert he.2 using 2
        ring
      have h :=
        (mul_le_mul_of_nonneg_left he' (hα n).1).trans (mul_le_mul_of_nonneg_right (hα n).2 he.1)
      have hh :=
        mul_le_mul_of_nonneg_left h
          (show 0 ≤ A n from
            div_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      dsimp only [f, g]
      rw [ite_eq_left hn]
      linear_combination hh
    · dsimp only [f, g]
      rw [ite_eq_right hn]
      by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
      · simp only [A, hΛ, zero_div, mul_zero, zero_mul, le_refl]
      · simp only [hprefix n (le_of_not_gt hn) hΛ, zero_mul, mul_zero, le_refl]
  have h := hf.tsum_le_tsum hterm (hs.mul_left 4)
  rw [tsum_mul_left] at h
  rw [gaussian_joint_reflection_eq_197 α hα]
  have hb :=
    mul_le_mul_of_nonpos_left h
      (show -((11 / 10 : ℝ) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ)) ≤ 0 from
        neg_nonpos.mpr (by positivity))
  dsimp only [f, g, A] at hb
  linear_combination hb

end PseudoPrime.PrimeTestBounds.MillerRabin
