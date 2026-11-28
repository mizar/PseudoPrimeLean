/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxNumerics656
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.EulerDerivatives

/-! # Pairwise comparison of the section 132 reflected deficits -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The reflected Euler deficit at displacement h, with a common trace
deficit and the section 132 normalization. -/
noncomputable def quarterAuxReflection656 (α : ℕ → ℝ) (r h : ℝ) : ℝ :=
  ((11 / 10 : ℝ) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ) * Real.exp ((11 / 10) * h)) *
    ∑' n : ℕ,
      α n * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)) *
        (2 * Real.log r - h + Real.log n) ^ 5

private theorem reflection_summable (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4) (z : ℝ) :
    Summable
      (fun n : ℕ ↦
        α n * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)) *
          (z + Real.log n) ^ 5) := by
  have hm (k : ℕ) :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 8 / 5)
      (by norm_num only) k
  have hs :
    Summable
      (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ) * (z + Real.log n) ^ 5) := by
    have h :=
      ((((((hm 0).mul_left (z ^ 5)).add ((hm 1).mul_left (5 * z ^ 4))).add
                    ((hm 2).mul_left (10 * z ^ 3))).add
                ((hm 3).mul_left (10 * z ^ 2))).add
            ((hm 4).mul_left (5 * z))).add
        (hm 5)
    apply h.congr
    intro n
    ring
  apply (hs.norm.mul_left 4).of_norm_bounded
  intro n
  rw [mul_assoc, norm_mul, Real.norm_eq_abs (α n), abs_of_nonneg (hα n).1]
  exact mul_le_mul_of_nonneg_right (hα n).2 (norm_nonneg _)

/-- Moving from a smaller displacement to a larger one decreases
the logarithmic weight after removing the change in exponential scale. -/
theorem quarter_aux_reflection_compare_656 (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4) {r u v : ℝ}
    (hr : 0 < r) (huv : u ≤ v) (hv : v ≤ 2 * Real.log r) :
    Real.exp (-(11 / 10) * (v - u)) * quarterAuxReflection656 α r v ≤
      quarterAuxReflection656 α r u := by
  have h :=
    (reflection_summable α hα (2 * Real.log r - v)).tsum_le_tsum
      (fun n ↦
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (add_nonneg (sub_nonneg.mpr hv) (Real.log_natCast_nonneg n))
            (by linarith only [huv]) 5)
          (mul_nonneg (hα n).1
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (Real.rpow_nonneg (Nat.cast_nonneg n) _))))
      (reflection_summable α hα (2 * Real.log r - u))
  unfold quarterAuxReflection656
  have he :
    Real.exp (-(11 / 10 : ℝ) * (v - u)) * Real.exp ((11 / 10) * v) = Real.exp ((11 / 10) * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hh :=
    mul_le_mul_of_nonneg_left h
      (show 0 ≤ (11 / 10 : ℝ) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ) * Real.exp ((11 / 10) * u) by
        positivity)
  rw [← he] at hh
  rw [← he]
  convert hh using 1
  ring

/-- One positive coefficient absorbs part of its paired negative
coefficient, leaving only the larger displacement in the lower bound. -/
theorem quarter_aux_reflection_pair_656 (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4) {r u v c d : ℝ}
    (hr : 0 < r) (huv : u ≤ v) (hv : v ≤ 2 * Real.log r) (hc : 0 ≤ c) :
    (d + c * Real.exp (-(11 / 10) * (v - u))) * quarterAuxReflection656 α r v ≤
      c * quarterAuxReflection656 α r u + d * quarterAuxReflection656 α r v := by
  have h := mul_le_mul_of_nonneg_left (quarter_aux_reflection_compare_656 α hα hr huv hv) hc
  linarith only [h]

/-- The amount of the negative coefficient left after one positive
coefficient has been paired with it. -/
noncomputable def quarterAuxPairLoss656 (i j : Fin 7) : ℝ :=
  -quarterAuxCoeff656 j -
    quarterAuxCoeff656 i *
      Real.exp (-(11 / 10) * ((quarterAuxShift656 j : ℝ) - quarterAuxShift656 i))

private theorem shifts_order (i j : Fin 7) (hij : i ≤ j) :
    (quarterAuxShift656 i : ℝ) ≤ quarterAuxShift656 j := by
  have h : ∀ i j, i ≤ j → quarterAuxShift656 i ≤ quarterAuxShift656 j := by decide +kernel
  exact_mod_cast h i j hij

private theorem positive_coeff (i : Fin 7) (hi : i = 0 ∨ i = 2 ∨ i = 5) :
    0 ≤ quarterAuxCoeff656 i := by
  have h : ∀ j, j = 0 ∨ j = 2 ∨ j = 5 → 0 ≤ quarterAuxCoeffRat656 j := by decide +kernel
  unfold quarterAuxCoeff656
  exact_mod_cast h i hi

/-- For the seven specified coefficients, the three disjoint pairs and
the one unpaired coefficient bound the full reflected contribution. -/
theorem quarter_aux_reflection_three_pairs_656 (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4) {r : ℝ}
    (hr : 0 < r) (hs : ∀ i, (quarterAuxShift656 i : ℝ) ≤ 2 * Real.log r) :
    let F := fun i ↦ quarterAuxReflection656 α r (quarterAuxShift656 i : ℝ)
    (-quarterAuxPairLoss656 0 1 * F 1 - quarterAuxPairLoss656 2 3 * F 3 -
          quarterAuxPairLoss656 5 6 * F 6 +
        quarterAuxCoeff656 4 * F 4) ≤
      ∑ i, quarterAuxCoeff656 i * F i := by
  intro F
  have h (i j : Fin 7) (hij : i ≤ j) (hi : i = 0 ∨ i = 2 ∨ i = 5) :
    -quarterAuxPairLoss656 i j * F j ≤ quarterAuxCoeff656 i * F i + quarterAuxCoeff656 j * F j := by
    have hh :=
      quarter_aux_reflection_pair_656 α hα hr (shifts_order i j hij) (hs j) (c :=
        quarterAuxCoeff656 i) (d := quarterAuxCoeff656 j) (positive_coeff i hi)
    unfold quarterAuxPairLoss656
    dsimp only [F]
    linarith only [hh]
  have h₁ := h 0 1 (by decide) (Or.inl rfl)
  have h₂ := h 2 3 (by decide) (Or.inr (Or.inl rfl))
  have h₃ := h 5 6 (by decide) (Or.inr (Or.inr rfl))
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change
    _ ≤
      quarterAuxCoeff656 0 * F 0 +
        (quarterAuxCoeff656 1 * F 1 +
          (quarterAuxCoeff656 2 * F 2 +
            (quarterAuxCoeff656 3 * F 3 +
              (quarterAuxCoeff656 4 * F 4 +
                (quarterAuxCoeff656 5 * F 5 + quarterAuxCoeff656 6 * F 6)))))
  linarith only [h₁, h₂, h₃]

private def pairLossRat (i j : Fin 7) : ℚ :=
  -quarterAuxCoeffRat656 j -
    quarterAuxCoeffRat656 i *
      auxExpTaylor656 (-(11 / 10) * (quarterAuxShift656 j - quarterAuxShift656 i))

private theorem pair_loss_error (i j : Fin 7) :
    |quarterAuxPairLoss656 i j - (pairLossRat i j : ℝ)| ≤ 1 / 10 ^ 16 := by
  let x : ℚ := -(11 / 10) * (quarterAuxShift656 j - quarterAuxShift656 i)
  have hx :
    ∀ k l : Fin 7, |(-(11 / 10) * (quarterAuxShift656 l - quarterAuxShift656 k) : ℚ)| ≤ 10 := by
    decide +kernel
  have h := aux_exp_error_656 x (by exact_mod_cast hx i j)
  have hcoeff : ∀ k : Fin 7, |quarterAuxCoeffRat656 k| ≤ 1 := by decide +kernel
  have hc : |quarterAuxCoeff656 i| ≤ 1 := by
    unfold quarterAuxCoeff656
    exact_mod_cast hcoeff i
  have he :
    quarterAuxPairLoss656 i j - (pairLossRat i j : ℝ) =
      -(quarterAuxCoeff656 i * (Real.exp (x : ℝ) - (auxExpTaylor656 x : ℝ))) := by
    simp only [quarterAuxPairLoss656, pairLossRat, x, Rat.cast_sub, Rat.cast_mul, Rat.cast_neg,
      Rat.cast_div, Rat.cast_ofNat, aux_coeff_cast]
    ring
  rw [he, abs_neg, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) hc).trans h

private theorem pair_loss_box (i j : Fin 7) {l u : ℚ} (hl : l + 1 / 10 ^ 16 ≤ pairLossRat i j)
    (hu : pairLossRat i j ≤ u - 1 / 10 ^ 16) :
    quarterAuxPairLoss656 i j ∈ Set.Icc (l : ℝ) (u : ℝ) := by
  have he := abs_le.mp (pair_loss_error i j)
  have hlo := (Rat.cast_le (K := ℝ)).mpr hl
  have hhi := (Rat.cast_le (K := ℝ)).mpr hu
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_one] at hlo hhi
  exact ⟨by linarith only [he.1, hlo], by linarith only [he.2, hhi]⟩

/-- All three residual coefficients are positive. The third needs a
Taylor enclosure narrow enough to distinguish it from zero. -/
theorem quarter_aux_pair_loss_boxes_656 :
    quarterAuxPairLoss656 0 1 ∈ Set.Icc 0.08790103598 0.08790103601 ∧
      quarterAuxPairLoss656 2 3 ∈ Set.Icc 0.07976212830 0.07976212832 ∧
      quarterAuxPairLoss656 5 6 ∈ Set.Icc 0.00000000983 0.00000000985 := by
  have h₁ :=
    pair_loss_box 0 1 (l := 8790103598 / 10 ^ 11) (u := 8790103601 / 10 ^ 11) (by decide +kernel)
      (by decide +kernel)
  have h₂ :=
    pair_loss_box 2 3 (l := 7976212830 / 10 ^ 11) (u := 7976212832 / 10 ^ 11) (by decide +kernel)
      (by decide +kernel)
  have h₃ :=
    pair_loss_box 5 6 (l := 983 / 10 ^ 11) (u := 985 / 10 ^ 11) (by decide +kernel)
      (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at h₁ h₂ h₃ ⊢
  exact ⟨h₁, h₂, h₃⟩

private theorem aux_shift_in_range {r : ℝ} (hr : 322 ≤ r) (i : Fin 7) :
    (quarterAuxShift656 i : ℝ) ≤ 2 * Real.log r := by
  have h : ∀ j : Fin 7, quarterAuxShift656 j ≤ 64 / 10 := by decide +kernel
  have hc := (Rat.cast_le (K := ℝ)).mpr (h i)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc
  have he : Real.exp 5 ≤ r := by
    rw [show (5 : ℝ) = 1 * ((5 : ℕ) : ℝ) by norm_num only, Real.exp_mul_natCast]
    exact
      (pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _).trans
        ((by norm_num only : (3 : ℝ) ^ 5 ≤ 322).trans hr)
  have hl := (Real.le_log_iff_exp_le (by linarith only [hr] : 0 < r)).mpr he
  linarith only [hc, hl]

/-- A nonnegative trace produces a nonnegative shifted deficit on the
radius range used in the seven-frequency comparison. -/
theorem quarter_aux_reflection_nonneg_656 (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n) {r : ℝ} (hr : 322 ≤ r)
    (i : Fin 7) : 0 ≤ quarterAuxReflection656 α r (quarterAuxShift656 i : ℝ) := by
  have hp : 0 < r := by linarith only [hr]
  unfold quarterAuxReflection656
  apply mul_nonneg (by positivity)
  apply tsum_nonneg
  intro n
  exact
    mul_nonneg
      (mul_nonneg (hα n)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
      (pow_nonneg
        (add_nonneg (sub_nonneg.mpr (aux_shift_in_range hr i)) (Real.log_natCast_nonneg n)) _)

/-- With upper bounds at the four remaining displacements, the signed
reflection sum has the lower bound using the certified residual coefficients. -/
theorem quarter_aux_reflection_caps_656 (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4) {r : ℝ}
    (hr : 322 ≤ r) {B₁ B₃ B₄ B₆ : ℝ}
    (H₁ : quarterAuxReflection656 α r (quarterAuxShift656 1 : ℝ) ≤ B₁)
    (H₃ : quarterAuxReflection656 α r (quarterAuxShift656 3 : ℝ) ≤ B₃)
    (H₄ : quarterAuxReflection656 α r (quarterAuxShift656 4 : ℝ) ≤ B₄)
    (H₆ : quarterAuxReflection656 α r (quarterAuxShift656 6 : ℝ) ≤ B₆) :
    -0.08790103601 * B₁ - 0.07976212832 * B₃ - 0.012744582 * B₄ - 0.00000000985 * B₆ ≤
      ∑ i, quarterAuxCoeff656 i * quarterAuxReflection656 α r (quarterAuxShift656 i : ℝ) := by
  have h :=
    quarter_aux_reflection_three_pairs_656 α hα (by linarith only [hr] : 0 < r)
      (aux_shift_in_range hr)
  obtain ⟨h₁, h₃, h₆⟩ := quarter_aux_pair_loss_boxes_656
  have hn i := quarter_aux_reflection_nonneg_656 α (fun n ↦ (hα n).1) hr i
  have hc : quarterAuxCoeff656 4 = -0.012744582 := by
    have hq : quarterAuxCoeffRat656 4 = -12744582 / 1000000000 := by decide +kernel
    have he := congrArg (fun x : ℚ ↦ (x : ℝ)) hq
    simp only [aux_coeff_cast, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at he
    linarith only [he]
  have hB₁ := mul_le_mul h₁.2 H₁ (hn 1) (by norm_num only)
  have hB₃ := mul_le_mul h₃.2 H₃ (hn 3) (by norm_num only)
  have hB₆ := mul_le_mul h₆.2 H₆ (hn 6) (by norm_num only)
  have hB₄ := mul_le_mul_of_nonneg_left H₄ (by norm_num only : (0 : ℝ) ≤ 0.012744582)
  dsimp only at h
  rw [hc] at h
  linarith only [h, hB₁, hB₃, hB₄, hB₆]

end PseudoPrime.PrimeTestBounds.MillerRabin
