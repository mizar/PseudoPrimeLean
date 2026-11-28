/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredVariation
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredVariation
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadNumeric
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalLowZeros
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import Mathlib.Tactic.Ring

/-! # Rational error bounds for the centered low-zero brackets -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A single weighted coefficient sum majorizes the derivative moment above height 14. -/
private noncomputable def centeredVariationMass (K : HighGaussianKernel) : ℝ :=
  let P := highCenteredProfile K
  ∑ j ∈ Finset.range (P.natDegree + 1),
    |principalMomentCoeff P 5 j| * ((j.factorial : ℝ) * ((j + 2 : ℕ) : ℝ) / 14 ^ j)

/-- Factoring out the inverse cube leaves a common weighted moment for all brackets. -/
private theorem centered_variation_mass_le (K : HighGaussianKernel) {l : ℝ} (hl : 14 ≤ l) :
    let P := highCenteredProfile K
    (∑ j ∈ Finset.range (P.natDegree + 1),
        |principalMomentCoeff P 5 j * (j.factorial : ℝ)| * ((j + 2 : ℕ) : ℝ) / l ^ (j + 3)) ≤
      centeredVariationMass K / l ^ 3 := by
  intro P
  unfold centeredVariationMass
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j.factorial), pow_add, ← div_div, ←
    mul_div_assoc, mul_assoc]
  apply div_le_div_of_nonneg_right _ (pow_nonneg ((by norm_num only : (0 : ℝ) ≤ 14).trans hl) _)
  exact
    div_le_div_of_nonneg_left
      (mul_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (pow_pos (by norm_num only) _) (pow_le_pow_left₀ (by norm_num only) hl _)

/-- The rational moment weights match the real weights exactly. -/
private def centeredVariationWeight (j : ℕ) : ℚ :=
  (j.factorial : ℚ) * ((j + 2 : ℕ) : ℚ) / 14 ^ j

/-- The shared rational coefficient evaluator computes the derivative moment. -/
private theorem centered_variation_mass_eq (K : HighGaussianKernel) :
    centeredVariationMass K = (centeredWeightFast K centeredVariationWeight : ℝ) := by
  have hd : (highCenteredProfile K).natDegree ≤ 2 * K.degree + 3 := by
    rw [← high_centered_rat_map]
    exact Polynomial.natDegree_map_le.trans (high_centered_rat_degree K)
  unfold centeredVariationMass
  rw [centered_mass_pad _ (fun j ↦ (j.factorial : ℝ) * ((j + 2 : ℕ) : ℝ) / 14 ^ j) hd,
    centered_weight_fast_eq]
  simp only [centeredVariationWeight, Rat.cast_sum, Rat.cast_abs, Rat.cast_mul, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat, ← high_centered_rat_map K, Polynomial.coeff_map,
    Rat.coe_castHom]

/-- The reciprocal-power sums over the certified left endpoints. -/
private def centeredZeroPowerSum (n : ℕ) : ℚ :=
  ∑ i : Fin 29, (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i ^ n)⁻¹

/-- The rational total error uses a single centered coefficient calculation. -/
public def highCenteredErrorRat (K : HighGaussianKernel) : ℚ :=
  let (M₀, M₁) := highCompactRat K
  (K.normalization *
        (5 * M₀ ^ 2 * centeredZeroPowerSum 4 + 4 * M₀ ^ 2 * centeredZeroPowerSum 5 +
          4 * K.pole * M₀ * M₁ * centeredZeroPowerSum 6) +
      4 * headExpUpper (K.pole * 5) 36 * centeredWeightFast K centeredVariationWeight *
        centeredZeroPowerSum 3) /
    200

/-- Every left endpoint of a certified positive bracket is at least 14. -/
private theorem centered_zero_left_ge (i : Fin 29) :
    (14 : ℚ) ≤ AnalyticNumberTheory.RiemannZeta.lowZero100Lower i := by
  exact
    (by decide +kernel :
        ∀ j : Fin 29, (14 : ℚ) ≤ AnalyticNumberTheory.RiemannZeta.lowZero100Lower j)
      i

/-- Factoring the common moment bound across the brackets yields the rational budget. -/
public theorem high_centered_error_rat_le (K : HighGaussianKernel) :
    (∑ i, highCenteredBracketError K i) ≤ (highCenteredErrorRat K : ℝ) := by
  let l := fun i : Fin 29 ↦ (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i : ℝ)
  let a := (K.pole : ℝ)
  let M₀ := highCompactMass K
  let M₁ := highCompactSlope K
  let E := (headExpUpper (K.pole * 5) 36 : ℝ)
  let M := centeredVariationMass K
  have ha : 0 < a := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have he : Real.exp (-(5 * a)) ≤ E := by
    have h :=
      head_exp_upper_sound (mul_nonneg (Rat.cast_pos.mp ha).le (by norm_num only : (0 : ℚ) ≤ 5)) 36
    simpa only [E, a, Rat.cast_mul, Rat.cast_ofNat, mul_comm (5 : ℝ)] using h
  have hle (i : Fin 29) :
    highCenteredBracketError K i ≤
      ((K.normalization : ℝ) *
            (5 * M₀ ^ 2 / l i ^ 4 + 4 * M₀ ^ 2 / l i ^ 5 + 4 * a * M₀ * M₁ / l i ^ 6) +
          4 * E * (M / l i ^ 3)) /
        200 := by
    have hl : 14 ≤ l i := by
      simpa only [l, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (centered_zero_left_ge i)
    have h := centered_variation_mass_le K hl
    unfold highCenteredBracketError highCenteredDerivCap
    refine div_le_div_of_nonneg_right (add_le_add le_rfl ?_) (by norm_num only : (0 : ℝ) ≤ 200)
    exact
      mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num only)) h
        (Finset.sum_nonneg
          (fun _ _ ↦
            div_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
              (pow_nonneg ((by norm_num only : (0 : ℝ) ≤ 14).trans hl) _)))
        (mul_nonneg (by norm_num only) ((Real.exp_pos _).le.trans he))
  refine (Finset.sum_le_sum (fun i _ ↦ hle i)).trans_eq ?_
  simp only [highCenteredErrorRat, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat, (high_compact_rat_eq K).1, (high_compact_rat_eq K).2,
    ← centered_variation_mass_eq, centeredZeroPowerSum, Rat.cast_sum, Rat.cast_inv,
    ← Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply congrArg (· / 200)
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [a, M₀, M₁, l, E, M]
  ring

/-- Upper bounds for the 29 positive-bracket errors in millionths. -/
@[expose]
public def highCenteredErrorTicks : HighGaussianKernel → ℕ
  | .k186 => 65
  | .k196 => 122

/-- The rational certificate fits the kernel-specific error budget. -/
private theorem high_centered_error_check (K : HighGaussianKernel) :
    highCenteredErrorRat K ≤ (highCenteredErrorTicks K : ℚ) / 1000000 := by
  cases K <;> decide +kernel

/-- The sum of the 29 midpoint errors uses the certified scalar budget. -/
public theorem high_centered_error_sum_le (K : HighGaussianKernel) :
    (∑ i, highCenteredBracketError K i) ≤ (highCenteredErrorTicks K : ℝ) / 1000000 := by
  have h : (highCenteredErrorRat K : ℝ) ≤ ((((highCenteredErrorTicks K : ℚ) / 1000000) : ℚ) : ℝ) :=
    Rat.cast_le.mpr (high_centered_error_check K)
  exact
    (high_centered_error_rat_le K).trans
      (by simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h)

/-- A family in the 29 brackets is bounded by the midpoint norms and the checked error budget. -/
public theorem high_centered_low_budget_le (K : HighGaussianKernel) (g : Fin 29 → ℝ)
    (hlo : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hhi : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    (∑ i, ‖highPrincipalMultiplier K (g i)‖) ≤
      (∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
        (highCenteredErrorTicks K : ℝ) / 1000000 := by
  exact
    (high_centered_low_sum_le K g hlo hhi).trans (add_le_add le_rfl (high_centered_error_sum_le K))

end PseudoPrime.PrimeTestBounds.MillerRabin
