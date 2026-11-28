/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ShiftedPoleProfile
public import PseudoPrime.LLS.PaperStatements.RationalPoleKernel
import all PseudoPrime.LLS.PaperStatements.RationalPoleKernel

/-! # Admissible shifted poles of arbitrary order -/

namespace PseudoPrime.LLS.PaperStatements

private theorem shifted_power_exp_eq (b : ℝ) : (2 : ℂ) * ((b / 2 : ℝ) : ℂ) = (b : ℂ) := by
  rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
  congr 1
  ring

private theorem shifted_power_integrable {n : ℕ} (hn : 1 ≤ n) {ρ σ : ℝ} (hσ : 0 < σ + ρ) (b : ℝ) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        Complex.exp ((b : ℂ) * ((σ : ℂ) + Complex.I * t)) /
          (((σ : ℂ) + Complex.I * t) + ρ) ^ (n + 1)) := by
  have hc : Continuous (fun t : ℝ ↦ Complex.exp ((b : ℂ) * ((σ : ℂ) + Complex.I * t))) :=
    Complex.continuous_exp.comp
      (continuous_const.mul (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)))
  have he (t : ℝ) :
    ‖Complex.exp ((b : ℂ) * ((σ : ℂ) + Complex.I * t))‖ ≤ Real.exp (2 * (b / 2) * σ) := by
    rw [← shifted_power_exp_eq b, norm_exp_rationalPole_line]
  have hi :=
    (integrable_shifted_reciprocal_power hn hσ).mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall he)
  exact
    hi.congr
      (Filter.Eventually.of_forall
        (fun t ↦ by
          dsimp only
          rw [one_div_mul_eq_div]))

private theorem shifted_power_decay {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ} (hρ : 1 / 2 < ρ) (b : ℝ) {η : ℝ}
    (hη : 0 < η) {z : ℂ} (hz : z ∈ reciprocalGapRegion (ρ - 1 / 2)) (hd : η ≤ ‖z + 1 / 2‖) :
    ‖Complex.exp ((b : ℂ) * z) / (z + ρ) ^ (n + 1)‖ ≤
      (Real.exp ((3 / 2 : ℝ) * |b / 2|) * 3 * (1 / ((ρ - 1 / 2) / 2)) ^ (n - 1) *
          (3 + 6 / (η * (ρ - 1 / 2)))) /
        (1 + ‖z‖ ^ 2) := by
  let h := ρ - 1 / 2
  have hh : 0 < h := sub_pos.mpr hρ
  have he : (1 / 2 : ℝ) + h = ρ := by
    dsimp only [h]; ring
  have hp :=
    reciprocal_power_le_pair (hη.trans_le hd) (by linarith only [hh] : 0 < h / 2)
      (reciprocalGap_second_norm_lower hz) (first_norm_le_three_second hh hz) (n - 1)
  rw [show n - 1 + 2 = n + 1 from by
      change (n - 1 + 1) + 1 = n + 1
      rw [Nat.sub_add_cancel hn]] at hp
  have hre : |z.re| ≤ 3 / 4 :=
    abs_le.mpr ⟨by linarith only [hz.1, min_le_right (h / 2) (1 / 4 : ℝ)], hz.2.le⟩
  have hex := norm_exp_rationalPole_strip (b / 2) hre
  rw [shifted_power_exp_eq] at hex
  have hgap := reciprocalGap_strip_bound hh hη hz hd
  rw [Analysis.reciprocalGapFunction, Analysis.twoPoleFunction, norm_div, norm_one,
    norm_mul] at hgap
  rw [norm_div, norm_pow]
  conv_lhs => rw [← he]
  calc
    _ ≤ Real.exp ((3 / 2 : ℝ) * |b / 2|) * (1 / ‖z + ((1 / 2 + h : ℝ) : ℂ)‖ ^ (n + 1)) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right hex (pow_nonneg (norm_nonneg _) _)
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hp (Real.exp_pos ((3 / 2 : ℝ) * |b / 2|)).le
      have hr :=
        mul_le_mul_of_nonneg_left hgap
          (show 0 ≤ Real.exp ((3 / 2 : ℝ) * |b / 2|) * 3 * (1 / (h / 2)) ^ (n - 1) from
            mul_nonneg (mul_nonneg (Real.exp_pos _).le (by norm_num only))
              (pow_nonneg (div_nonneg zero_le_one (by linarith only [hh])) _))
      dsimp only [h] at *
      simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hr
      rw [mul_div_assoc _ _ (1 + ‖z‖ ^ 2)]
      exact hm.trans (by simpa only [mul_div_assoc, mul_assoc] using hr)

/-- The shifted pole of order `n + 1` at `-ρ` with exponential shift
`b` is an admissible Mellin kernel when `1 ≤ n` and `1/2 < ρ`.
Inversion provides the real nonnegative profile and the gap strip supplies decay. -/
public noncomputable def shiftedPoleKernel (n : ℕ) (ρ b : ℝ) (hn : 1 ≤ n) (hρ : 1 / 2 < ρ) :
    MellinKernel where
  function z := Complex.exp ((b : ℂ) * z) / (z + ρ) ^ (n + 1)
  delta := (reciprocalGapMellinKernel _ (sub_pos.mpr hρ)).delta
  delta_pos := (reciprocalGapMellinKernel _ (sub_pos.mpr hρ)).delta_pos
  region := reciprocalGapRegion (ρ - 1 / 2)
  region_open := (reciprocalGapMellinKernel _ (sub_pos.mpr hρ)).region_open
  strip_subset := (reciprocalGapMellinKernel _ (sub_pos.mpr hρ)).strip_subset
  holomorphic := by
    intro z hz
    have hd := reciprocalGap_second_shift_ne_zero (sub_pos.mpr hρ) hz.1
    rw [show (1 / 2 : ℝ) + (ρ - 1 / 2) = ρ by ring] at hd
    exact
      ((Complex.differentiable_exp.differentiableAt.comp z
              ((differentiableAt_id (𝕜 := ℂ) (x := z)).const_mul (b : ℂ))).div
          (((differentiableAt_id (𝕜 := ℂ) (x := z)).add_const _).pow (n + 1))
          (pow_ne_zero _ hd)).differentiableWithinAt
  regularized z := (z + 1 / 2) * (Complex.exp ((b : ℂ) * z) / (z + ρ) ^ (n + 1))
  regularized_holomorphic := by
    intro z hz
    have hd := reciprocalGap_second_shift_ne_zero (sub_pos.mpr hρ) hz
    rw [show (1 / 2 : ℝ) + (ρ - 1 / 2) = ρ by ring] at hd
    exact
      (((differentiableAt_id (𝕜 := ℂ) (x := z)).add_const _).mul
          ((Complex.differentiable_exp.differentiableAt.comp z
                ((differentiableAt_id (𝕜 := ℂ) (x := z)).const_mul (b : ℂ))).div
            (((differentiableAt_id (𝕜 := ℂ) (x := z)).add_const _).pow (n + 1))
            (pow_ne_zero _ hd))).differentiableWithinAt
  regularized_eq := fun _ _ _ ↦ rfl
  decay := by
    intro η hη
    refine ⟨_, ?_, fun z hz hd ↦ shifted_power_decay hn hρ b hη hz hd⟩
    have hh : 0 < ρ - 1 / 2 := sub_pos.mpr hρ
    exact
      mul_pos
        (mul_pos (mul_pos (Real.exp_pos _) (by norm_num only))
          (pow_pos (div_pos zero_lt_one (by linarith only [hh])) _))
        (add_pos_of_pos_of_nonneg (by norm_num only)
          (div_nonneg (by norm_num only) (mul_pos hη hh).le))
  mellin_integrable := by
    intro σ u hσ _ hu
    exact
      integrable_inverseMellin_of_line (c := σ) (F := fun z ↦
        Complex.exp ((b : ℂ) * z) / (z + ρ) ^ (n + 1)) hu
        (shifted_power_integrable hn (ρ := ρ) (σ := σ) (by linarith only [hσ, hρ]) b)
  mellin_eq := by
    intro σ u hσ _ hu
    rw [Analysis.inverseMellin_shiftedPole hn (ρ := ρ) (σ := σ) (by linarith only [hσ, hρ]) hu b,
      Analysis.inverseMellin_shiftedPole hn (ρ := ρ) (σ := 0) (by linarith only [hρ]) hu b]
  mellin_nonneg := by
    intro u hu
    rw [Analysis.inverseMellin_shiftedPole hn (ρ := ρ) (σ := 0) (by linarith only [hρ]) hu b,
      Complex.ofReal_re]
    exact Analysis.shiftedPoleProfile_nonneg n ρ b hu
  mellin_nonzero := by
    have hu := Real.exp_pos (b - 1)
    refine ⟨_, hu, ?_⟩
    rw [Analysis.inverseMellin_shiftedPole hn (ρ := ρ) (σ := 0) (by linarith only [hρ]) hu b,
      Complex.ofReal_re,
      Analysis.shiftedPoleProfile_eq n ρ hu (Real.exp_le_exp.mpr (by linarith only)), Real.log_exp]
    exact
      (div_pos
          (mul_pos (Real.rpow_pos_of_pos (mul_pos hu (Real.exp_pos _)) _)
            (pow_pos (by linarith only : 0 < b - (b - 1)) _))
          (Nat.cast_pos.mpr (Nat.factorial_pos _))).ne'
  mellin_real := by
    intro u hu
    rw [Analysis.inverseMellin_shiftedPole hn (ρ := ρ) (σ := 0) (by linarith only [hρ]) hu b,
      Complex.ofReal_im]

/-- The transform of an admissible shifted pole is its real profile on
positive arguments, so signed sums can use this identity componentwise. -/
public theorem shiftedPoleKernel_transform (n : ℕ) (ρ b : ℝ) (hn : 1 ≤ n) (hρ : 1 / 2 < ρ) {u : ℝ}
    (hu : 0 < u) :
    (shiftedPoleKernel n ρ b hn hρ).transform u = (Analysis.shiftedPoleProfile n ρ b u : ℂ) := by
  exact Analysis.inverseMellin_shiftedPole hn (ρ := ρ) (σ := 0) (by linarith only [hρ]) hu b

end PseudoPrime.LLS.PaperStatements
