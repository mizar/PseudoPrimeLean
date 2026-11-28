/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassInversion
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassInversion
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassMellin
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Kernel
import PseudoPrime.LLS.PaperStatements.ReciprocalKernel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Balanced reciprocal components for the high Gaussian mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The balanced pole profile is nonnegative, and positive away from log frequency zero. -/
private theorem symmetric_profile_pos {a u : ℝ} (ha : 0 < a) (hu : 0 < |Real.log u|) (p q : ℕ)
    (hpq : 0 < p + q) : 0 < k131SymmetricProfile a p q u := by
  induction p, q using k131SymmetricProfile.induct with
  | case1 => exact (Nat.lt_irrefl 0 hpq).elim
  | case2 j =>
    simp only [k131SymmetricProfile]
    exact div_pos (mul_pos (Real.exp_pos _) (pow_pos hu _)) (Nat.cast_pos.mpr (Nat.factorial_pos _))
  | case3 j =>
    simp only [k131SymmetricProfile]
    exact div_pos (mul_pos (Real.exp_pos _) (pow_pos hu _)) (Nat.cast_pos.mpr (Nat.factorial_pos _))
  | case4 p q hp hq =>
    simp only [k131SymmetricProfile]
    exact
      div_pos
        (add_pos (hp (Nat.add_pos_right _ (Nat.succ_pos q)))
          (hq (Nat.add_pos_left (Nat.succ_pos p) _)))
        (mul_pos (by norm_num only) ha)

/-- Nonnegativity of a balanced pole profile, including at the central argument. -/
private theorem symmetric_profile_nonneg {a : ℝ} (ha : 0 < a) (p q : ℕ) (u : ℝ) :
    0 ≤ k131SymmetricProfile a p q u := by
  induction p, q using k131SymmetricProfile.induct with
  | case1 => simp only [k131SymmetricProfile, le_refl]
  | case2 j =>
    simp only [k131SymmetricProfile]
    exact
      div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (abs_nonneg _) _)) (Nat.cast_nonneg _)
  | case3 j =>
    simp only [k131SymmetricProfile]
    exact
      div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (abs_nonneg _) _)) (Nat.cast_nonneg _)
  | case4 p q hp hq =>
    simp only [k131SymmetricProfile]
    exact div_nonneg (add_nonneg hp hq) (mul_pos (by norm_num only) ha).le

/-- A reciprocal power with two poles equally spaced from the imaginary axis. -/
private noncomputable def balancedPoleFn (a : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  1 / ((a : ℂ) ^ 2 - s ^ 2) ^ (n + 1)

/-- For pole distance at least two and real part bounded by one,
the quadratic denominator dominates one plus the squared norm. -/
private theorem balanced_den_lower {a : ℝ} (ha : 2 ≤ a) {s : ℂ} (hs : |s.re| ≤ 1) :
    1 + ‖s‖ ^ 2 ≤ ‖(a : ℂ) ^ 2 - s ^ 2‖ := by
  have h := Complex.re_le_norm ((a : ℂ) ^ 2 - s ^ 2)
  simp only [pow_two, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at h
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two]
  have hr := pow_le_pow_left₀ (abs_nonneg s.re) hs 2
  rw [sq_abs, one_pow, pow_two] at hr
  have hA := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 2) ha 2
  nlinarith only [h, hr, hA]

/-- Balanced denominator powers do not vanish on the contour strip. -/
private theorem balanced_den_ne {a : ℝ} (ha : 2 ≤ a) {s : ℂ} (hs : |s.re| ≤ 1) :
    (a : ℂ) ^ 2 - s ^ 2 ≠ 0 :=
  norm_pos_iff.mp
    ((add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg ‖s‖)).trans_le (balanced_den_lower ha hs))

/-- The balanced pole function is differentiable everywhere on the contour strip. -/
private theorem balanced_diff {a : ℝ} (ha : 2 ≤ a) (n : ℕ) {s : ℂ} (hs : |s.re| ≤ 1) :
    DifferentiableAt ℂ (balancedPoleFn a n) s := by
  unfold balancedPoleFn
  exact
    (differentiableAt_const _).div
      (((differentiableAt_id (𝕜 := ℂ) (x := s)).pow 2).const_sub _ |>.pow _)
      (pow_ne_zero _ (balanced_den_ne ha hs))

/-- Quadratic decay is uniform in the order as long as the contour remains in the strip. -/
private theorem balanced_decay {a : ℝ} (ha : 2 ≤ a) (n : ℕ) {s : ℂ} (hs : |s.re| ≤ 1) :
    ‖balancedPoleFn a n s‖ ≤ 1 / (1 + ‖s‖ ^ 2) := by
  have h := balanced_den_lower ha hs
  have h1 : 1 ≤ ‖(a : ℂ) ^ 2 - s ^ 2‖ := (le_add_of_nonneg_right (sq_nonneg _)).trans h
  unfold balancedPoleFn
  rw [norm_div, norm_one, norm_pow]
  exact
    div_le_div_of_nonneg_left zero_le_one (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _))
      (h.trans (by simpa only [pow_one] using pow_le_pow_right₀ h1 (Nat.succ_pos n)))

/-- The analytic pole component is the Mellin transform of its half-normalized profile. -/
private theorem balanced_hasMellin {a : ℝ} {s : ℂ} (hl : -a < s.re) (hr : s.re < a) (n : ℕ) :
    HasMellin (fun u ↦ ((1 / 2 * k131SymmetricProfile a (n + 1) (n + 1) u : ℝ) : ℂ)) s
      (balancedPoleFn a n s) := by
  have h := balanced_mellin hl hr (n + 1) (Nat.succ_pos n) 1
  have he : ((a : ℂ) + s) * ((a : ℂ) - s) = (a : ℂ) ^ 2 - s ^ 2 := by ring
  simpa only [balancedPoleFn, ← mul_pow, he, Complex.ofReal_one] using h

/-- On a line within the analytic strip, balanced powers have an integrable vertical trace. -/
private theorem balanced_vertical {a c : ℝ} (hl : -a < c) (hr : c < a) (n : ℕ) :
    Complex.VerticalIntegrable (balancedPoleFn a n) c := by
  have hd : 0 < a + c := by linarith only [hl]
  have he : 0 < a - c := sub_pos.mpr hr
  apply (integrable_vertical_pair hd he n).congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [balancedPoleFn]
  rw [← mul_pow]
  congr 2
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg]
  ring

/-- Mellin inversion gives the same real nonnegative profile throughout the open strip. -/
private theorem balanced_inversion {a c u : ℝ} (hl : -a < c) (hr : c < a) (hu : 0 < u) (n : ℕ) :
    Analysis.inverseMellin (balancedPoleFn a n) c u =
      ((1 / 2 * k131SymmetricProfile a (n + 1) (n + 1) u : ℝ) : ℂ) := by
  let f := fun v : ℝ ↦ ((1 / 2 * k131SymmetricProfile a (n + 1) (n + 1) v : ℝ) : ℂ)
  have hre (t : ℝ) : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      mul_zero, zero_mul, sub_zero, add_zero]
  have h (t : ℝ) :
    HasMellin f ((c : ℂ) + (t : ℂ) * Complex.I)
      (balancedPoleFn a n ((c : ℂ) + (t : ℂ) * Complex.I)) :=
    balanced_hasMellin
      (by
        rw [hre]; exact hl)
      (by
        rw [hre]; exact hr)
      n
  have hi := (balanced_vertical hl hr n).congr (Filter.Eventually.of_forall fun t ↦ (h t).2.symm)
  have h0 : MellinConvergent f (c : ℂ) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using (h 0).1
  have hc : ContinuousAt f u :=
    Complex.continuous_ofReal.continuousAt.comp ((k131_symmetric_cont hu _ _ _).const_mul _)
  change Analysis.inverseMellin (balancedPoleFn a n) c u = f u
  rw [Analysis.inverseMellin_eq_mellinInv, ← mellinInv_mellin_eq c f hu h0 hi hc]
  unfold mellinInv
  congr 1
  exact
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun t ↦
        congrArg (fun z : ℂ ↦ (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) • z) (h t).2.symm)

/-- A balanced reciprocal power at pole distance at least two is an admissible
Mellin kernel on the standard contour strip of width one eighth. -/
public noncomputable def balancedPoleKernel (a : ℝ) (ha : 2 ≤ a) (n : ℕ) :
    LLS.PaperStatements.MellinKernel where
  function := balancedPoleFn a n
  delta := 1 / 8
  delta_pos := by norm_num only
  region := {s | s.re ∈ Set.Ioo (-(3 / 4 : ℝ)) (3 / 4)}
  region_open := isOpen_Ioo.preimage Complex.continuous_re
  strip_subset := by
    intro s hs
    exact ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
  holomorphic := by
    intro s hs
    exact
      (balanced_diff ha n
          (abs_le.mpr
            ⟨by linarith only [hs.1.1], by linarith only [hs.1.2]⟩)).differentiableWithinAt
  regularized := fun s ↦ (s + 1 / 2) * balancedPoleFn a n s
  regularized_holomorphic := by
    intro s hs
    exact
      (((differentiableAt_id (𝕜 := ℂ) (x := s)).add_const _).mul
          (balanced_diff ha n
            (abs_le.mpr ⟨by linarith only [hs.1], by linarith only [hs.2]⟩))).differentiableWithinAt
  regularized_eq := fun _ _ _ ↦ rfl
  decay := by
    intro η _
    exact
      ⟨1, zero_lt_one, fun s hs _ ↦
        balanced_decay ha n (abs_le.mpr ⟨by linarith only [hs.1], by linarith only [hs.2]⟩)⟩
  mellin_integrable := by
    intro c u hl hr hu
    apply LLS.PaperStatements.integrable_inverseMellin_of_line hu
    simpa only [Complex.VerticalIntegrable, mul_comm Complex.I] using
      (balanced_vertical (a := a) (c := c) (by linarith only [ha, hl]) (by linarith only [ha, hr])
        n)
  mellin_eq := by
    intro c u hl hr hu
    rw [balanced_inversion (by linarith only [ha, hl]) (by linarith only [ha, hr]) hu,
      balanced_inversion (by linarith only [ha]) (by linarith only [ha]) hu]
  mellin_nonneg := by
    intro u hu
    rw [balanced_inversion (by linarith only [ha]) (by linarith only [ha]) hu, Complex.ofReal_re]
    exact mul_nonneg (by norm_num only) (symmetric_profile_nonneg (by linarith only [ha]) _ _ _)
  mellin_nonzero := by
    refine ⟨Real.exp 1, Real.exp_pos _, ?_⟩
    rw [balanced_inversion (by linarith only [ha]) (by linarith only [ha]) (Real.exp_pos _),
      Complex.ofReal_re]
    exact
      (mul_pos (by norm_num only)
          (symmetric_profile_pos (by linarith only [ha])
            (by
              rw [Real.log_exp, abs_one]; exact zero_lt_one)
            _ _ (Nat.add_pos_left (Nat.succ_pos n) _))).ne'
  mellin_real := by
    intro u hu
    rw [balanced_inversion (by linarith only [ha]) (by linarith only [ha]) hu, Complex.ofReal_im]

/-- The admissible kernel has the stated balanced reciprocal function. -/
public theorem balanced_pole_function (a : ℝ) (ha : 2 ≤ a) (n : ℕ) (s : ℂ) :
    (balancedPoleKernel a ha n).function s = 1 / ((a : ℂ) ^ 2 - s ^ 2) ^ (n + 1) := by rfl

/-- The balanced component uses the fixed contour width. -/
public theorem balanced_pole_delta (a : ℝ) (ha : 2 ≤ a) (n : ℕ) :
    (balancedPoleKernel a ha n).delta = 1 / 8 := by rfl

/-- Both high Gaussian pole locations are in the admissible balanced-kernel range. -/
public theorem high_gaussian_pole_ge_two (K : HighGaussianKernel) : 2 ≤ (K.pole : ℝ) := by
  cases K <;> norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]

/-- The rational extension is a signed sum of admissible balanced Mellin kernels. -/
public theorem high_gaussian_balanced_sum (K : HighGaussianKernel) {z : ℂ}
    (hl : -(K.pole : ℝ) < z.re) (hr : z.re < (K.pole : ℝ)) :
    K.massExtension z =
      ∑ j ∈ Finset.range (K.degree + 1),
        ((K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)) *
          (balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)).function
            z := by
  rw [high_gaussian_mass_extension_sum K hl hr]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hm : K.degree + 1 - j + 1 = K.degree + 2 - j :=
    (Nat.sub_add_comm (hj'.trans (Nat.le_succ K.degree))).symm
  have hprod : ((K.pole : ℂ) + z) * ((K.pole : ℂ) - z) = (K.pole : ℂ) ^ 2 - z ^ 2 := by ring
  rw [balanced_pole_function, hm, ← mul_pow, hprod, mul_one_div]
  simp only [Complex.ofReal_ratCast]

/-- The inverse of an admissible balanced component is its half-normalized symmetric profile. -/
public theorem balanced_pole_inverse {a c u : ℝ} (ha : 2 ≤ a) (n : ℕ) (hl : -a < c) (hr : c < a)
    (hu : 0 < u) :
    Analysis.inverseMellin (balancedPoleKernel a ha n).function c u =
      ((1 / 2 * k131SymmetricProfile a (n + 1) (n + 1) u : ℝ) : ℂ) := by
  exact balanced_inversion hl hr hu n

end PseudoPrime.PrimeTestBounds.MillerRabin
