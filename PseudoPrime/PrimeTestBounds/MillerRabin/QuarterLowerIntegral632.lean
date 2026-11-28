/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMain570
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMain570

/-! # The omitted lower integral in the quarter-square comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem small_weight_decay632 {X t : ℝ} (hX : 0 < X) (ht : 0 < t) (hu : t ≤ 1)
    (hz : 14 ≤ 14 / 5 + Real.log X) :
    quarterWeight570 X t ≤ quarterWeight570 X 1 * t ^ (4 / 25 : ℝ) := by
  let z := 14 / 5 + Real.log X
  let y := -Real.log t
  have hz0 : 0 < z := by
    dsimp only [z]; linarith only [hz]
  have hy : 0 ≤ y := neg_nonneg.mpr (Real.log_nonpos ht.le hu)
  have hlog := Real.add_one_le_exp (y / z)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ y / z + 1) hlog 5
  rw [← Real.exp_natCast_mul, Nat.cast_ofNat] at hp
  have h₁ : (z + y) ^ 5 ≤ z ^ 5 * Real.exp ((9 / 25) * y) := by
    have hb : 5 / z ≤ (9 / 25 : ℝ) :=
      (div_le_iff₀ hz0).mpr
        (by
          dsimp only [z]; linarith only [hz])
    have he : Real.exp (5 * (y / z)) ≤ Real.exp (9 / 25 * y) := by
      apply Real.exp_le_exp.mpr
      rw [show (5 : ℝ) * (y / z) = (5 / z) * y by ring]
      exact mul_le_mul_of_nonneg_right hb hy
    have h := mul_le_mul_of_nonneg_left (hp.trans he) (pow_nonneg hz0.le 5)
    calc
      _ = z ^ 5 * (y / z + 1) ^ 5 := by
        rw [← mul_pow]; congr 1; field_simp [hz0.ne']; ring
      _ ≤ _ := h
  have hlt : Real.log (t / X) = -y - Real.log X := by
    rw [Real.log_div ht.ne' hX.ne']
    dsimp only [y]; rw [neg_neg]
  have hlf : Real.log (1 / X) = -Real.log X := by rw [one_div, Real.log_inv]
  unfold quarterWeight570
  rw [hlt, hlf, Real.sqrt_one, div_one, one_mul, Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht,
    Real.rpow_def_of_pos ht]
  have hE :
    Real.exp (-((2 * (7 / 5) - (-y - Real.log X)) / (2 * (25 / 51)))) =
      Real.exp (-(51 / 50) * z) * Real.exp (-(51 / 50) * y) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [z]
    ring
  have hZ : (2 * (7 / 5) - -Real.log X) / (2 * (25 / 51)) = (51 / 50) * z := by
    dsimp only [z]; ring
  have hY : (2 * (7 / 5) - (-y - Real.log X)) / (2 * (25 / 51)) = (51 / 50) * (z + y) := by
    dsimp only [z]; ring
  have hscale :
    (1 / Real.exp (Real.log t * (1 / 2))) * Real.exp (-(51 / 50) * y) * Real.exp ((9 / 25) * y) =
      Real.exp (Real.log t * (4 / 25)) := by
    rw [one_div, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [y]
    ring
  dsimp only
  rw [hE, hZ, hY, mul_pow, mul_pow]
  have hh :=
    mul_le_mul_of_nonneg_left h₁
      (show
        0 ≤
          (1 / Real.exp (Real.log t * (1 / 2))) * ((51 / 50 : ℝ) ^ 5 / 120) *
            Real.exp (-(51 / 50) * z) *
            Real.exp (-(51 / 50) * y)
        by positivity)
  dsimp only [z] at hh hscale ⊢
  simp only [neg_mul] at hh hscale ⊢
  linear_combination
    hh +
      (((51 / 50 : ℝ) ^ 5 / 120) * Real.exp (-((51 / 50) * (14 / 5 + Real.log X))) *
          (14 / 5 + Real.log X) ^ 5) *
        hscale

/-- The omitted lower integral is at most 25/29 of the weight at one
when the logarithmic cutoff coordinate is at least fourteen. -/
theorem quarter_missing_mass_ratio632 {X : ℝ} (hX : 1 ≤ X) (hz : 14 ≤ 14 / 5 + Real.log X) :
    Real.sqrt X * (∫ u in (0 : ℝ)..1 / X, (quarterKernel570.transform u).re / Real.sqrt u) ≤
      25 / 29 * quarterWeight570 X 1 := by
  have hx := zero_lt_one.trans_le hX
  let K := fun u : ℝ ↦ (quarterKernel570.transform u).re / Real.sqrt u
  let C := Real.sqrt X * quarterWeight570 X 1 * X ^ (4 / 25 : ℝ)
  have hi :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (one_div_pos.mpr hx).le).mpr
      ((LLS.PaperStatements.MellinKernel.integrableOn_weight_Ioi quarterKernel570).mono_set
        (fun _ h ↦ h.1))
  have hJ : IntervalIntegrable (fun u : ℝ ↦ C * u ^ (4 / 25 : ℝ)) MeasureTheory.volume 0 (1 / X) :=
    (Real.continuous_rpow_const (by norm_num only : (0 : ℝ) ≤ 4 / 25) |>.const_mul
        C) |>.intervalIntegrable
      _ _
  have h :=
    intervalIntegral.integral_mono_on_of_le_Ioo (one_div_pos.mpr hx).le hi hJ
      (by
        intro u hu
        have ht := mul_pos hu.1 hx
        have hu1 := ((lt_div_iff₀ hx).mp hu.2).le
        have hb : u * X ≤ X * Real.exp (14 / 5) :=
          hu1.trans (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only)) |> hX.trans)
        have hw := scale_weight hx ht hb
        rw [mul_div_cancel_right₀ _ hx.ne'] at hw
        have hd := small_weight_decay632 hx ht hu1 hz
        rw [hw, Real.mul_rpow hu.1.le hx.le, one_div, inv_mul_eq_div] at hd
        change K u ≤ C * u ^ (4 / 25 : ℝ)
        unfold C K
        have hh := (div_le_iff₀ (Real.sqrt_pos.mpr hx)).mp hd
        exact hh.trans_eq (by ring))
  have hp : X ^ (4 / 25 : ℝ) * (1 / X) ^ (29 / 25 : ℝ) = 1 / X := by
    rw [one_div, Real.inv_rpow hx.le, ← div_eq_mul_inv, ← Real.rpow_sub hx]
    rw [show (4 / 25 - 29 / 25 : ℝ) = -1 by norm_num only, Real.rpow_neg hx.le, Real.rpow_one]
  have h' := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg X)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num only)),
    show (4 / 25 + 1 : ℝ) = 29 / 25 by norm_num only, Real.zero_rpow (by norm_num only),
    sub_zero] at h'
  change Real.sqrt X * (∫ u in (0 : ℝ)..1 / X, K u) ≤ _
  refine h'.trans_eq ?_
  unfold C
  have hs := Real.sq_sqrt hx.le
  calc
    _ =
        (Real.sqrt X) ^ 2 * quarterWeight570 X 1 * (X ^ (4 / 25 : ℝ) * (1 / X) ^ (29 / 25 : ℝ)) /
          (29 / 25) :=
      by ring
    _ = _ := by
      rw [hs, hp]; field_simp [hx.ne']

end PseudoPrime.PrimeTestBounds.MillerRabin
