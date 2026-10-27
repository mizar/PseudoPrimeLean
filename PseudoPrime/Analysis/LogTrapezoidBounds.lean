/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic

/-! # Telescoping trapezoid bounds for real logarithmic increments -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The trapezoid approximation to log(1+t), minus the exact logarithm.
Its derivative is a nonnegative rational function on t≥0. The error supplies
a telescoping second-order enclosure for the real digamma error series. -/
noncomputable def logTrapezoidError (t : ℝ) : ℝ :=
  ((1 + t) - (1 + t)⁻¹) / 2 - Real.log (1 + t)

/-- The rational remainder allowance minus the trapezoid error.
Its nonnegative derivative on t≥0 bounds the error by a difference of inverse
squares after substituting t=1/z. This yields an exactly telescoping tail. -/
noncomputable def logTrapezoidRemainder (t : ℝ) : ℝ :=
  t ^ 2 / 8 * (1 - (1 + t)⁻¹ ^ 2) - logTrapezoidError t

/-- For t≥0, differentiate the trapezoid error. The derivative is
t²/(2(1+t)²); the positive denominator makes its sign explicit. -/
theorem hasDerivAt_logTrapezoidError {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt logTrapezoidError (t ^ 2 / (2 * (1 + t) ^ 2)) t := by
  have hz : 1 + t ≠ 0 := (add_pos_of_pos_of_nonneg zero_lt_one ht).ne'
  have hd := (hasDerivAt_id t).const_add 1
  have h := ((hd.sub (hd.inv hz)).div_const 2).sub (hd.log hz)
  convert h using 1
  · rfl
  · simp only [id_eq]
    field_simp (discharger :=
      first
      | exact hz
      | norm_num only)
    ring

/-- For t≥0, the rational remainder has derivative
t²(1+t+t²)/(4(1+t)³). Its nonnegative sign proves the lower logarithm bound. -/
theorem hasDerivAt_logTrapezoidRemainder {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt logTrapezoidRemainder (t ^ 2 * (1 + t + t ^ 2) / (4 * (1 + t) ^ 3)) t := by
  have hz : 1 + t ≠ 0 := (add_pos_of_pos_of_nonneg zero_lt_one ht).ne'
  have hi := ((hasDerivAt_id t).const_add 1).inv hz
  have h := (((hasDerivAt_id t).pow 2).div_const 8).mul ((hi.pow 2).const_sub 1)
  convert h.sub (hasDerivAt_logTrapezoidError ht) using 1
  · rfl
  · dsimp only [Pi.pow_apply, Pi.inv_apply, id_eq]
    simp only [inv_eq_one_div]
    field_simp (discharger :=
      first
      | exact hz
      | norm_num only)
    ring_nf
    field_simp (discharger :=
      first
      | exact hz
      | norm_num only)
    ring

/-- The real trapezoid error is nonnegative at every t≥0.
Its rational derivative is nonnegative and the error vanishes at zero.
This gives the upper bound for each logarithmic increment. -/
theorem logTrapezoidError_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ logTrapezoidError t := by
  have hm :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
      (fun u hu ↦ (hasDerivAt_logTrapezoidError hu).continuousAt.continuousWithinAt)
      (fun u hu ↦ (hasDerivAt_logTrapezoidError (interior_subset hu)).hasDerivWithinAt)
      (fun u _ ↦ div_nonneg (sq_nonneg u) (mul_nonneg (by norm_num only) (sq_nonneg _)))
  have h := hm (show (0 : ℝ) ∈ Set.Ici 0 from Set.mem_Ici.mpr (le_refl _)) ht ht
  simpa only [logTrapezoidError, add_zero, inv_one, sub_self, zero_div, Real.log_one] using h

/-- For t≥0, the trapezoid error is at most t²(1-(1+t)⁻²)/8.
The remainder derivative is nonnegative and its value at zero vanishes.
This is the lower logarithm bound needed for a two-sided digamma enclosure. -/
theorem logTrapezoidError_le_remainder {t : ℝ} (ht : 0 ≤ t) :
    logTrapezoidError t ≤ t ^ 2 / 8 * (1 - (1 + t)⁻¹ ^ 2) := by
  have hm :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
      (fun u hu ↦ (hasDerivAt_logTrapezoidRemainder hu).continuousAt.continuousWithinAt)
      (fun u hu ↦ (hasDerivAt_logTrapezoidRemainder (interior_subset hu)).hasDerivWithinAt)
      (fun u hu ↦
        div_nonneg
          (mul_nonneg (sq_nonneg u)
            (add_nonneg (add_nonneg zero_le_one (interior_subset hu)) (sq_nonneg u)))
          (mul_nonneg (by norm_num only)
            (pow_nonneg (add_nonneg zero_le_one (interior_subset hu)) _)))
  have h := hm (show (0 : ℝ) ∈ Set.Ici 0 from Set.mem_Ici.mpr (le_refl _)) ht ht
  simp only [logTrapezoidRemainder, logTrapezoidError, add_zero, inv_one, sub_self, zero_div,
    Real.log_one, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
  change 0 ≤ t ^ 2 / 8 * (1 - (1 + t)⁻¹ ^ 2) - logTrapezoidError t at h
  exact sub_nonneg.mp h

/-- For z>0, the logarithmic increment minus the initial reciprocal lies
between the negative trapezoid endpoint difference and that quantity minus
one eighth of the inverse-square endpoint difference. Both bounds telescope
exactly over integer translates, giving a quadratic digamma tail error. -/
theorem log_increment_trapezoid_bounds {z : ℝ} (hz : 0 < z) :
    -(1 / 2 : ℝ) * (z⁻¹ - (z + 1)⁻¹) - (1 / 8 : ℝ) * (z⁻¹ ^ 2 - (z + 1)⁻¹ ^ 2) ≤
        Real.log (z + 1) - Real.log z - z⁻¹ ∧
      Real.log (z + 1) - Real.log z - z⁻¹ ≤ -(1 / 2 : ℝ) * (z⁻¹ - (z + 1)⁻¹) := by
  have hz1 : z + 1 ≠ 0 := (add_pos hz zero_lt_one).ne'
  have he : 1 + z⁻¹ = (z + 1) / z := by field_simp (discharger := exact hz.ne')
  have ht := logTrapezoidError_nonneg (inv_nonneg.mpr hz.le)
  have hu := logTrapezoidError_le_remainder (inv_nonneg.mpr hz.le)
  have hT : logTrapezoidError z⁻¹ = (z⁻¹ + (z + 1)⁻¹) / 2 - (Real.log (z + 1) - Real.log z) := by
    rw [logTrapezoidError, he, Real.log_div hz1 hz.ne']
    field_simp (discharger :=
      first
      | exact hz.ne'
      | exact hz1
      | norm_num only)
    ring
  have hR : z⁻¹ ^ 2 / 8 * (1 - (1 + z⁻¹)⁻¹ ^ 2) = (1 / 8 : ℝ) * (z⁻¹ ^ 2 - (z + 1)⁻¹ ^ 2) := by
    rw [he]
    field_simp (discharger :=
      first
      | exact hz.ne'
      | exact hz1
      | norm_num only)
  rw [hT] at ht hu
  rw [hR] at hu
  constructor <;> linarith only [ht, hu]

end PseudoPrime.Analysis
