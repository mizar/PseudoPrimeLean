/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialFixedPointExecution
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring

/-! # Certified normalization scales for the two middle kernels -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An integer Taylor subtotal verifies an upper bound for the normalized
exponential without dividing rational terms inside the certificate. -/
public theorem middle_exp_scale_le {a b S n : ℕ} {k p : ℚ} (hS : 0 < S) (hp : 0 ≤ p)
    (hc : k * (S : ℚ) ≤ p * (Analysis.expFixedPointLowerSumFast a b S n : ℚ)) :
    (k : ℝ) * Real.exp (-((a : ℝ) / b)) ≤ (p : ℝ) := by
  have hs : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have he := Analysis.expFixedPointLowerSum_le_exp a b S n
  rw [← Analysis.expFixedPointLowerSumFast_eq] at he
  have h := Rat.cast_le (K := ℝ).mpr hc
  simp only [Rat.cast_mul, Rat.cast_natCast] at h
  have hh := h.trans (mul_le_mul_of_nonneg_left he (Rat.cast_nonneg.mpr hp))
  rw [show (p : ℝ) * ((S : ℝ) * Real.exp ((a : ℝ) / b)) = (p : ℝ) * Real.exp ((a : ℝ) / b) * S by
      ring] at hh
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr ((mul_le_mul_iff_of_pos_right hs).mp hh)

/-- Clear both positive denominators before checking the normalized Taylor comparison. -/
private theorem middle_scale_cross {a b c d S T : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : a * S * d ≤ c * T * b) : (a / b : ℚ) * S ≤ (c / d : ℚ) * T := by
  have hc := (Nat.cast_le (α := ℚ)).mpr h
  simp only [Nat.cast_mul] at hc
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  exact (div_le_div_iff₀ (Nat.cast_pos.mpr hb) (Nat.cast_pos.mpr hd)).mpr hc

/-- The rational Fourier mass normalization for kernel K141. -/
@[expose]
public def middleK141Norm : ℚ :=
  6755399441055744000000000000000000000000 / 1157999552468559480747792355671594867723563

/-- The rational coefficient multiplying the decaying profile in the K141 residual. -/
@[expose]
public def middleK141Scale : ℚ :=
  (68391147416588715600235206 * 10 ^ 60 +
      330696196985529339557704038061210006641710991698272989699471) /
    (12856377656562217656730421962669 * 10 ^ 60 +
      673382734936151194915510131977498531341552734375000000000000)

/-- K141's rational profile coefficient bounds its normalization times `exp(-a*b)`. -/
public theorem middle_k141_scale_le :
    (middleK141Norm : ℝ) * Real.exp (-(7)) ≤ (middleK141Scale : ℝ) := by
  have h :=
    middle_exp_scale_le (a := 7) (b := 1) (S := 10 ^ 110) (n := 112) (k := middleK141Norm) (p :=
      middleK141Scale) (by decide) (by decide +kernel)
      (by
        have hc :=
          middle_scale_cross (a := 6755399441055744000000000000000000000000) (b :=
            1157999552468559480747792355671594867723563) (c :=
            (68391147416588715600235206 * 10 ^ 60 +
              330696196985529339557704038061210006641710991698272989699471))
            (d :=
            (12856377656562217656730421962669 * 10 ^ 60 +
              673382734936151194915510131977498531341552734375000000000000))
            (S := 10 ^ 110) (T := Analysis.expFixedPointLowerSumFast 7 1 (10 ^ 110) 112) (by decide)
            (by decide) (by decide +kernel)
        simpa only [middleK141Norm, middleK141Scale, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add,
          Nat.cast_pow, Nat.cast_zero] using hc)
  simpa only [Nat.cast_ofNat, Nat.cast_one, div_one] using h

/-- The rational Fourier mass normalization for kernel K156. -/
@[expose]
public def middleK156Norm : ℚ :=
  13160960115218627860845326763 / 1982243918942918689610607040000

/-- The rational coefficient multiplying the decaying profile in the K156 residual. -/
@[expose]
public def middleK156Scale : ℚ :=
  (310543471561848907696595029276642698601476891684550873 * 10 ^ 60 +
      542785150476426609608154727941149473783733096190057985624901) /
    (247780489867864836201325880000000000000000000000000000000000 * 10 ^ 60 + 0)

/-- K156's rational profile coefficient bounds its normalization times `exp(-a*b)`. -/
public theorem middle_k156_scale_le :
    (middleK156Norm : ℝ) * Real.exp (-(343 / 40)) ≤ (middleK156Scale : ℝ) := by
  have h :=
    middle_exp_scale_le (a := 343) (b := 40) (S := 10 ^ 110) (n := 118) (k := middleK156Norm) (p :=
      middleK156Scale) (by decide) (by decide +kernel)
      (by
        have hc :=
          middle_scale_cross (a := 13160960115218627860845326763) (b :=
            1982243918942918689610607040000) (c :=
            (310543471561848907696595029276642698601476891684550873 * 10 ^ 60 +
              542785150476426609608154727941149473783733096190057985624901))
            (d := (247780489867864836201325880000000000000000000000000000000000 * 10 ^ 60 + 0))
            (S := 10 ^ 110) (T := Analysis.expFixedPointLowerSumFast 343 40 (10 ^ 110) 118)
            (by decide) (by decide) (by decide +kernel)
        simpa only [middleK156Norm, middleK156Scale, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add,
          Nat.cast_pow, Nat.cast_zero] using hc)
  simpa only [Nat.cast_ofNat] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
