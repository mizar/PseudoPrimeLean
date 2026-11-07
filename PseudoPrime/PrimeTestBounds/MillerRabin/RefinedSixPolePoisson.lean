/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleZeroConvergence

/-! # Sixth-order Poisson resolvent identity -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For positive pole distance, the weighted combination of the Poisson
resolvent and its first two formal derivatives equals the sixth-order
resolvent. The common denominator is nonzero, so polynomial normalization
proves the identity at every real ordinate. This is the pointwise algebraic
step in the differentiated Poisson zero-mass formula. -/
theorem sixth_pole_poisson_identity {a : ℝ} (ha : 0 < a) (t : ℝ) :
    3 * (a / (a ^ 2 + t ^ 2)) - 3 * a * ((t ^ 2 - a ^ 2) / (a ^ 2 + t ^ 2) ^ 2) +
        a ^ 2 * (2 * a * (a ^ 2 - 3 * t ^ 2) / (a ^ 2 + t ^ 2) ^ 3) =
      8 * a ^ 5 / (a ^ 2 + t ^ 2) ^ 3 := by
  have hd : a ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t))
  have h1 : a / (a ^ 2 + t ^ 2) = (a * (a ^ 2 + t ^ 2) ^ 2) / (a ^ 2 + t ^ 2) ^ 3 := by
    apply (div_eq_div_iff hd (pow_ne_zero 3 hd)).2
    ring
  have h2 :
    (t ^ 2 - a ^ 2) / (a ^ 2 + t ^ 2) ^ 2 =
      ((t ^ 2 - a ^ 2) * (a ^ 2 + t ^ 2)) / (a ^ 2 + t ^ 2) ^ 3 := by
    apply (div_eq_div_iff (pow_ne_zero 2 hd) (pow_ne_zero 3 hd)).2
    ring
  rw [h1, h2]
  simp only [mul_div_assoc]
  ring

/-- The derivative in the pole distance of the Poisson resolvent is the
signed quadratic numerator over the squared denominator. This identifies
the first formal derivative in the sixth-pole identity. -/
theorem hasDerivAt_poisson_distance {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ u / (u ^ 2 + t ^ 2)) ((t ^ 2 - a ^ 2) / (a ^ 2 + t ^ 2) ^ 2) a := by
  have hd : a ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t))
  have h := (hasDerivAt_id a).div (((hasDerivAt_id a).pow 2).add_const (t ^ 2)) hd
  convert h using 1
  · ext u
    rfl
  · simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, one_mul]
    ring

/-- The derivative of the first Poisson-distance derivative is the cubic
resolvent expression appearing in the sixth-pole identity. -/
theorem hasDerivAt_poisson_distance_deriv {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ (t ^ 2 - u ^ 2) / (u ^ 2 + t ^ 2) ^ 2)
      (2 * a * (a ^ 2 - 3 * t ^ 2) / (a ^ 2 + t ^ 2) ^ 3) a := by
  have hd : a ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t))
  have h :=
    (((hasDerivAt_id a).pow 2).const_sub (t ^ 2)).div
      ((((hasDerivAt_id a).pow 2).add_const (t ^ 2)).pow 2) (pow_ne_zero 2 hd)
  convert h using 1
  · ext u
    rfl
  · simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    apply (div_eq_div_iff (pow_ne_zero 3 hd) (pow_ne_zero 2 (pow_ne_zero 2 hd))).2
    ring

end PseudoPrime.PrimeTestBounds.MillerRabin
